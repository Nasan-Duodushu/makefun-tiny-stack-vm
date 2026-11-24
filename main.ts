// Tiny stack VM for the make.fun bounty: a complete interpreter for the tiny
// stack ISA. Opcode shapes are derived from the opcode ranges instead of a
// table: imm is 1 for PUSH8, 4 for PUSH32, 2 for the jump/call group, and the
// pop/push counts follow from which range an opcode sits in.
// Run: MAKEFUN_INPUT_DIR=<in> MAKEFUN_OUTPUT_DIR=<out> node main.ts
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

function run(p: Uint8Array, inp: Uint8Array): { b: Uint8Array; c: number } {
  const k = new Int32Array(256), cs = new Int32Array(64), m = new Int32Array(256);
  const o = new Uint8Array(65536);
  let n = 0, sp = 0, cp = 0, pc = 0, ia = 0, st = 0;
  const end = (c: number) => ({ b: o.slice(0, n), c });
  for (;;) {
    if (st >= 1000000) return end(10);
    if (pc < 0 || pc >= p.length) return end(9);
    const op = p[pc]!;
    const known = op <= 7 || (op >= 16 && op <= 34 && op !== 31) || (op >= 48 && op <= 52) || op === 64 || op === 65 || (op >= 80 && op <= 83);
    if (!known) return end(5);
    const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 48 && op <= 51 ? 2 : 0;
    if (imm > 0 && pc + imm >= p.length) return end(9);
    st += 1;
    const pops = op === 0 || op === 1 || op === 2 || op === 48 || op === 51 || op === 52 || op === 82 ? 0
      : op === 7 ? 3
      : op === 3 || op === 4 || op === 23 || op === 27 || op === 49 || op === 50 || op === 64 || op === 80 || op === 81 || op === 83 ? 1 : 2;
    const push = op === 4 || op === 5 ? 2 : op === 6 || op === 7 ? 3
      : op === 1 || op === 2 || op === 64 || op === 82 || (op >= 16 && op <= 34 && op !== 31) ? 1 : 0;
    if (sp < pops) return end(2);
    if (sp - pops + push > 256) return end(3);
    const a2 = pc + 1 + imm;
    pc = a2;
    if (op === 0) return end(0);
    if (op === 83) return end(k[--sp]! & 255);
    if (op === 1) { const b = p[a2 - 1]!; k[sp++] = b < 128 ? b : b - 256; continue; }
    if (op === 2) { k[sp++] = p[a2 - 4]! | (p[a2 - 3]! << 8) | (p[a2 - 2]! << 16) | (p[a2 - 1]! << 24); continue; }
    if (op === 82) { k[sp++] = ia < inp.length ? inp[ia++]! : -1; continue; }
    if (op >= 48 && op <= 50) {
      const raw = p[a2 - 2]! | (p[a2 - 1]! << 8), rel = raw < 32768 ? raw : raw - 65536;
      let go = op === 48;
      if (op === 49) go = k[--sp] === 0;
      if (op === 50) go = k[--sp] !== 0;
      if (go) pc = a2 + rel;
      continue;
    }
    if (op === 51) { if (cp >= 64) return end(7); cs[cp++] = a2; pc = p[a2 - 2]! | (p[a2 - 1]! << 8); continue; }
    if (op === 52) { if (cp === 0) return end(8); pc = cs[--cp]!; continue; }
    if (op === 64 || op === 65) {
      const ad = k[sp - 1]!;
      if (ad < 0 || ad > 255) return end(6);
      if (op === 64) k[sp - 1] = m[ad]!;
      else { m[ad] = k[sp - 2]!; sp -= 2; }
      continue;
    }
    if (op === 80) {
      const t = String(k[--sp]!);
      if (n + t.length > 65536) return end(11);
      for (let i = 0; i < t.length; i++) o[n++] = t.charCodeAt(i);
      continue;
    }
    if (op === 81) { if (n + 1 > 65536) return end(11); o[n++] = k[--sp]! & 255; continue; }
    if (op === 3) { sp -= 1; continue; }
    if (op === 4) { k[sp] = k[sp - 1]!; sp += 1; continue; }
    if (op === 5) { const t = k[sp - 1]!; k[sp - 1] = k[sp - 2]!; k[sp - 2] = t; continue; }
    if (op === 6) { k[sp] = k[sp - 2]!; sp += 1; continue; }
    if (op === 7) { const a = k[sp - 3]!; k[sp - 3] = k[sp - 2]!; k[sp - 2] = k[sp - 1]!; k[sp - 1] = a; continue; }
    if (op === 23) { k[sp - 1] = (-k[sp - 1]!) | 0; continue; }
    if (op === 27) { k[sp - 1] = ~k[sp - 1]!; continue; }
    const b = k[sp - 1]!, a = k[sp - 2]!;
    let r = 0;
    if (op === 16) r = (a + b) | 0;
    else if (op === 17) r = (a - b) | 0;
    else if (op === 18) r = Math.imul(a, b);
    else if (op === 19) { if (b === 0) return end(4); r = Math.trunc(a / b) | 0; }
    else if (op === 20) { if (b === 0) return end(4); r = (a % b) | 0; }
    else if (op === 21) { if (b === 0) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
    else if (op === 22) { if (b === 0) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
    else if (op === 24) r = a & b;
    else if (op === 25) r = a | b;
    else if (op === 26) r = a ^ b;
    else if (op === 28) r = a << (b & 31);
    else if (op === 29) r = a >> (b & 31);
    else if (op === 30) r = (a >>> (b & 31)) | 0;
    else if (op === 32) r = a === b ? 1 : 0;
    else if (op === 33) r = a < b ? 1 : 0;
    else if (op === 34) r = (a >>> 0) < (b >>> 0) ? 1 : 0;
    sp -= 1;
    k[sp - 1] = r;
  }
}

const idir = process.env.MAKEFUN_INPUT_DIR ?? '/input', odir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(idir).sort()) {
  const r = run(new Uint8Array(readFileSync(join(idir, id, 'program.bin'))), new Uint8Array(readFileSync(join(idir, id, 'input.bin'))));
  mkdirSync(join(odir, id), { recursive: true });
  writeFileSync(join(odir, id, 'stdout.bin'), r.b);
  writeFileSync(join(odir, id, 'exit.txt'), `${r.c}\n`);
}
