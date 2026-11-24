// Tiny stack VM: a complete interpreter for the tiny stack ISA, written for the
// make.fun "Build a tiny stack virtual machine" bounty. Every trap code, limit and
// wrapping rule of the ISA is honoured, including the edge cases a plain
// interpreter tends to miss (unsigned division, shift masking, output limits).
// Run: MAKEFUN_INPUT_DIR=<in> MAKEFUN_OUTPUT_DIR=<out> node main.ts
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode shape: [immediate bytes, values popped, values pushed].
// A missing entry is an unknown opcode (trap 5).
const SHAPE: Record<number, [number, number, number]> = {
  0x00: [0, 0, 0], 0x01: [1, 0, 1], 0x02: [4, 0, 1], 0x03: [0, 1, 0],
  0x04: [0, 1, 2], 0x05: [0, 2, 2], 0x06: [0, 2, 3], 0x07: [0, 3, 3],
  0x10: [0, 2, 1], 0x11: [0, 2, 1], 0x12: [0, 2, 1], 0x13: [0, 2, 1],
  0x14: [0, 2, 1], 0x15: [0, 2, 1], 0x16: [0, 2, 1], 0x17: [0, 1, 1],
  0x18: [0, 2, 1], 0x19: [0, 2, 1], 0x1a: [0, 2, 1], 0x1b: [0, 1, 1],
  0x1c: [0, 2, 1], 0x1d: [0, 2, 1], 0x1e: [0, 2, 1], 0x20: [0, 2, 1],
  0x21: [0, 2, 1], 0x22: [0, 2, 1], 0x30: [2, 0, 0], 0x31: [2, 1, 0],
  0x32: [2, 1, 0], 0x33: [2, 0, 0], 0x34: [0, 0, 0], 0x40: [0, 1, 1],
  0x41: [0, 2, 0], 0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1],
  0x53: [0, 1, 0],
};

function execute(prog: Uint8Array, inp: Uint8Array): { bytes: number[]; code: number } {
  const stack = new Int32Array(256);
  const calls = new Int32Array(64);
  const mem = new Int32Array(256);
  const bytes: number[] = [];
  let sp = 0, csp = 0, pc = 0, inAt = 0, steps = 0;
  const end = (code: number) => ({ bytes, code });

  for (;;) {
    // The ISA's step order: step limit, pc range, opcode known, immediate fits.
    if (steps >= 1_000_000) return end(10);
    if (pc < 0 || pc >= prog.length) return end(9);
    const op = prog[pc];
    const shape = SHAPE[op];
    if (shape === undefined) return end(5);
    const [imm, pops, pushes] = shape;
    if (pc + imm >= prog.length && imm > 0) return end(9);
    steps += 1;
    // Then the stack needs, before the instruction's own traps or effects.
    if (sp < pops) return end(2);
    if (sp - pops + pushes > 256) return end(3);
    const after = pc + 1 + imm;
    pc = after;

    if (op === 0x00) return end(0); // HALT
    if (op === 0x53) return end(stack[--sp] & 255); // EXIT
    if (op === 0x01) { // PUSH8, sign-extended
      const b = prog[after - 1];
      stack[sp++] = b < 128 ? b : b - 256;
      continue;
    }
    if (op === 0x02) { // PUSH32, little-endian
      stack[sp++] = prog[after - 4] | (prog[after - 3] << 8) | (prog[after - 2] << 16) | (prog[after - 1] << 24);
      continue;
    }
    if (op === 0x52) { // IN
      stack[sp++] = inAt < inp.length ? inp[inAt++] : -1;
      continue;
    }
    if (op === 0x30 || op === 0x31 || op === 0x32) { // JMP / JZ / JNZ
      const raw = prog[after - 2] | (prog[after - 1] << 8);
      const rel = raw < 32768 ? raw : raw - 65536;
      let go = op === 0x30;
      if (op === 0x31) go = stack[--sp] === 0;
      if (op === 0x32) go = stack[--sp] !== 0;
      if (go) pc = after + rel;
      continue;
    }
    if (op === 0x33) { // CALL to an absolute address
      if (csp >= 64) return end(7);
      calls[csp++] = after;
      pc = prog[after - 2] | (prog[after - 1] << 8);
      continue;
    }
    if (op === 0x34) { // RET
      if (csp === 0) return end(8);
      pc = calls[--csp];
      continue;
    }
    if (op === 0x40 || op === 0x41) { // LOAD / STORE, address on top
      const addr = stack[sp - 1];
      if (addr < 0 || addr > 255) return end(6);
      if (op === 0x40) {
        stack[sp - 1] = mem[addr];
      } else {
        mem[addr] = stack[sp - 2];
        sp -= 2;
      }
      continue;
    }
    if (op === 0x50) { // PRINT in decimal
      const text = String(stack[--sp]);
      if (bytes.length + text.length > 65_536) return end(11);
      for (let i = 0; i < text.length; i++) bytes.push(text.charCodeAt(i));
      continue;
    }
    if (op === 0x51) { // PUTC, one byte
      if (bytes.length + 1 > 65_536) return end(11);
      bytes.push(stack[--sp] & 255);
      continue;
    }
    if (op === 0x03) { sp -= 1; continue; } // POP
    if (op === 0x04) { stack[sp] = stack[sp - 1]; sp += 1; continue; } // DUP
    if (op === 0x05) { // SWAP
      const t = stack[sp - 1]; stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = t;
      continue;
    }
    if (op === 0x06) { stack[sp] = stack[sp - 2]; sp += 1; continue; } // OVER
    if (op === 0x07) { // ROT: (a b c) becomes (b c a)
      const a = stack[sp - 3];
      stack[sp - 3] = stack[sp - 2]; stack[sp - 2] = stack[sp - 1]; stack[sp - 1] = a;
      continue;
    }
    if (op === 0x17) { stack[sp - 1] = (-stack[sp - 1]) | 0; continue; } // NEG
    if (op === 0x1b) { stack[sp - 1] = ~stack[sp - 1]; continue; } // NOT

    // The remaining opcodes are the two-input arithmetic and comparison set.
    const b = stack[sp - 1];
    const a = stack[sp - 2];
    let r = 0;
    if (op === 0x10) r = (a + b) | 0;
    else if (op === 0x11) r = (a - b) | 0;
    else if (op === 0x12) r = Math.imul(a, b);
    else if (op === 0x13) { if (b === 0) return end(4); r = Math.trunc(a / b) | 0; }
    else if (op === 0x14) { if (b === 0) return end(4); r = (a % b) | 0; }
    else if (op === 0x15) { if (b === 0) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
    else if (op === 0x16) { if (b === 0) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
    else if (op === 0x18) r = a & b;
    else if (op === 0x19) r = a | b;
    else if (op === 0x1a) r = a ^ b;
    else if (op === 0x1c) r = a << (b & 31);
    else if (op === 0x1d) r = a >> (b & 31);
    else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
    else if (op === 0x20) r = a === b ? 1 : 0;
    else if (op === 0x21) r = a < b ? 1 : 0;
    else if (op === 0x22) r = (a >>> 0) < (b >>> 0) ? 1 : 0;
    sp -= 1;
    stack[sp - 1] = r;
  }
}

const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(inputDir).sort()) {
  const prog = new Uint8Array(readFileSync(join(inputDir, id, 'program.bin')));
  const inp = new Uint8Array(readFileSync(join(inputDir, id, 'input.bin')));
  const result = execute(prog, inp);
  mkdirSync(join(outputDir, id), { recursive: true });
  writeFileSync(join(outputDir, id, 'stdout.bin'), Uint8Array.from(result.bytes));
  writeFileSync(join(outputDir, id, 'exit.txt'), `${result.code}\n`);
}
