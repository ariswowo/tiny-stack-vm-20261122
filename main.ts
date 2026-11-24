// Tiny stack VM (ISA v1): runs each /input/<id>/program.bin and writes
// /output/<id>/stdout.bin + exit.txt. 32-bit wrapping ints, traps 2-11,
// 1M steps and 64K output max per program.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const MAX_STEPS = 1000000;
const MAX_OUT = 65536;
const DIG = new Int8Array(10);

// Decimal ASCII of v into out at at; new position, or -1 if past MAX_OUT.
function putInt(out, at, v) {
  let u = v;
  let neg = 0;
  if (v < 0) {
    neg = 1;
    u = -v;
  }
  let k = 0;
  do {
    DIG[k++] = u % 10;
    u = Math.trunc(u / 10);
  } while (u > 0);
  const len = k + neg;
  if (at + len > MAX_OUT) return -1;
  let p = at;
  if (neg) out[p++] = 45;
  while (k > 0) out[p++] = 48 + DIG[--k];
  return p;
}

function run(prog, inp) {
  const n = prog.length;
  const st = new Int32Array(257);
  let sp = 0;
  const cs = new Int32Array(64);
  let csp = 0;
  const mem = new Int32Array(256);
  const out = new Uint8Array(MAX_OUT);
  let olen = 0;
  let pc = 0;
  let ip = 0;
  let steps = 0;
  const done = (code) => ({ code, out: out.subarray(0, olen) });

  for (;;) {
    if (steps === MAX_STEPS) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = prog[pc++];
    switch (op) {
      case 0x00:
        return done(0);
      case 0x01: {
        if (pc >= n) return done(9);
        if (sp === 256) return done(3);
        st[sp++] = (prog[pc++] << 24) >> 24;
        break;
      }
      case 0x02: {
        if (pc + 4 > n) return done(9);
        if (sp === 256) return done(3);
        st[sp++] = prog[pc] | (prog[pc + 1] << 8) | (prog[pc + 2] << 16) | (prog[pc + 3] << 24);
        pc += 4;
        break;
      }
      case 0x03:
        if (sp === 0) return done(2);
        sp--;
        break;
      case 0x04: {
        if (sp === 0) return done(2);
        if (sp === 256) return done(3);
        st[sp] = st[sp - 1];
        sp++;
        break;
      }
      case 0x05: {
        if (sp < 2) return done(2);
        const t = st[sp - 1];
        st[sp - 1] = st[sp - 2];
        st[sp - 2] = t;
        break;
      }
      case 0x06: {
        if (sp < 2) return done(2);
        if (sp === 256) return done(3);
        st[sp] = st[sp - 2];
        sp++;
        break;
      }
      case 0x07: {
        if (sp < 3) return done(2);
        const t = st[sp - 3];
        st[sp - 3] = st[sp - 2];
        st[sp - 2] = st[sp - 1];
        st[sp - 1] = t;
        break;
      }
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14:
      case 0x15: case 0x16: case 0x18: case 0x19: case 0x1a:
      case 0x1c: case 0x1d: case 0x1e: case 0x20: case 0x21:
      case 0x22: {
        if (sp < 2) return done(2);
        const b = st[--sp];
        const a = st[--sp];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return done(4);
          r = (a === -2147483648 && b === -1) ? -2147483648 : Math.trunc(a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return done(4);
          r = (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return done(4);
          r = Math.trunc((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        st[sp++] = r;
        break;
      }
      case 0x17:
        if (sp === 0) return done(2);
        st[sp - 1] = (-st[sp - 1]) | 0;
        break;
      case 0x1b:
        if (sp === 0) return done(2);
        st[sp - 1] = ~st[sp - 1];
        break;
      case 0x30: case 0x31: case 0x32: {
        if (pc + 2 > n) return done(9);
        const rel = ((prog[pc] | (prog[pc + 1] << 8)) << 16) >> 16;
        pc += 2;
        let take = op === 0x30;
        if (op !== 0x30) {
          if (sp === 0) return done(2);
          const v = st[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc += rel;
        break;
      }
      case 0x33: {
        if (pc + 2 > n) return done(9);
        if (csp === 64) return done(7);
        const target = prog[pc] | (prog[pc + 1] << 8);
        cs[csp++] = pc + 2;
        pc = target;
        break;
      }
      case 0x34:
        if (csp === 0) return done(8);
        pc = cs[--csp];
        break;
      case 0x40: {
        if (sp === 0) return done(2);
        const addr = st[--sp];
        if (addr < 0 || addr > 255) return done(6);
        st[sp++] = mem[addr];
        break;
      }
      case 0x41: {
        if (sp < 2) return done(2);
        const addr = st[--sp];
        const v = st[--sp];
        if (addr < 0 || addr > 255) return done(6);
        mem[addr] = v;
        break;
      }
      case 0x50: {
        if (sp === 0) return done(2);
        const v = st[--sp];
        const end = putInt(out, olen, v);
        if (end < 0) return done(11);
        olen = end;
        break;
      }
      case 0x51: {
        if (sp === 0) return done(2);
        if (olen >= MAX_OUT) return done(11);
        out[olen++] = st[--sp] & 255;
        break;
      }
      case 0x52:
        if (sp === 256) return done(3);
        st[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: {
        if (sp === 0) return done(2);
        return done(st[--sp] & 255);
      }
      default:
        return done(5);
    }
    steps++;
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin')))
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), r.code + '\n');
}
