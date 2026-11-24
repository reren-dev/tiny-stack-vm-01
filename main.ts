// Tiny stack VM for make.fun's tiny stack ISA: runs every /input/<id>/program.bin
// on /input/<id>/input.bin, writes /output/<id>/stdout.bin and /output/<id>/exit.txt.
// 32-bit wrapping ints, 256-value stack, 64-deep call stack, 256 words of memory,
// 1,000,000-step and 65,536-byte limits, ten traps with their own exit codes.
import { chmodSync, mkdirSync, readdirSync, readFileSync, renameSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input', O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const E = new TextEncoder();
// Opcode table: (immediateBytes << 4) | (pops << 2) | pushes; 255 = unknown opcode.
const T = new Uint8Array(256).fill(255);
for (let o = 0x10; o <= 0x22; o++) T[o] = 9; // binary ops: 0 imm, pop 2, push 1
T[0x17] = 5; T[0x1b] = 5; // NEG, NOT: pop 1, push 1
T[0x00] = 0; T[0x01] = 0x11; T[0x02] = 0x41; T[0x03] = 4; T[0x04] = 6; T[0x05] = 0x0a;
T[0x06] = 0x0b; T[0x07] = 0x0f; T[0x30] = 0x20; T[0x31] = 0x24; T[0x32] = 0x24;
T[0x33] = 0x20; T[0x34] = 0; T[0x40] = 5; T[0x41] = 8; T[0x50] = 4; T[0x51] = 4;
T[0x52] = 1; T[0x53] = 4;
const put = (d, n, v) => { // atomic write, fixed temp name, mode 0644
  const p = join(d, n), t = p + '.tmp';
  writeFileSync(t, v); renameSync(t, p); chmodSync(p, 0o644);
};
for (const id of readdirSync(I).sort()) {
  const P = readFileSync(join(I, id, 'program.bin')), U = readFileSync(join(I, id, 'input.bin'));
  const n = P.length, S = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const o = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0, ex = 0;
  run: for (;;) {
    if (st === 1000000) { ex = 10; break; }
    if (pc < 0 || pc >= n) { ex = 9; break; }
    const b = P[pc], t = T[b];
    if (t === 255) { ex = 5; break; }
    const im = t >> 4;
    if (pc + im >= n) { ex = 9; break; }
    st++;
    const nx = pc + 1 + im, pops = (t >> 2) & 3, pu = t & 3;
    if (sp < pops) { ex = 2; break; }
    if (sp - pops + pu > 256) { ex = 3; break; }
    pc = nx;
    switch (b) {
      case 0x00: ex = 0; break run;
      case 0x01: S[sp++] = (P[nx - 1] << 24) >> 24; break;
      case 0x02: S[sp++] = P[nx - 4] | (P[nx - 3] << 8) | (P[nx - 2] << 16) | (P[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: S[sp] = S[sp - 1]; sp++; break;
      case 0x05: { const v = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = v; break; }
      case 0x06: S[sp] = S[sp - 2]; sp++; break;
      case 0x07: { const v = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = v; break; }
      case 0x17: S[sp - 1] = -S[sp - 1] | 0; break;
      case 0x1b: S[sp - 1] = ~S[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const y = S[sp - 1], x = S[sp - 2];
        let r;
        if (b === 0x10) r = (x + y) | 0;
        else if (b === 0x11) r = (x - y) | 0;
        else if (b === 0x12) r = Math.imul(x, y);
        else if (b === 0x13) {
          if (y === 0) { ex = 4; break run; }
          r = x === -2147483648 && y === -1 ? x : (x / y) | 0;
        } else if (b === 0x14) {
          if (y === 0) { ex = 4; break run; }
          r = y === -1 ? 0 : (x % y) | 0;
        } else if (b === 0x15) {
          if (y === 0) { ex = 4; break run; }
          r = Math.floor((x >>> 0) / (y >>> 0)) | 0;
        } else if (b === 0x16) {
          if (y === 0) { ex = 4; break run; }
          r = ((x >>> 0) % (y >>> 0)) | 0;
        } else if (b === 0x18) r = x & y;
        else if (b === 0x19) r = x | y;
        else if (b === 0x1a) r = x ^ y;
        else if (b === 0x1c) r = x << (y & 31);
        else if (b === 0x1d) r = x >> (y & 31);
        else if (b === 0x1e) r = (x >>> (y & 31)) | 0;
        else if (b === 0x20) r = x === y ? 1 : 0;
        else if (b === 0x21) r = x < y ? 1 : 0;
        else r = (x >>> 0) < (y >>> 0) ? 1 : 0;
        sp -= 2;
        S[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((P[nx - 2] | (P[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (b !== 0x30) { const v = S[--sp]; take = b === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) { ex = 7; break run; }
        C[cp++] = nx;
        pc = P[nx - 2] | (P[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) { ex = 8; break run; }
        pc = C[--cp];
        break;
      case 0x40: {
        const a = S[sp - 1];
        if (a < 0 || a >= 256) { ex = 6; break run; }
        S[sp - 1] = M[a];
        break;
      }
      case 0x41: {
        const a = S[sp - 1], v = S[sp - 2];
        if (a < 0 || a >= 256) { ex = 6; break run; }
        sp -= 2;
        M[a] = v;
        break;
      }
      case 0x50: {
        const w = E.encode(String(S[sp - 1]));
        if (ol + w.length > 65536) { ex = 11; break run; }
        sp--;
        o.set(w, ol);
        ol += w.length;
        break;
      }
      case 0x51:
        if (ol + 1 > 65536) { ex = 11; break run; }
        o[ol++] = S[--sp] & 255;
        break;
      case 0x52: S[sp++] = ip < U.length ? U[ip++] : -1; break;
      case 0x53: ex = S[--sp] & 255; break run;
    }
  }
  const d = join(O, id);
  mkdirSync(d, { recursive: true });
  put(d, 'stdout.bin', o.subarray(0, ol));
  put(d, 'exit.txt', String(ex) + '\n');
}
