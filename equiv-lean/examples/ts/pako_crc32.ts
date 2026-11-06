// TS <-> Rust demo (equiv-lean, Demo/XLang/Crc32): pako 1.0.11's lib/zlib/crc32.js as TypeScript.
// Altered from the original: parameter and return types, `let`/`const` for `var`, the table built
// with `push` instead of `table[n] = c`, the parity test written as `(c & 1) !== 0`.  The Rust side
// is crc32fast 1.4.2's baseline implementation, examples/rust/crc32fast_base.
//
// Original notice (pako, lib/zlib/crc32.js; MIT AND Zlib):
// (C) 1995-2013 Jean-loup Gailly and Mark Adler
// (C) 2014-2017 Vitaly Puzrin and Andrey Tupitsin
//
// This software is provided 'as-is', without any express or implied
// warranty. In no event will the authors be held liable for any damages
// arising from the use of this software.
//
// Permission is granted to anyone to use this software for any purpose,
// including commercial applications, and to alter it and redistribute it
// freely, subject to the following restrictions:
//
// 1. The origin of this software must not be misrepresented; you must not
//   claim that you wrote the original software. If you use this software
//   in a product, an acknowledgment in the product documentation would be
//   appreciated but is not required.
// 2. Altered source versions must be plainly marked as such, and must not be
//   misrepresented as being the original software.
// 3. This notice may not be removed or altered from any source distribution.

// Use ordinary array, since untyped makes no boost here
function makeTable(): number[] {
  let c = 0;
  const table: number[] = [];

  for (let n = 0; n < 256; n++) {
    c = n;
    for (let k = 0; k < 8; k++) {
      c = ((c & 1) !== 0 ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1));
    }
    table.push(c);
  }

  return table;
}

// Create table on load. Just 255 signed longs. Not a problem.
const crcTable: number[] = makeTable();

export function crc32(crc: number, buf: Uint8Array, len: number, pos: number): number {
  const t = crcTable;
  const end = pos + len;

  crc ^= -1;

  for (let i = pos; i < end; i++) {
    crc = (crc >>> 8) ^ t[(crc ^ buf[i]) & 0xFF];
  }

  return (crc ^ (-1)); // >>> 0;
}

console.log(String(crc32(0, new Uint8Array([104, 101, 108, 108, 111]), 5, 0) >>> 0));
