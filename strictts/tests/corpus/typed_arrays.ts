// @numbers
// Typed arrays: wrap-around on store, fill, slice, element types.
const u8 = new Uint8Array(4);
u8[0] = 255; u8[1] = 256; u8[2] = -1; u8[3] = 3.9;
console.log(`${u8[0]} ${u8[1]} ${u8[2]} ${u8[3]} len=${u8.length}`);
const i32 = new Int32Array([2147483647, 1, -2]);
i32[1] = i32[0] + 1;
console.log(`${i32[0]} ${i32[1]} ${i32[2]}`);
const f32 = new Float32Array(2);
f32[0] = 0.1;
console.log(`${f32[0]} ${f32[0] === 0.1}`);
const big = new BigInt64Array(2);
big[0] = 2n ** 63n;
big[1] = -1n;
console.log(`${big[0]} ${big[1]}`);
const filled = new Int8Array(3).fill(-129);
console.log(`${filled[0]} ${filled.slice(1).length}`);
