// @reject no-for-in
const o = { a: 1n, b: 2n };
for (const k in o) console.log(k);
