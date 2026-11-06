// Reads past the end of an array in a loop condition are undefined, which is falsy, as in
// JavaScript: `while (a[i])` over elements that are all truthy stops past the end, and a
// `for (…; !flags[k]; …)` loop keeps going past the end until something else stops it.
const pos = [3, 1, 2];
let i = 0;
while (pos[i]) i++;
const words = ["a", "b"];
let w = 0;
while (words[w] && w < 10) w++;
const flags: boolean[] = [false, false];
let k = 0;
for (; !flags[k]; k++) { if (k >= 4) break; }
const seen: boolean[] = [true];
let m = 0;
for (let j = 0; !seen[j] || j === 0; j++) { m = j; if (j >= 3) break; }
console.log(`${i} ${w} ${k} ${m} ${pos[i] === undefined} ${!flags[k]}`);
