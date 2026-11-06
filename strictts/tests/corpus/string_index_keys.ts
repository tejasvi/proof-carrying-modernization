// `s[i]` on a string reads a code unit only at an array index (an integer from 0; -0 is 0): a
// negative, fractional, NaN or infinite index names a property strings do not have, so the read
// is undefined, unlike `s.at(i)` and `s.charAt(i)`, which truncate the index (and `at` counts
// negative ones from the end).
const s = "abc";
const idx = [0, -0, 2, 3, -1, 1.5, NaN, Infinity, -Infinity, 2 ** 32];
console.log(idx.map((i) => s[i] ?? "-").join(" "));
console.log(idx.map((i) => s.at(i) ?? "-").join(" "));
console.log(idx.map((i) => s.charAt(i) || "-").join(" "));
function around(t: string, k: number): string { return `${t[k - 1] ?? "<"}${t[k + 1] ?? ">"}`; }
console.log(`${around("xy", 0)} ${around("xy", 1)} ${around("xy", NaN)} ${around("", 0)}`);
