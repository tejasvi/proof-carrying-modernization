// @numbers
// Building strings in loops; number formatting inside templates; word counting.
const words = "the quick brown fox jumps over the lazy dog the end".split(" ");
const freq = new Map<string, number>();
for (const w of words) freq.set(w, (freq.get(w) ?? 0) + 1);
const top = [...freq.entries()].sort((a, b) => (b[1] - a[1] !== 0 ? b[1] - a[1] : a[0] < b[0] ? -1 : 1)).slice(0, 3);
console.log(top.map(([w, n]) => `${w}:${n}`).join(" "));
let line = "";
for (let i = 1; i <= 15; i++) {
  line += i % 15 === 0 ? "FizzBuzz" : i % 3 === 0 ? "Fizz" : i % 5 === 0 ? "Buzz" : `${i}`;
  if (i < 15) line += ",";
}
console.log(line);
function pad(n: number, width: number): string { return `${n}`.padStart(width, " "); }
for (const n of [1, 22, 333]) console.log(`|${pad(n, 5)}|${(n / 7).toFixed(3)}|`);
const csv = "name,age\nann,31\nbob,27";
const rows = csv.split("\n").slice(1).map((r) => r.split(","));
console.log(rows.map(([n, a]) => `${n} is ${Number(a) + 1} next year`).join("; "));
