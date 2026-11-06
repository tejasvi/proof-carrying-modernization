// while / do-while / for with break and continue (bigint counters).
let total = 0n;
let i = 0n;
while (true) {
  i++;
  if (i > 10n) break;
  if (i % 2n === 0n) continue;
  total += i;
}
console.log(`odd sum ${total}`);
let j = 5n;
do {
  console.log(`do ${j}`);
  j -= 2n;
} while (j > 0n);
do { console.log("once"); } while (false);
for (let k = 0n; k < 6n; k++) {
  if (k === 1n) continue;
  if (k === 4n) break;
  console.log(`for ${k}`);
}
let s = "";
for (let a = 3n, b = 0n; a > b; a--, b++) s += `(${a},${b})`;
console.log(s);
for (;;) { console.log("infinite loop body runs once"); break; }
