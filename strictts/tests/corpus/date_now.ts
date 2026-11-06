// @extern
// Date.now() is the world's `now` oracle; the Lean run replays the Node run's values.
const t0 = Date.now();
let spins = 0;
while (Date.now() < t0 + 2) spins++;
const t1 = Date.now();
console.log(`${t1 - t0 >= 2} ${Number.isInteger(t0)} ${spins > 0}`);
function since(start: number): string { const d = Date.now() - start; return d >= 0 ? "ok" : "clock went back"; }
console.log(since(t0));
