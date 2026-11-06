// Per-iteration bindings: closures created in loops see their own iteration's value.
const fns: (() => string)[] = [];
for (let i = 0n; i < 3n; i++) {
  fns.push(() => `for-let ${i}`);
}
for (const s of ["x", "y"]) {
  fns.push(() => `for-of ${s}`);
}
let k = 0n;
while (k < 2n) {
  const kk = k;
  let m = kk * 10n;
  fns.push(() => `while ${kk} ${m}`);
  m += 1n;
  k++;
}
for (const f of fns) console.log(f());
