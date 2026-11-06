// Labelled break/continue across nested loops (and a switch inside a loop).
const rows: bigint[] = [1n, 2n, 3n, 4n];
outer: for (const r of rows) {
  for (const c of rows) {
    if (c > r) continue outer;
    if (r * c > 6n) break outer;
    console.log(`${r}x${c}`);
  }
}
let n = 0n;
loop: while (n < 10n) {
  n++;
  switch (n % 3n) {
    case 0n: continue loop;
    case 1n:
      if (n > 6n) break loop;
      break;
    default:
      console.log(`n=${n} default`);
  }
  console.log(`after switch ${n}`);
}
console.log(`end n=${n}`);
