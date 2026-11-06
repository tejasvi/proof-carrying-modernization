// Sorting: default string sort and comparators (stable).
const names = ["delta", "alpha", "Charlie", "bravo"];
names.sort();
console.log(names.join(" "));
const pairs: [string, bigint][] = [["b", 2n], ["a", 2n], ["c", 1n], ["d", 3n]];
pairs.sort((x, y) => (x[1] < y[1] ? -1 : x[1] > y[1] ? 1 : 0));
console.log(pairs.map(([k, v]) => `${k}${v}`).join(" "));
const big = [10n, 9n, 100n, 1n];
big.sort((a, b) => (a < b ? 1 : a > b ? -1 : 0));
console.log(big.join(" "));
const sorted = [...names].sort((a, b) => (a < b ? 1 : -1));
console.log(`${sorted.join(" ")} | original ${names.join(" ")}`);
