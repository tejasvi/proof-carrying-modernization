// Array.prototype.concat: array arguments are spread, other arguments appended; empty array
// literals take the receiver's element type.
export function f(xs: number[]): number[] { return xs.concat([]); }
const a = [1, 2];
console.log(`${f(a).join(",")} ${f([]).length}`);
console.log(a.concat(3, [4, 5], [], 6).join(","));
const ys: readonly number[] = [7];
console.log(a.concat(ys, [8] as const).join(","));
const words = ["x"].concat([], ["y"], "z");
console.log(`${words.join("|")} ${words.length}`);
const nested: number[][] = [[1], [2, 3]];
const more = nested.concat([[4]], []);
console.log(`${more.map((r) => r.join("+")).join(" ")} ${more.length}`);
console.log(a.join(","));
