// Left-to-right evaluation order with side effects in operands, arguments and assignments.
const trace: string[] = [];
function v(name: string, x: bigint): bigint { trace.push(name); return x; }
function s(name: string): string { trace.push(name); return name; }
const sum = v("a", 1n) + v("b", 2n) * v("c", 3n);
console.log(`${sum} ${trace.join("")}`);
trace.length = 0;
function three(x: bigint, y: string, z: bigint): string { return `${x}${y}${z}`; }
console.log(three(v("1", 1n), s("2"), v("3", 3n)) + " " + trace.join(""));
trace.length = 0;
const arr: bigint[] = [10n, 20n, 30n];
let i = 0n;
const idx = (): number => { trace.push(`i${i}`); i++; return i === 1n ? 0 : 2; };
arr[idx()] = v("rhs", 99n);
console.log(`${arr.join(",")} ${trace.join(" ")}`);
trace.length = 0;
const obj = { a: v("A", 1n), b: s("B"), c: v("C", 3n) };
console.log(`${obj.a}${obj.b}${obj.c} ${trace.join("")}`);
trace.length = 0;
const m = new Map<string, bigint>();
m.set(s("key"), v("val", 5n));
console.log(trace.join(","));
