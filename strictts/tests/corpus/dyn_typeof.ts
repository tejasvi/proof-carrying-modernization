// Values of type unknown carry their runtime type: typeof, Array.isArray, truthiness, String(x)
// and template holes follow JavaScript for every runtime type.
class Box { constructor(public v: number) {} }
function f(): number { return 1; }
const samples: unknown[] = [0, -0, 1.5, NaN, -Infinity, "", "s", true, false, undefined, null, 10n, 0n,
  [1, "a", [2, null, undefined]], [], { a: 1 }, new Map<string, number>(), new Set<number>(), new Box(3),
  new Error("boom"), new TypeError("bad"), new Error("")];
for (const x of samples) {
  console.log(`${typeof x} ${Array.isArray(x)} ${x ? "T" : "F"} ${!x} [${String(x)}] [${x}]`);
}
const fn: unknown = f;
console.log(`${typeof fn} ${Array.isArray(fn)} ${fn ? "T" : "F"}`);
const kinds = samples.map((x) => typeof x);
console.log(kinds.join(","));
console.log(samples.map((x) => `${Number(x)}`).join(" "));
const numish: unknown[] = ["42", " 7 ", "", "0x10", "1e3", "abc", [], [5], [1, 2], "-0"];
console.log(numish.map((x) => `${Number(x)}`).join(" "));
