// Boolean as a callback (truthiness of the first argument), filter with type-guard callbacks
// (explicit and inferred: the kept elements are narrowed), Number of optional values and unions,
// and push with spread arguments (all arguments evaluated first, a spread as a snapshot).
const mixed: (string | undefined)[] = ["a", undefined, "", "b"];
console.log(`${mixed.filter(Boolean).length} ${[0, 1, NaN, 2].map(Boolean).join(",")}`);
const defined = mixed.filter((x): x is string => x !== undefined);
console.log(`${defined.length} ${defined.map((s) => s.toUpperCase()).join("|")}`);
const inferred = mixed.filter((x) => x !== undefined);
console.log(inferred.join("+"));
type Shape = { kind: "c"; r: number } | { kind: "s"; side: number };
const shapes: Shape[] = [{ kind: "c", r: 1 }, { kind: "s", side: 2 }, { kind: "c", r: 3 }];
const circles = shapes.filter((s): s is { kind: "c"; r: number } => s.kind === "c");
console.log(circles.map((c) => c.r).join(","));
const maybe: (number | string | undefined)[] = [4, "5", undefined, " 6 ", "x"];
console.log(maybe.map((v) => Number(v)).join(" "));
const acc: number[] = [1];
const more = [2, 3];
const n = acc.push(0, ...more, ...acc, 9);
console.log(`${n} ${acc.join(",")}`);
const nums = [3, -1, 7];
const empty: number[] = [];
console.log(`${Math.max(...nums)} ${Math.min(...nums)} ${Math.max(...empty)} ${Math.min(...empty)} ${Math.max(10, ...nums, 2)} ${Math.min(...nums, -5)} ${Math.max(...[1, NaN, 2])} ${1 / Math.max(...[-0, 0])} ${1 / Math.min(...[0, -0])}`);
