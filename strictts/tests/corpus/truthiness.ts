// @numbers
// JavaScript truthiness of strings, numbers, bigints, optionals and objects (desugared into
// explicit tests by the translator), in conditions, `!`, `&&`, `||` and filters.
function t(label: string, b: boolean): string { return `${label}:${b ? "T" : "F"}`; }
const strs = ["", "0", " ", "false", "x"];
console.log(strs.map((s) => t(JSON_SAFE(s), !!s)).join(" "));
function JSON_SAFE(s: string): string { return `[${s}]`; }
const nums = [0, -0, 1, -1, 0.5, Infinity, -Infinity, 0 / 0];
console.log(nums.map((n) => t(`${n}`, n ? true : false)).join(" "));
const bigs = [0n, 1n, -1n];
console.log(bigs.map((n) => t(`${n}n`, !(!n))).join(" "));
const maybeStr: (string | undefined)[] = [undefined, "", "a"];
console.log(maybeStr.map((s) => t(s ?? "undef", s ? true : false)).join(" "));
const maybeNum: (number | null)[] = [null, 0, 2];
console.log(maybeNum.map((n) => t(`${n ?? "null"}`, Boolean(n))).join(" "));
const objs: ({ v: number } | undefined)[] = [undefined, { v: 0 }];
console.log(objs.map((o) => t(o ? "obj" : "undef", !!o)).join(" "));
const empty: string[] = [];
console.log(t("emptyArray", empty ? true : false));
console.log(["", "a", "", "b"].filter((s) => s).join(","));
console.log([0, 1, 0 / 0, 2, -0].filter((n) => n).join(","));
const name = "";
const fallback = name || "anonymous";
const count = 0;
const doubled = count && count * 2;
const xs = ["x", ""];
const label = xs[0] && xs[1];
const zero = nums[0];
console.log(`${fallback} ${doubled} [${label}] ${zero || "zero"} ${xs[1] || 0} ${nums[2] && zero}`);
let n = 5;
let steps = 0;
while (n) { n -= 1; steps++; }
console.log(`steps ${steps}`);
let s = "abc";
while (s) s = s.slice(1);
console.log(`s=[${s}]`);
function describe(x: string | number | undefined): string {
  if (!x) return "falsy";
  return typeof x === "string" ? `string ${x}` : `number ${x}`;
}
console.log([describe(undefined), describe(""), describe(0), describe("q"), describe(7)].join(", "));
