// @extern
// Regular expressions as external calls: the Lean run replays the outcomes of the Node run, so
// the names, the arguments (receiver, pattern, flags in canonical order, other arguments) and
// the order of the calls must agree with Node's.
const WORD = /^[a-z]+$/i;
const DIGITS = /\d+/g;
function classify(s: string): string {
  if (WORD.test(s)) return "word";
  if (/^\d+$/.test(s)) return "number";
  return s === "" ? "empty" : "other";
}
console.log(["abc", "Abc", "123", "a1", ""].map(classify).join(","));
const text = "a1b22c333";
console.log(`${text.replace(DIGITS, "#")} ${text.replace(/\d/, "_")} ${text.replaceAll(/[abc]/gi, "")} ${text.search(/c/)}`);
const m = /(\d+)-(\d+)/.exec("range 10-20 end");
if (m !== null) console.log(`${m[0]} ${m[1]} ${m[2]} ${m.index} ${m.length}`);
const none = "xyz".match(/\d/);
console.log(none === null ? "no match" : "match");
const all = "a1b2".match(/\d/g);
console.log(all ? `${all.length} ${all[0]}${all[1]}` : "none");
function firstNumber(s: string): number {
  const r = s.match(/-?\d+(\.\d+)?/);
  if (!r) return NaN;
  return Number(r[0]);
}
console.log(`${firstNumber("x = -12.5;")} ${firstNumber("none")} ${firstNumber("7 and 8")}`);
let hits = 0;
for (const w of ["ab", "AB", "a-b", "b"]) if (/^[ab]+$/gi.test(w)) hits++;
console.log(`hits ${hits}`);
const parts = "a, b,,c".split(/\s*,\s*/);
console.log(`${parts.length} [${parts.join("|")}] ${"x1y22z".split(/\d+/).map((p) => p.toUpperCase()).join("-")}`);
const pairs: string[] = [];
for (const m of "a=1, b=22, c=3".matchAll(/(\w)=(\d+)/g)) pairs.push(`${m[1]}:${m[2]}@${m.index}`);
console.log(`${pairs.join(" ")} ${[..."x1y2".matchAll(/\d/g)].length}`);
const swapped = "a=1, b=22".replace(/(\w)=(\d+)/g, (_m, k: string, v: string) => `${v}:${k}`);
const firstOnly = "x1y2".replace(/\d/, (d) => `<${Number(d) * 10}>`);
const withOffset = "aXbX".replaceAll(/X/g, (m, off: number) => `${m.toLowerCase()}${off}`);
const optional = "ab".replace(/(a)|(b)/g, (m, g1: string | undefined, g2: string | undefined) => g1 !== undefined ? "A" : g2 ?? "?");
console.log(`${swapped} ${firstOnly} ${withOffset} ${optional}`);
