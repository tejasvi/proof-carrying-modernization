// Disjoint primitive unions narrowed with typeof.
type Val = string | bigint | boolean;
function show(v: Val): string {
  if (typeof v === "string") return `str(${v})`;
  if (typeof v === "bigint") return `big(${v * 2n})`;
  return `bool(${v ? "yes" : "no"})`;
}
const vals: Val[] = ["a", 21n, true, false];
console.log(vals.map(show).join(" "));
function len(x: string | string[]): string {
  return typeof x === "string" ? `s:${x}` : `arr:${x.join("/")}`;
}
console.log(`${len("abc")} ${len(["p", "q"])}`);
let u: string | bigint = "start";
u = 5n;
console.log(typeof u === "bigint" ? `now big ${u}` : "still string");
