// Default, optional and rest parameters; JavaScript passes callback arguments by position.
function greet(name: string, greeting = "Hello", punct?: string): string {
  return `${greeting}, ${name}${punct ?? "."}`;
}
console.log(greet("Ann"));
console.log(greet("Bob", "Hi"));
console.log(greet("Cy", "Yo", "!"));
console.log(greet("Di", undefined, "?"));
function joinAll(sep: string, ...parts: string[]): string { return parts.join(sep); }
console.log(joinAll("-", "a", "b", "c"));
console.log(joinAll("+"));
const arr = ["x", "y"];
console.log(joinAll("/", ...arr));
function withIndex(s: string, i?: number): string { return i === undefined ? `${s}(no index)` : `${s}(index)`; }
console.log(["p", "q"].map(withIndex).join(" "));
function defaults(a: bigint, b: bigint = a * 2n, c: bigint = a + b): string { return `${a} ${b} ${c}`; }
console.log(defaults(1n));
console.log(defaults(1n, 5n));
const arrow = (x: string, times: bigint = 2n): string => {
  let out = "";
  for (let i = 0n; i < times; i++) out += x;
  return out;
};
console.log(`${arrow("ab")} ${arrow("c", 3n)}`);
