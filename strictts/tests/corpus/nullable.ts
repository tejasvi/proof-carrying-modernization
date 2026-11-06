// T | null with null checks; null and undefined together.
type Node = { id: string; parent: Node | null };
const root: Node = { id: "root", parent: null };
const child: Node = { id: "child", parent: root };
const leaf: Node = { id: "leaf", parent: child };
function path(n: Node): string {
  const parts: string[] = [];
  let cur: Node | null = n;
  while (cur !== null) {
    parts.push(cur.id);
    cur = cur.parent;
  }
  return parts.join("<");
}
console.log(path(leaf));
function depth(n: Node | null): bigint {
  if (n === null) return 0n;
  return 1n + depth(n.parent);
}
console.log(`depth ${depth(leaf)}`);
function pick(x: string | null | undefined): string {
  if (x === undefined) return "undefined";
  if (x === null) return "null";
  return `value ${x}`;
}
console.log([pick("a"), pick(null), pick(undefined)].join(", "));
function lookup(k: bigint): string | null { return k > 0n ? "found" : null; }
const opt = lookup(0n);
console.log(`${opt ?? "defaulted"} ${lookup(1n) ?? "defaulted"}`);
