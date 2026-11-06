// Recursive type aliases (immutable trees, lists): named types with fold/unfold.
type Tree = { kind: "leaf"; value: bigint } | { kind: "node"; left: Tree; right: Tree };
function sum(t: Tree): bigint {
  return t.kind === "leaf" ? t.value : sum(t.left) + sum(t.right);
}
function show(t: Tree): string {
  if (t.kind === "leaf") return `${t.value}`;
  return `(${show(t.left)} ${show(t.right)})`;
}
const leaf = (v: bigint): Tree => ({ kind: "leaf", value: v });
const t: Tree = { kind: "node", left: leaf(1n), right: { kind: "node", left: leaf(2n), right: leaf(3n) } };
console.log(`${show(t)} = ${sum(t)}`);
interface Cons { head: string; tail: Cons | undefined }
function build(xs: string[]): Cons | undefined {
  let acc: Cons | undefined = undefined;
  for (const x of xs.reverse()) acc = { head: x, tail: acc };
  return acc;
}
function toStr(l: Cons | undefined): string {
  return l === undefined ? "nil" : `${l.head}:${toStr(l.tail)}`;
}
console.log(toStr(build(["a", "b", "c"])));
