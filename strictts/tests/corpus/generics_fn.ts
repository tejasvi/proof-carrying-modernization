// Generic functions instantiated at several types (monomorphisation).
function identity<T>(x: T): T { return x; }
function mapArr<A, B>(xs: A[], f: (a: A) => B): B[] {
  const out: B[] = [];
  for (const x of xs) out.push(f(x));
  return out;
}
function firstOr<T>(xs: T[], d: T): T {
  const v = xs.at(0);
  return v === undefined ? d : v;
}
function pairUp<K, V>(k: K, v: V): [K, V] { return [k, v]; }
console.log(identity("str"));
console.log(`${identity(42n)}`);
console.log(mapArr([1n, 2n, 3n], (n) => `#${n}`).join(" "));
console.log(mapArr(["a", "bb"], (s) => s.length === 1).join(" "));
console.log(`${firstOr([], 7n)} ${firstOr(["z"], "d")}`);
const pr = pairUp("k", true);
console.log(`${pr[0]} ${pr[1]}`);
function countBy<T>(xs: T[], key: (x: T) => string): Map<string, bigint> {
  const m = new Map<string, bigint>();
  for (const x of xs) {
    const k = key(x);
    m.set(k, (m.get(k) ?? 0n) + 1n);
  }
  return m;
}
for (const [k, n] of countBy(["apple", "avocado", "banana"], (s) => (s === "banana" ? "b" : "a"))) console.log(`${k}: ${n}`);
