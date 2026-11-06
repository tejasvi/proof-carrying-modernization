// An event emitter: Map of listener arrays, closures unsubscribing themselves, memoization.
type Listener = (payload: string) => void;
// (functions have no identity in StrictTS, so listeners are removed by id)
class Emitter {
  private listeners = new Map<string, Map<bigint, Listener>>();
  private nextId = 0n;
  on(event: string, fn: Listener): () => void {
    const id = this.nextId++;
    const list = this.listeners.get(event) ?? new Map<bigint, Listener>();
    list.set(id, fn);
    this.listeners.set(event, list);
    return () => {
      const cur = this.listeners.get(event);
      if (cur !== undefined) cur.delete(id);
    };
  }
  emit(event: string, payload: string): bigint {
    let n = 0n;
    const list = this.listeners.get(event);
    if (list === undefined) return 0n;
    for (const fn of list.values()) { fn(payload); n++; }
    return n;
  }
}
const em = new Emitter();
const seen: string[] = [];
const off1 = em.on("msg", (p) => seen.push(`one:${p}`));
em.on("msg", (p) => seen.push(`two:${p}`));
console.log(`${em.emit("msg", "a")} listeners`);
off1();
console.log(`${em.emit("msg", "b")} listeners, ${em.emit("other", "c")} on other`);
console.log(seen.join(" "));
function memoize(f: (n: bigint) => bigint): (n: bigint) => bigint {
  const cache = new Map<bigint, bigint>();
  return (n) => {
    const hit = cache.get(n);
    if (hit !== undefined) return hit;
    const v = f(n);
    cache.set(n, v);
    return v;
  };
}
let calls = 0n;
const slowSquare = (n: bigint): bigint => { calls++; return n * n; };
const fast = memoize(slowSquare);
console.log(`${fast(12n)} ${fast(12n)} ${fast(3n)} calls=${calls}`);
