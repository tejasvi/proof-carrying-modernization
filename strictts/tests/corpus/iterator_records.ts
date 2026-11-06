// Iterator<T, TReturn, TNext> as the record of its methods: an iterator built from closures over a
// counter, consumed with next() until a result is done (its value read only when not done); the
// optional return?.() called when present and skipped when absent; a done result's value.
function countTo(n: number): Iterator<number, string> {
  let i = 0;
  let stopped = false;
  return {
    next: () => (i < n && !stopped ? { value: i++, done: false } : { value: stopped ? "stopped" : "end", done: true }),
    return: (v?: string) => { stopped = true; return { value: v ?? "returned", done: true }; },
  };
}
function evens(limit: number): Iterator<number> {
  let k = 0;
  return { next() { k += 2; return k <= limit ? { value: k, done: false } : { value: undefined, done: true }; } };
}
function take<T>(it: Iterator<T>, count: number): T[] {
  const out: T[] = [];
  while (out.length < count) {
    const r = it.next();
    if (r.done) break;
    out.push(r.value);
  }
  it.return?.();
  return out;
}
function drain(it: Iterator<number, string>): string {
  const parts: string[] = [];
  for (;;) {
    const r = it.next();
    if (r.done) { parts.push(`done:${r.value}`); break; }
    parts.push(String(r.value));
  }
  return parts.join(",");
}
const a = countTo(5);
console.log(`${take(a, 2).join(",")} | ${drain(a)}`);
console.log(`${drain(countTo(3))} | ${take(evens(7), 10).join(",")} | ${take(evens(100), 3).join(",")}`);
const b = countTo(4);
const first = b.next();
const r = b.return?.("early");
console.log(`${first.done ? "done" : first.value} ${r && r.done ? r.value : "?"} ${drain(b)} ${evens(1).return === undefined}`);
