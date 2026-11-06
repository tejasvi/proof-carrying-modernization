// Nested functions compared by identity: one function object per scope instantiation (its cell
// is created at the declaration); optional handlers (truthiness of a function); handlers kept in
// object fields and compared.
const subs = new Set<(n: number) => void>();
function component(name: string): () => void {
  const seen: number[] = [];
  function onValue(n: number): void { seen.push(n); console.log(`${name} got ${n} (${seen.length})`); }
  subs.add(onValue);
  subs.add(onValue);
  return () => { subs.delete(onValue); };
}
const offA = component("A");
const offB = component("B");
console.log(`${subs.size}`);
for (const s of subs) s(1);
offA();
for (const s of subs) s(2);
offB();
console.log(`${subs.size}`);
class Emitter {
  handler: ((n: number) => void) | undefined = undefined;
  fire(n: number): string { if (this.handler) { this.handler(n); return "fired"; } return "no handler"; }
  isHandler(h: (n: number) => void): boolean { return this.handler === h; }
}
const em = new Emitter();
const h1 = (n: number): void => { console.log(`h1 ${n}`); };
console.log(em.fire(0));
em.handler = h1;
console.log(`${em.fire(5)} ${em.isHandler(h1)} ${em.isHandler((n) => { console.log(`${n}`); })}`);
