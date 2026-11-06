// Closures: let reassigned in for-of bodies (fresh box per iteration), closures in class
// methods capturing this, closures created inside callbacks.
const getters: (() => string)[] = [];
for (let s of ["a", "b"]) {
  s = s + "!";
  getters.push(() => s);
  s = s + "?";
}
console.log(getters.map((g) => g()).join(" "));
class Clicker {
  count = 0n;
  handlers: (() => void)[] = [];
  constructor(public name: string) {
    this.handlers.push(() => { this.count++; });
    this.handlers.push(() => { this.count += 10n; });
  }
  fire(): string {
    this.handlers.forEach((h) => h());
    return `${this.name} ${this.count}`;
  }
}
const c = new Clicker("btn");
c.fire();
console.log(c.fire());
const adders = [1n, 2n, 3n].map((k) => (x: bigint) => x + k);
console.log(adders.map((f) => f(10n)).join(","));
function counterFactory(): { next: () => bigint; reset: () => void } {
  let v = 0n;
  const next = () => ++v;
  const reset = () => { v = 0n; };
  return { next, reset };
}
const cf = counterFactory();
cf.next(); cf.next();
const before = cf.next();
cf.reset();
console.log(`${before} ${cf.next()}`);
