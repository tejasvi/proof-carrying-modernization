// Records with function-valued fields (object literal methods without `this`).
interface Ops { name: string; apply: (x: bigint) => bigint; describe(): string }
function make(name: string, k: bigint): Ops {
  return {
    name,
    apply: (x) => x * k,
    describe() { return `${name} times ${k}`; },
  };
}
const ops = [make("double", 2n), make("triple", 3n)];
for (const o of ops) console.log(`${o.describe()}: ${o.apply(7n)}`);
const calc = {
  total: 0n,
  add(n: bigint): bigint { return n + 1n; },
};
console.log(`${calc.add(41n)} ${calc.total}`);
