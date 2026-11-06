// Closures capturing constants and boxed (reassigned) let variables.
function makeCounter(start: bigint): { inc: () => bigint; get: () => bigint } {
  let count = start;
  return {
    inc: () => { count += 1n; return count; },
    get: () => count,
  };
}
const c1 = makeCounter(10n);
const c2 = makeCounter(100n);
c1.inc(); c1.inc(); c2.inc();
console.log(`c1=${c1.get()} c2=${c2.get()}`);
let shared = "a";
const appendB = () => { shared = shared + "b"; };
const read = () => shared;
appendB(); appendB();
console.log(read());
function adder(k: bigint): (x: bigint) => bigint {
  return (x) => x + k;
}
const add5 = adder(5n);
console.log(`${add5(1n)} ${adder(7n)(3n)}`);
let x = 1n;
const getX = () => x;
x = 2n;
console.log(`late binding sees ${getX()}`);
