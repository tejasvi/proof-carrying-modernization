// Nested closures: transitive capture, closures returned from closures, shared boxes.
function outer(a: string): () => () => string {
  const b = a + "!";
  return () => {
    const c = b + "?";
    return () => a + b + c;
  };
}
console.log(outer("hi")()());
function makePair(): [() => bigint, (d: bigint) => void] {
  let v = 0n;
  return [() => v, (d) => { v += d; }];
}
const [get, add] = makePair();
add(5n); add(7n);
console.log(`pair ${get()}`);
const compose = (f: (s: string) => string, g: (s: string) => string) => (s: string) => g(f(s));
const shout = compose((s) => s + "!", (s) => `<${s}>`);
console.log(shout("hey"));
