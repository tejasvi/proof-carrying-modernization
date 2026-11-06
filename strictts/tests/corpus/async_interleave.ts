// Several async functions interleaving at await points.
async function worker(name: string, n: bigint): Promise<bigint> {
  let acc = 0n;
  for (let i = 1n; i <= n; i++) {
    console.log(`${name}:${i}`);
    acc += await Promise.resolve(i);
  }
  return acc;
}
async function main(): Promise<void> {
  const a = worker("a", 3n);
  const b = worker("b", 2n);
  const c = worker("c", 1n);
  console.log("all started");
  const ra = await a;
  console.log(`a=${ra}`);
  const rb = await b;
  const rc = await c;
  console.log(`b=${rb} c=${rc}`);
}
main().then(() => console.log("main finished"));
console.log("sync end");
