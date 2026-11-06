// async/await ordering relative to synchronous code.
async function task(name: string, steps: bigint): Promise<string> {
  console.log(`${name} start`);
  for (let i = 0n; i < steps; i++) {
    await null;
    console.log(`${name} step ${i}`);
  }
  return `${name} done`;
}
console.log("main 1");
const p = task("A", 2n);
console.log("main 2");
p.then((r) => console.log(r));
console.log("main 3");
