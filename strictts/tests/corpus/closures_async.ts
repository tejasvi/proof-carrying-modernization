// Boxed variables shared between async functions across await points.
let shared = 0n;
const events: string[] = [];
async function incr(name: string, times: bigint): Promise<void> {
  for (let i = 0n; i < times; i++) {
    const before = shared;
    await null;
    shared = before + 1n;
    events.push(`${name}${shared}`);
  }
}
async function main(): Promise<void> {
  await Promise.all([incr("a", 2n), incr("b", 2n)]);
  console.log(`shared=${shared} events=${events.join(" ")}`);
  let local = "x";
  const add = async (s: string): Promise<void> => { await null; local += s; };
  await add("y");
  await add("z");
  console.log(local);
}
main();
