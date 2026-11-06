// Promise.all over a tuple of different types with a rejection in the middle: the result is
// rejected at the first rejection, the other elements still run (their reactions are no-ops),
// a second rejection is ignored; awaited inside try/catch and handled with catch.
async function okAfter(ticks: bigint, v: number): Promise<number> {
  for (let i = 0n; i < ticks; i++) await null;
  console.log(`ok ${v}`);
  return v;
}
async function failAfter(ticks: bigint, msg: string): Promise<string> {
  for (let i = 0n; i < ticks; i++) await null;
  console.log(`fail ${msg}`);
  throw new Error(msg);
}
async function word(ticks: bigint, s: string): Promise<string> {
  for (let i = 0n; i < ticks; i++) await null;
  console.log(`word ${s}`);
  return s;
}

console.log("start");
Promise.all([okAfter(3n, 1), failAfter(1n, "boom"), word(2n, "late")])
  .then(([a, b, c]) => console.log(`unexpected ${a} ${b} ${c}`))
  .catch((e) => { console.log(`caught ${e.message}`); });
Promise.resolve(0).then(() => console.log("tick 1")).then(() => console.log("tick 2")).then(() => console.log("tick 3"));

async function main(): Promise<void> {
  try {
    const [n, s] = await Promise.all([okAfter(1n, 5), failAfter(2n, "second")]);
    console.log(`unexpected ${n} ${s}`);
  } catch (e) {
    console.log(`main caught ${e instanceof Error ? e.message : "?"}`);
  }
  try {
    await Promise.all([failAfter(2n, "first of two"), okAfter(0n, 9), failAfter(1n, "earlier")]);
  } catch (e) {
    console.log(`two rejections: ${e instanceof Error ? e.message : "?"}`);
  }
  const [x, y] = await Promise.all([okAfter(0n, 2), word(0n, "fine")]);
  console.log(`after: ${x} ${y}`);
}
main().then(() => console.log("main resolved"));
console.log("end of sync");
