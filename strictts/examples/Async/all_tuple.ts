// Promise.all over a tuple of different types, and Promise.allSettled over a tuple with a
// rejection, against a then chain.
async function count(ticks: bigint): Promise<bigint> {
  for (let i = 0n; i < ticks; i++) await null;
  console.log(`count ${ticks}`);
  return ticks;
}
async function word(ticks: bigint, s: string): Promise<string> {
  for (let i = 0n; i < ticks; i++) await null;
  console.log(`word ${s}`);
  return s;
}
async function fail(msg: string): Promise<bigint> {
  await null;
  throw new Error(msg);
}
Promise.all([count(2n), word(1n, "a")]).then(([n, s]) => console.log(`all: ${n} ${s}`));
Promise.allSettled([word(0n, "b"), fail("no")]).then(([x, y]) => {
  console.log(`settled: ${x.status === "fulfilled" ? x.value : "-"} ${y.status}`);
});
Promise.resolve(0n).then(() => console.log("tick 1")).then(() => console.log("tick 2"));
console.log("sync");
