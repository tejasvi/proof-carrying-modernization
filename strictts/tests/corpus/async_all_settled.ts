// Promise.allSettled over a tuple of different types and over an array: every outcome is kept
// (never rejects), narrowing on status, the reason of a rejection, the order of the element
// reactions against other jobs, empty inputs.
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
function describe(r: PromiseSettledResult<number>): string {
  if (r.status === "fulfilled") return `fulfilled ${r.value}`;
  return `rejected ${r.reason instanceof Error ? r.reason.message : String(r.reason)}`;
}

console.log("start");
Promise.allSettled([okAfter(2n, 1), failAfter(1n, "boom"), Promise.resolve(true)]).then(([a, b, c]) => {
  console.log(`a: ${a.status === "fulfilled" ? a.value : "-"}`);
  console.log(`b: ${b.status === "rejected" ? (b.reason instanceof Error ? b.reason.message : "?") : b.value}`);
  console.log(`c: ${c.status === "fulfilled" ? c.value : "-"}`);
});
Promise.resolve(0).then(() => console.log("tick 1")).then(() => console.log("tick 2")).then(() => console.log("tick 3"));

async function main(): Promise<void> {
  const ps: Promise<number>[] = [okAfter(1n, 10), okAfter(0n, 20)];
  ps.push(okAfter(2n, 30).then((v) => { if (v > 25) throw new Error(`too big ${v}`); return v; }));
  const rs = await Promise.allSettled(ps);
  for (const r of rs) console.log(describe(r));
  const none: Promise<number>[] = [];
  const empty = await Promise.allSettled(none);
  console.log(`empty array: ${empty.length}`);
  await Promise.allSettled([]);
  console.log("empty tuple settled");
  const [x, y] = await Promise.allSettled([failAfter(0n, "first"), okAfter(1n, 7)]);
  if (x.status === "rejected" && y.status === "fulfilled") console.log(`pair: ${x.reason instanceof Error ? x.reason.message : "?"} ${y.value}`);
}
main().then(() => console.log("main resolved"));
console.log("end of sync");
