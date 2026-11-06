// Promise corner cases: resolving a then-chain with promises, finally passthrough of
// rejections, catch after then, nested async returning promises, Promise.race with settled.
const log: string[] = [];
const rejected: Promise<string> = Promise.reject(new Error("boom"));
rejected
  .then((v) => { log.push(`then ${v}`); return v; })
  .finally(() => { log.push("finally on rejected"); })
  .catch((e) => { log.push(`catch ${e.message}`); return "x"; })
  .then(() => console.log(log.join(" / ")));
async function inner(): Promise<bigint> { await null; return 41n; }
async function outer(): Promise<bigint> { const v = await inner(); return v + 1n; }
outer().then((v) => console.log(`outer ${v}`));
const settled = Promise.resolve("settled");
Promise.race([settled, new Promise<string>(() => {})]).then((v) => console.log(`race ${v}`));
Promise.resolve(1n).then((x) => Promise.resolve(x + 1n)).then((y) => console.log(`flattened ${y}`));
console.log("sync");
