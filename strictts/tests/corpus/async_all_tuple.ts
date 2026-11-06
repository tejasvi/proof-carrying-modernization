// Promise.all over tuples of different types: the order of the element reactions against other
// jobs (then chains, queueMicrotask, timers), plain values among the promises, nested Promise.all,
// awaits inside the elements, and the empty tuple.
async function num(name: string, ticks: bigint, v: number): Promise<number> {
  for (let i = 0n; i < ticks; i++) await null;
  console.log(`${name} -> ${v}`);
  return v;
}
async function str(name: string, ticks: bigint): Promise<string> {
  for (let i = 0n; i < ticks; i++) await null;
  console.log(`${name} -> "${name}"`);
  return name;
}
async function flag(ticks: bigint): Promise<boolean> {
  for (let i = 0n; i < ticks; i++) await null;
  console.log(`flag -> ${ticks > 1n}`);
  return ticks > 1n;
}
function later(ms: number, s: string): Promise<string> {
  return new Promise((resolve) => setTimeout(() => { console.log(`timer ${s}`); resolve(s); }, ms));
}
async function pair(tag: string): Promise<[number, string]> {
  const [a, b] = await Promise.all([num(`${tag}.a`, 2n, 7), str(`${tag}.b`, 1n)]);
  console.log(`pair ${tag} done`);
  return [a * 2, b + "!"];
}

console.log("start");
Promise.all([num("n", 3n, 1), str("s", 1n), flag(2n)]).then(([n, s, b]) => {
  console.log(`all1: ${n} ${s} ${b}`);
});
Promise.resolve("x").then((v) => { console.log(`chain1 ${v}`); return v + "y"; }).then((v) => console.log(`chain2 ${v}`));
queueMicrotask(() => console.log("microtask"));
Promise.all([42, str("plain", 0n), Promise.resolve(true)]).then(([n, s, b]) => {
  console.log(`all2: ${n} ${s} ${b}`);
});
Promise.all([]).then(() => console.log("empty tuple resolved"));

async function main(): Promise<void> {
  const [p, t, n] = await Promise.all([pair("p"), later(5, "late"), num("m", 1n, 3)]);
  console.log(`main: ${p[0]} ${p[1]} ${t} ${n}`);
  await Promise.all([]);
  console.log("after empty await");
  const [x, y] = await Promise.all([str("again", 2n), Promise.all([num("in1", 1n, 10), flag(1n)])]);
  console.log(`nested: ${x} ${y[0]} ${y[1]}`);
}
main().then(() => console.log("main resolved"));
console.log("end of sync");
