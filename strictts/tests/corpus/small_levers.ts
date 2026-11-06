// @extern
// Small library cases: the first key of a Map / Set by keys().next().value (a bounded cache
// drops its oldest entry); Math.random and Date.now as function values (a default `rand`, a
// stored clock: the same oracles as the calls); String.fromCodePoint, with Node's RangeError
// for an invalid code point; the resolve function of `new Promise((r) => setTimeout(r, ms))`,
// whose unknown parameter receives undefined when the timer calls it with none (the cast stands
// in for the host's setTimeout type, which takes any function).
const cache = new Map<string, number>();
function remember(k: string, v: number): void {
  cache.set(k, v);
  if (cache.size > 2) {
    const oldest = cache.keys().next().value;
    if (oldest !== undefined) cache.delete(oldest);
  }
}
remember("a", 1); remember("b", 2); remember("c", 3); remember("b", 4); remember("d", 5);
const seen = new Set<number>([7, 8]);
const empty = new Map<string, number>();
console.log(`${[...cache.keys()].join(",")} ${seen.values().next().value} ${String(empty.keys().next().value)} ${cache.values().next().value}`);
function pick(xs: string[], rand: () => number = Math.random): string { return xs[Math.floor(rand() * xs.length)]; }
const clock: () => number = Date.now;
console.log(`${pick(["x", "y"], () => 0.7)} ${pick(["z"])} ${clock() > 0}`);
function cp(...codes: number[]): string {
  try { return String.fromCodePoint(...codes); } catch (e) { return e instanceof Error ? `${e.name}: ${e.message}` : "?"; }
}
const smile = String.fromCodePoint(72, 0x1f600, 105);
console.log(`${smile} ${smile.length} ${cp(97, 98)} ${cp(-1)} | ${cp(1.5)} | ${cp(0x110000)} ${String.fromCodePoint()}`);
async function main(): Promise<void> {
  const order: string[] = [];
  const nap = (ms: number) => new Promise((r) => setTimeout(r as () => void, ms));
  const t = nap(5).then((v) => { order.push(`slept ${String(v)}`); });
  order.push("sync");
  await t;
  console.log(order.join(", "));
}
void main();
