// Function identity beyond Sets: Map keys, === and !==, indexOf/includes/lastIndexOf on arrays
// of functions, insertion order of emits, module-level const arrows (one function), handlers
// with parameters, and resolve functions kept for later.
type Handler = (n: number) => string;
const counts = new Map<Handler, number>();
const double: Handler = (n) => `${n * 2}`;
const neg = (n: number): string => `${-n}`;
for (const h of [double, neg, double]) counts.set(h, (counts.get(h) ?? 0) + 1);
console.log(`${counts.size} ${counts.get(double)} ${counts.get(neg)} ${[...counts.keys()].map((h) => h(3)).join(",")}`);
const same = double;
console.log(`${same === double} ${double === neg} ${double !== neg} ${(() => "x") === (() => "x")}`);
const order: Handler[] = [neg, double, neg];
console.log(`${order.indexOf(neg)} ${order.lastIndexOf(neg)} ${order.indexOf(double)} ${order.includes((n) => `${n}`)}`);
const queue = new Set<(v: number) => void>();
function later(): Promise<number> { return new Promise<number>((resolve) => { queue.add(resolve); }); }
async function main(): Promise<void> {
  const p1 = later();
  const p2 = later();
  console.log(`waiting ${queue.size}`);
  let k = 10;
  for (const r of queue) r(k++);
  queue.clear();
  console.log(`${await p1} ${await p2} ${queue.size}`);
}
main();
