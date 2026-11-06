// @numbers
// A larger program (≈320 lines) used to measure elaboration time of the generated Lean:
// an inventory / order-processing simulation with classes, records, unions, maps, sets,
// closures, generics, async workflows and string reports.

type Category = "tools" | "garden" | "kitchen" | "toys";

interface Product {
  sku: string;
  name: string;
  category: Category;
  priceCents: number;
  tags: string[];
}

interface OrderLine { sku: string; qty: number }

type OrderStatus =
  | { kind: "pending" }
  | { kind: "paid"; amountCents: number }
  | { kind: "shipped"; trackingId: string; amountCents: number }
  | { kind: "cancelled"; reason: string };

class Order {
  status: OrderStatus = { kind: "pending" };
  readonly lines: OrderLine[] = [];
  constructor(public readonly id: string, public customer: string) {}
  add(sku: string, qty: number): Order {
    const idx = this.lines.findIndex((l) => l.sku === sku);
    if (idx >= 0) {
      const existing = this.lines[idx];
      this.lines[idx] = { sku, qty: existing.qty + qty };
    } else {
      this.lines.push({ sku, qty });
    }
    return this;
  }
  itemCount(): number {
    return this.lines.reduce((n, l) => n + l.qty, 0);
  }
}

class Inventory {
  private stock = new Map<string, number>();
  private products = new Map<string, Product>();
  private log: string[] = [];
  register(p: Product, initial: number): void {
    this.products.set(p.sku, p);
    this.stock.set(p.sku, initial);
    this.log.push(`register ${p.sku} x${initial}`);
  }
  product(sku: string): Product | undefined {
    return this.products.get(sku);
  }
  available(sku: string): number {
    return this.stock.get(sku) ?? 0;
  }
  reserve(sku: string, qty: number): boolean {
    const have = this.available(sku);
    if (have < qty) {
      this.log.push(`shortage ${sku} want ${qty} have ${have}`);
      return false;
    }
    this.stock.set(sku, have - qty);
    this.log.push(`reserve ${sku} x${qty}`);
    return true;
  }
  restock(sku: string, qty: number): void {
    this.stock.set(sku, this.available(sku) + qty);
    this.log.push(`restock ${sku} x${qty}`);
  }
  lowStock(threshold: number): string[] {
    const out: string[] = [];
    for (const [sku, n] of this.stock) {
      if (n <= threshold) out.push(sku);
    }
    return out.sort();
  }
  history(): string[] {
    return [...this.log];
  }
  skus(): string[] {
    return [...this.products.keys()];
  }
}

function formatCents(c: number): string {
  const sign = c < 0 ? "-" : "";
  const abs = Math.abs(c);
  const dollars = Math.floor(abs / 100);
  const cents = abs % 100;
  return `${sign}$${dollars}.${`${cents}`.padStart(2, "0")}`;
}

function lineTotal(inv: Inventory, line: OrderLine): number {
  const p = inv.product(line.sku);
  if (p === undefined) return 0;
  return p.priceCents * line.qty;
}

function orderTotal(inv: Inventory, o: Order): number {
  let total = 0;
  for (const line of o.lines) total += lineTotal(inv, line);
  return total;
}

function discountFor(category: Category, qty: number): number {
  switch (category) {
    case "tools":
      return qty >= 3 ? 10 : 0;
    case "garden":
      return qty >= 5 ? 15 : 5;
    case "kitchen":
      return 0;
    case "toys":
      return qty >= 2 ? 20 : 0;
  }
}

function applyDiscounts(inv: Inventory, o: Order): number {
  let total = 0;
  for (const line of o.lines) {
    const p = inv.product(line.sku);
    if (p === undefined) continue;
    const pct = discountFor(p.category, line.qty);
    const gross = p.priceCents * line.qty;
    total += gross - Math.round((gross * pct) / 100);
  }
  return total;
}

function describeStatus(s: OrderStatus): string {
  switch (s.kind) {
    case "pending":
      return "pending";
    case "paid":
      return `paid ${formatCents(s.amountCents)}`;
    case "shipped":
      return `shipped (${s.trackingId}) ${formatCents(s.amountCents)}`;
    case "cancelled":
      return `cancelled: ${s.reason}`;
  }
}

function groupBy<T, K>(xs: T[], key: (x: T) => K): Map<K, T[]> {
  const m = new Map<K, T[]>();
  for (const x of xs) {
    const k = key(x);
    const bucket = m.get(k);
    if (bucket === undefined) m.set(k, [x]);
    else bucket.push(x);
  }
  return m;
}

function uniqueTags(products: Product[]): string[] {
  const s = new Set<string>();
  for (const p of products) for (const t of p.tags) s.add(t);
  return [...s].sort();
}

function makeIdGenerator(prefix: string): () => string {
  let n = 0;
  return () => {
    n++;
    return `${prefix}-${`${n}`.padStart(3, "0")}`;
  };
}

const catalog: Product[] = [
  { sku: "HAM-1", name: "Hammer", category: "tools", priceCents: 1599, tags: ["steel", "hand"] },
  { sku: "SAW-2", name: "Saw", category: "tools", priceCents: 2450, tags: ["steel", "hand", "sharp"] },
  { sku: "HOS-3", name: "Hose", category: "garden", priceCents: 3200, tags: ["rubber"] },
  { sku: "POT-4", name: "Flower pot", category: "garden", priceCents: 899, tags: ["clay"] },
  { sku: "PAN-5", name: "Frying pan", category: "kitchen", priceCents: 4100, tags: ["steel", "cook"] },
  { sku: "KNF-6", name: "Knife", category: "kitchen", priceCents: 2999, tags: ["steel", "sharp", "cook"] },
  { sku: "CAR-7", name: "Toy car", category: "toys", priceCents: 1250, tags: ["plastic"] },
  { sku: "PUZ-8", name: "Puzzle", category: "toys", priceCents: 1875, tags: ["cardboard"] },
];

const inventory = new Inventory();
catalog.forEach((p, i) => inventory.register(p, 3 + (i % 4)));

const nextOrderId = makeIdGenerator("ORD");
const orders: Order[] = [];

function placeOrder(customer: string, lines: [string, number][]): Order {
  const o = new Order(nextOrderId(), customer);
  for (const [sku, qty] of lines) o.add(sku, qty);
  orders.push(o);
  return o;
}

placeOrder("alice", [["HAM-1", 1], ["SAW-2", 2], ["HAM-1", 2]]);
placeOrder("bob", [["HOS-3", 5], ["POT-4", 6]]);
placeOrder("carol", [["PAN-5", 1], ["KNF-6", 1], ["CAR-7", 3]]);
placeOrder("dave", [["PUZ-8", 2], ["CAR-7", 1]]);
placeOrder("erin", [["KNF-6", 9]]);

function fulfil(o: Order): void {
  const reserved: OrderLine[] = [];
  for (const line of o.lines) {
    if (!inventory.reserve(line.sku, line.qty)) {
      for (const r of reserved) inventory.restock(r.sku, r.qty);
      o.status = { kind: "cancelled", reason: `out of ${line.sku}` };
      return;
    }
    reserved.push(line);
  }
  o.status = { kind: "paid", amountCents: applyDiscounts(inventory, o) };
}

for (const o of orders) fulfil(o);

let trackingCounter = 1000;
function ship(o: Order): void {
  if (o.status.kind !== "paid") return;
  trackingCounter += 7;
  o.status = { kind: "shipped", trackingId: `TRK${trackingCounter}`, amountCents: o.status.amountCents };
}
orders.filter((o) => o.customer !== "carol").forEach(ship);

console.log("== orders ==");
for (const o of orders) {
  const gross = orderTotal(inventory, o);
  console.log(`${o.id} ${o.customer.padEnd(6)} items=${o.itemCount()} gross=${formatCents(gross)} -> ${describeStatus(o.status)}`);
}

console.log("== by category ==");
const byCat = groupBy(catalog, (p) => p.category);
for (const [cat, ps] of byCat) {
  const names = ps.map((p) => p.name).join(", ");
  const avg = ps.reduce((s, p) => s + p.priceCents, 0) / ps.length;
  console.log(`${cat}: ${names} (avg ${formatCents(Math.round(avg))})`);
}

console.log("== stock ==");
for (const sku of inventory.skus()) console.log(`${sku}: ${inventory.available(sku)}`);
const low = inventory.lowStock(1);
console.log(`low stock: ${low.length > 0 ? low.join(" ") : "none"}`);
console.log(`tags: ${uniqueTags(catalog).join(",")}`);

const revenue = orders.reduce((sum, o) => {
  const s = o.status;
  return s.kind === "paid" || s.kind === "shipped" ? sum + s.amountCents : sum;
}, 0);
console.log(`revenue ${formatCents(revenue)}`);

const cancelled = orders.filter((o) => o.status.kind === "cancelled").map((o) => o.id);
console.log(`cancelled: ${cancelled.join(" ")}`);

// price search utilities
function binarySearch(sorted: number[], target: number): number {
  let lo = 0;
  let hi = sorted.length - 1;
  while (lo <= hi) {
    const mid = Math.floor((lo + hi) / 2);
    const v = sorted[mid];
    if (v === target) return mid;
    if (v < target) lo = mid + 1;
    else hi = mid - 1;
  }
  return -1;
}

function insertionSort(xs: number[]): number[] {
  const a = [...xs];
  for (let i = 1; i < a.length; i++) {
    const key = a[i];
    let j = i - 1;
    while (j >= 0 && a[j] > key) {
      a[j + 1] = a[j];
      j--;
    }
    a[j + 1] = key;
  }
  return a;
}

const prices = insertionSort(catalog.map((p) => p.priceCents));
console.log(`prices: ${prices.map(formatCents).join(" ")}`);
console.log(`index of $29.99: ${binarySearch(prices, 2999)}, of $1.00: ${binarySearch(prices, 100)}`);
const median = prices.length % 2 === 0
  ? (prices[prices.length / 2 - 1] + prices[prices.length / 2]) / 2
  : prices[(prices.length - 1) / 2];
console.log(`median ${formatCents(Math.round(median))}`);

// async restocking workflow with interleaving suppliers
async function supplier(name: string, sku: string, batches: number[]): Promise<number> {
  let delivered = 0;
  for (const b of batches) {
    await Promise.resolve();
    inventory.restock(sku, b);
    delivered += b;
    console.log(`${name} delivered ${b} of ${sku}`);
  }
  return delivered;
}

async function restockAll(): Promise<void> {
  const totals = await Promise.all([
    supplier("acme", "KNF-6", [2, 3]),
    supplier("globex", "CAR-7", [1, 1, 1]),
    supplier("initech", "HOS-3", [4]),
  ]);
  console.log(`restocked ${totals.join("+")} = ${totals.reduce((a, b) => a + b, 0)}`);
  const retry = orders.find((o) => o.customer === "erin");
  if (retry !== undefined) {
    retry.status = { kind: "pending" };
    fulfil(retry);
    console.log(`erin retry: ${describeStatus(retry.status)}`);
  }
}

restockAll().then(() => {
  const hist = inventory.history();
  console.log(`history entries: ${hist.length}, last: ${hist[hist.length - 1] ?? "none"}`);
});
setTimeout(() => console.log(`timer: ${inventory.lowStock(2).length} low after restock`), 5);
console.log("sync part done");
