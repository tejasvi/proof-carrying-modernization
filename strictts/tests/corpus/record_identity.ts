// Objects compared by identity (===, Set elements, Map keys, indexOf/includes/lastIndexOf): each
// object literal evaluation is a new object, references to one object are equal, spreads and
// object rest patterns make new objects, and field reads, method calls and destructuring read
// through the object. Comparing with null, undefined or a string compares no objects.
interface Item { id: string; n: number }
const a: Item = { id: "a", n: 1 };
const b: Item = { id: "a", n: 1 };
const items: Item[] = [a, b, { id: "c", n: 3 }, a];
const selected = items[1];
console.log(`${selected === b} ${selected === a} ${selected !== a} ${items.indexOf(a)} ${items.lastIndexOf(a)} ${items.indexOf(b)} ${items.includes({ id: "a", n: 1 })}`);
const seen = new Set<Item>();
for (const it of [a, b, a, items[2]]) seen.add(it);
console.log(`${seen.size} ${[...seen].map((x) => `${x.id}${x.n}`).join(",")} ${seen.has(a)} ${seen.has({ ...a })}`);
const copy = { ...a, n: 5 };
const same = { ...a };
const { id, n } = copy;
console.log(`${copy === a} ${same === a} ${id} ${n} ${a.n} ${copy.id === a.id} ${same.n === a.n}`);
function pick(xs: Item[], target: Item): number { let k = -1; xs.forEach((x, i) => { if (x === target) k = i; }); return k; }
console.log(`${pick(items, items[2])} ${pick(items, { id: "c", n: 3 })} ${items.find((x) => x.n === 3) === items[2]} ${items.filter((x) => x !== a).length}`);
function idOf<T>(x: T): T { return x; }
console.log(`${idOf(a) === a} ${idOf(b) === a} ${typeof a} ${typeof a === "object"}`);

// Map keys and values: the last row of each turn, found by identity
interface Row { turn: string; text: string }
const rows: Row[] = [{ turn: "t1", text: "x" }, { turn: "t2", text: "y" }, { turn: "t1", text: "z" }];
const lastOfTurn = new Map<string, Row>();
for (const r of rows) lastOfTurn.set(r.turn, r);
console.log(rows.filter((r) => lastOfTurn.get(r.turn) === r).map((r) => r.text).join(","));
const notes = new Map<Row, string>();
notes.set(rows[0], "first");
notes.set({ turn: "t1", text: "x" }, "twin");
notes.set(rows[0], "again");
console.log(`${notes.size} ${notes.get(rows[0])} ${notes.get({ turn: "t1", text: "x" }) ?? "none"}`);

// a union with strings: comparing with a string is not an identity comparison
type Choice = Item | "none" | null;
function describe(p: Choice): string {
  if (p === null) return "null";
  if (p === "none") return "no item";
  return p === a ? "a itself" : `${p.id}${p.n}`;
}
console.log([describe(a), describe(b), describe("none"), describe(null)].join("; "));

// an object with function fields, compared by identity and called through
interface Store { getItem(k: string): string | null; setItem(k: string, v: string): void }
const data = new Map<string, string>();
const memory: Store = { getItem: (k) => data.get(k) ?? null, setItem: (k, v) => { data.set(k, v); } };
function storeOf(s: Store | undefined): Store { return s === undefined ? memory : s; }
const st = storeOf(undefined);
st.setItem("k", "v1");
console.log(`${st === memory} ${st.getItem("k")} ${storeOf(memory).getItem("missing")}`);
const handlers = new Set<() => void>();
const tick = () => { handlers.clear(); };
handlers.add(tick);
console.log(`${typeof tick} ${typeof tick === "function"} ${handlers.has(tick)}`);

// an object rest pattern makes a new object
interface Full { id: string; n: number; tag: string }
const full: Full = { id: "f", n: 2, tag: "t" };
const { id: fid, ...rest } = full;
const rests = [rest];
console.log(`${fid} ${rest.n}${rest.tag} ${rests.includes(rest)} ${rests.includes({ ...rest })}`);

// a discriminated union compared by identity
type Shape = { kind: "sq"; side: number } | { kind: "ci"; r: number };
const shapes: Shape[] = [{ kind: "sq", side: 2 }, { kind: "ci", r: 1 }];
const big: Shape = shapes[0];
function area(s: Shape): number { return s.kind === "sq" ? s.side * s.side : 3 * s.r * s.r; }
console.log(`${shapes.indexOf(big)} ${shapes.indexOf({ kind: "ci", r: 1 })} ${shapes.map(area).join(",")}`);

// objects held by a class, compared with the current one
class Player {
  busy: { line: Item } | null = null;
  start(line: Item): void { this.busy = { line }; }
  done(line: Item): string { return !this.busy || this.busy.line !== line ? "stale" : "done"; }
}
const pl = new Player();
pl.start(a);
console.log(`${pl.done(b)} ${pl.done(a)}`);
