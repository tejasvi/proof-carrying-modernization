// Object types whose fields are assigned become heap objects (shared by reference).
interface Counter { label: string; count: bigint }
function bump(c: Counter, by: bigint): void { c.count += by; }
const c: Counter = { label: "clicks", count: 0n };
const alias = c;
bump(c, 2n);
bump(alias, 3n);
console.log(`${c.label} ${c.count} ${alias.count} same=${c === alias}`);
const counters: Counter[] = [{ count: 1n, label: "a" }, { label: "b", count: 10n }];
for (const k of counters) k.count *= 2n;
console.log(counters.map(k => `${k.label}=${k.count}`).join(" "));
type Box = { value: string };
const boxes: Box[] = [{ value: "x" }];
const first = boxes[0];
first.value = "changed";
console.log(boxes[0].value);
