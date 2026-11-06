// A dictionary spread into a record literal: a field comes from the dictionary when it has the
// key (decided at run time; later properties win), else from the earlier properties.
interface Row { id: string; note?: unknown; count?: unknown }
function toRow(data: Record<string, unknown>, id: string): Row { return { count: 0, ...data, id }; }
const r1 = toRow({ note: "hi", id: "ignored", extra: true }, "A");
const r2 = toRow({}, "B");
const r3 = toRow({ count: 5 }, "C");
for (const r of [r1, r2, r3]) console.log(`${r.id} ${String(r.note)} ${String(r.count)}`);
