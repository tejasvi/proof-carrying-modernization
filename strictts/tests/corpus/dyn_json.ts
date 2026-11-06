// @extern
// Untyped JSON.parse results are unknown values (arrays of unknown, objects as dictionaries of
// unknown), replayed from the Node run; narrowing, `in` and checked casts read them.
const raw = '{"name":"ann","tags":["a","b"],"age":41,"nested":{"ok":true},"none":null}';
const j: unknown = JSON.parse(raw);
function field(o: unknown, k: string): unknown {
  if (typeof o === "object" && o !== null && k in o) return (o as Record<string, unknown>)[k];
  return undefined;
}
const tags = field(j, "tags");
console.log(`${typeof j} ${Array.isArray(j)} ${typeof field(j, "name")} ${field(j, "age") === 41} ${Array.isArray(tags)}`);
console.log(`${String(field(j, "name"))} ${String(tags)} ${field(j, "none") === null} ${field(j, "missing") === undefined}`);
const nested = field(j, "nested");
console.log(`${typeof nested} ${field(nested, "ok") === true} ${String(field(nested, "ok"))}`);
const list = JSON.parse('[1, "two", null, [3]]') as unknown[];
const listAsUnknown: unknown = list;
console.log(`${list.length} ${list.map((x) => typeof x).join(",")} ${String(listAsUnknown)}`);
// `typeof x === "object"` narrows an unknown to `object | null`: null must still fail `x !== null`
console.log(`${field(null, "name") === undefined} ${field(list[2], "x") === undefined} ${field(j, "nested") !== null}`);
