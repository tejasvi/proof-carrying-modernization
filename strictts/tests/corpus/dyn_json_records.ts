// @extern
// Parsed JSON objects (dictionaries of unknown values) cast to record types: fields read by name
// and cast (absent optional fields are undefined), nested objects as nested records; an unknown
// value holding a record is cast as itself.
interface Owner { name: string; admin?: boolean }
interface Doc { id: string; size: number; owner: Owner; note?: string; tags?: unknown[] }
const raw: unknown = JSON.parse('{"id":"d1","size":3,"owner":{"name":"ann"},"tags":["a",1],"extra":true}');
const doc = raw as Doc;
console.log(`${doc.id} ${doc.size + 1} ${doc.owner.name} ${doc.owner.admin ?? "no-admin"} ${doc.note ?? "no-note"} ${doc.tags?.length ?? -1}`);
const data: Record<string, unknown> = JSON.parse('{"id":"d2","size":10,"owner":{"name":"bo","admin":true}}');
const d2 = data as unknown as Doc;
console.log(`${d2.id} ${d2.size * 2} ${d2.owner.name} ${d2.owner.admin === true} ${d2.tags === undefined}`);
const asIs: unknown = { name: "cy", admin: false } as Owner;
const o = asIs as Owner;
console.log(`${o.name} ${o.admin}`);
