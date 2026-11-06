// @reject unsupported-conversion
// A dictionary with named properties used as a record type would be a copy: the write through
// the dictionary after the conversion would not show through the record (Node prints "late")
interface Consent { state?: unknown; [k: string]: unknown }
interface Plain { state?: unknown }
const c: Consent = { state: "early" };
const p: Plain = c;
c.state = "late";
console.log(String(p.state));
