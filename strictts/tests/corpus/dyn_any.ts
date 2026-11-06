// `any` values are unknown values: property and index reads on their runtime values (absent
// keys are undefined, reads on null and undefined throw TypeError), String(x), string
// concatenation, and checked casts into typed positions.
function read(o: any, k: string): string {
  try {
    return String(o[k]);
  } catch (e) {
    return `${(e as Error).name}: ${(e as Error).message}`;
  }
}
const data: any = { a: 1, list: [10, 20, 30], s: "hey", n: null, nested: { deep: true } };
console.log([read(data, "a"), read(data, "missing"), read(data.list, "1"), read(data.list, "5"), read(data.list, "length"),
  read(data.s, "length"), read(data.s, "0"), read(data.s, "9"), read(data.n, "x"), read(data.missing, "y"),
  read(data.nested, "deep"), read(data, "list")].join(" | "));
const n: number = data.a;
const s: string = data.s;
const flag: boolean = data.nested.deep;
console.log(`${n + 1} ${s.toUpperCase()} ${flag} ${data.list.length} ${data.list[2]} ${typeof data.nested} ${data.a === 1} ${data.n === null}`);
console.log("a=" + data.a + ", list=" + data.list + ", nested=" + data.nested + ", missing=" + data.missing);
function len(x: any): number { return Array.isArray(x) ? x.length : typeof x === "string" ? x.length : -1; }
console.log(`${len([1, 2])} ${len("abc")} ${len(5)} ${len(null)}`);
