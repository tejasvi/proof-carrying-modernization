// @extern
// JSON.parse with a declared type and JSON.stringify as external calls (replayed from the Node
// run); a parse error is the error the external call throws.
interface Settings { name: string; level?: number; mode: "dark" | "light" }
function load(raw: string): Settings {
  try {
    return JSON.parse(raw) as Settings;
  } catch (e) {
    const err = e as Error;
    return { name: `invalid (${err.name})`, mode: "light" };
  }
}
const a = load('{"name":"a","level":3,"mode":"dark"}');
const b = load('{"name":"b","mode":"light"}');
const c = load("{oops");
for (const s of [a, b, c]) console.log(`${s.name} ${s.level ?? "-"} ${s.mode}`);
const n: number = JSON.parse("42");
const flag = JSON.parse("true") as boolean;
console.log(`${n + 1} ${!flag}`);
console.log(JSON.stringify({ name: a.name, level: a.level ?? 0 }));
console.log(`${JSON.stringify("q\"uote")} ${JSON.stringify(1.5)} ${JSON.stringify(null)}`);
const list = JSON.parse('[3, 1, 2]') as number[];
list.sort((x, y) => x - y);
const grid = JSON.parse('[["a", "b"], [], ["c"]]') as string[][];
console.log(`${list.join(",")} ${grid.map((row) => row.length).join("/")} ${grid[2][0]}`);
