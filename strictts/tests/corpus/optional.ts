// T | undefined: ??, ?., !, guards, optional parameters and fields.
interface User { name: string; nick?: string; boss?: User }
function display(u: User | undefined): string {
  if (u === undefined) return "nobody";
  const nick = u.nick ?? u.name;
  return `${nick} (boss: ${u.boss?.name ?? "none"}, boss nick: ${u.boss?.nick ?? "-"})`;
}
const ceo: User = { name: "Carol" };
const dev: User = { name: "Dave", nick: "dd", boss: ceo };
console.log(display(dev));
console.log(display(ceo));
console.log(display(undefined));
function greet(name?: string): string { return `hi ${name ?? "stranger"}`; }
console.log(`${greet()} / ${greet("Ann")}`);
const m = new Map<string, bigint>([["a", 1n]]);
const a = m.get("a");
console.log(`a=${a!} b=${m.get("b") ?? -1n}`);
let maybe: string | undefined = undefined;
if (maybe === undefined) console.log("empty maybe");
maybe = "set";
console.log(maybe + "!");
function firstLong(xs: string[]): string | undefined {
  return xs.find(x => x.length === 4);
}
const fl = firstLong(["ab", "abcd", "abcde"]);
console.log(fl !== undefined ? `found ${fl}` : "none");
console.log(`${firstLong(["x"]) === undefined}`);
