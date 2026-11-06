// Optional chaining: method calls, element access, long chains, calls of optional functions.
interface Dept { name: string; head?: Emp; members: Emp[] }
interface Emp { name: string; dept?: Dept; greet?: (s: string) => string }
const eng: Dept = { name: "eng", members: [] };
const alice: Emp = { name: "alice", dept: eng, greet: (s) => `hi ${s}` };
const bob: Emp = { name: "bob" };
const engWithHead: Dept = { name: "eng2", head: alice, members: [alice, bob] };
const carol: Emp = { name: "carol", dept: engWithHead };
const emps: (Emp | undefined)[] = [alice, bob, carol, undefined];
for (const e of emps) {
  const deptName = e?.dept?.name ?? "-";
  const headName = e?.dept?.head?.name ?? "-";
  const greeting = e?.greet?.("you") ?? "(no greet)";
  const firstMember = e?.dept?.members[0]?.name ?? "-";
  console.log(`${e?.name ?? "nobody"}: dept=${deptName} head=${headName} ${greeting} first=${firstMember}`);
}
const arr: string[] | undefined = ["q"];
console.log(`${arr?.[0] ?? "?"} ${arr?.length === 1}`);
