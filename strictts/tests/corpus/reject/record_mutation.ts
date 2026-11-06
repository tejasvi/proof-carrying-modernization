// @reject record-mutation
interface Named { name: string }
interface Person { name: string; age: bigint }
function rename(n: { name: string }): void { n.name = "x"; }
const p: Person = { name: "a", age: 1n };
const q: Named = p;
rename(q);
console.log(p.name);
