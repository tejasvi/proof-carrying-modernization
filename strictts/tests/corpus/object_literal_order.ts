// Property initialisers are evaluated in source order (records are built in their canonical
// field order afterwards): calls, spreads, nested literals, mutable structures and returned
// literals.
const log: string[] = [];
function f(tag: string): number { log.push(tag); return log.length; }
function g(tag: string): { a: number; z: number } { log.push(tag); return { a: 100, z: 200 }; }
const r1 = { z: f("z"), b: f("b"), a: f("a") };
console.log(`${log.join(",")} | ${r1.a} ${r1.b} ${r1.z}`);
log.length = 0;
const r2 = { c: f("c1"), ...g("spread"), b: f("b1") };
console.log(`${log.join(",")} | ${r2.a} ${r2.b} ${r2.c} ${r2.z}`);
log.length = 0;
const r4 = { y: { q: f("q"), p: f("p") }, x: f("x") };
console.log(`${log.join(",")} | ${r4.y.p} ${r4.y.q} ${r4.x}`);
log.length = 0;
interface Counter { name: string; count: number }
const c: Counter = { name: `n${f("name")}`, count: f("count") };
c.count += 1;
console.log(`${log.join(",")} | ${c.name} ${c.count}`);
log.length = 0;
function pair(): { second: number; first: number } { return { second: f("second"), first: f("first") }; }
const p = pair();
console.log(`${log.join(",")} | ${p.first} ${p.second}`);
