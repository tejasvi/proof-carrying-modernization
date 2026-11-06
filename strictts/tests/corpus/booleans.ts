// Boolean logic and short-circuit evaluation order.
const log: string[] = [];
function t(name: string): boolean { log.push(name); return true; }
function f(name: string): boolean { log.push(name); return false; }
const r1 = f("a") && t("b");
const r2 = t("c") || f("d");
const r3 = f("e") || (t("f") && f("g"));
const r4 = !(t("h") && t("i"));
console.log(`${r1} ${r2} ${r3} ${r4} [${log.join("")}]`);
const flags = [true, false, true];
console.log(`${flags.every((b) => b)} ${flags.some((b) => b)} ${flags.filter((b) => !b).length === 1}`);
let n = 0n;
const bump = (): boolean => { n++; return n > 2n; };
while (!bump()) { /* spin */ }
console.log(`n=${n}`);
const yes = log.length === 7, no = !yes;
console.log(`${yes === true} ${no !== true} ${String(yes && no)}`);
