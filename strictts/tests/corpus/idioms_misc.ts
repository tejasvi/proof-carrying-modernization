// Promise.all with plain values, class toString in templates, switch(true), nested ternaries,
// arrow functions returning object literals.
class Money {
  constructor(private cents: bigint) {}
  toString(): string { return `$${this.cents / 100n}.${`${this.cents % 100n}`.padStart(2, "0")}`; }
  plus(o: Money): Money { return new Money(this.cents + o.cents); }
}
const total = new Money(1999n).plus(new Money(1n));
console.log(`total ${total} / ${String(new Money(5n))}`);
async function main(): Promise<void> {
  const vals = await Promise.all([1n, Promise.resolve(2n), 3n]);
  console.log(`all with plain values: ${vals.join(",")}`);
}
main();
function grade(score: bigint): string {
  switch (true) {
    case score >= 90n: return "A";
    case score >= 80n: return "B";
    default: return score >= 70n ? "C" : score >= 60n ? "D" : "F";
  }
}
console.log([95n, 85n, 75n, 65n, 5n].map(grade).join(""));
const mk = (name: string, n: bigint) => ({ name, n, tag: `${name}#${n}` });
console.log([mk("a", 1n), mk("b", 2n)].map((o) => o.tag).join(" "));
