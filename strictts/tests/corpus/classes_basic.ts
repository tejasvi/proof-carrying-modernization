// Classes: fields with initialisers, parameter properties, methods, getters/setters, this.
class Account {
  balance = 0n;
  private history: string[] = [];
  readonly id: string;
  constructor(public owner: string, initial: bigint) {
    this.id = `acct-${owner}`;
    this.deposit(initial);
  }
  deposit(amount: bigint): void {
    this.balance += amount;
    this.history.push(`+${amount}`);
  }
  withdraw(amount: bigint): boolean {
    if (amount > this.balance) {
      this.history.push(`!${amount}`);
      return false;
    }
    this.balance -= amount;
    this.history.push(`-${amount}`);
    return true;
  }
  get summary(): string { return `${this.id} ${this.owner}: ${this.balance} [${this.history.join(" ")}]`; }
  set nickname(n: string) { this.owner = n; }
}
const a = new Account("ann", 50n);
a.deposit(25n);
console.log(`${a.withdraw(100n)} ${a.withdraw(30n)}`);
console.log(a.summary);
a.nickname = "annie";
console.log(a.summary);
const b = new Account("bob", 0n);
const accts = [a, b];
for (const x of accts) x.deposit(1n);
console.log(`${a.balance} ${b.balance} same=${accts[0] === a}`);
