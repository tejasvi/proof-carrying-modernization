// A class whose invariant (balance >= 0) every method must preserve, including when it throws.
export class Account {
  private balance: bigint;

  constructor(initial: bigint) {
    if (initial < 0n) {
      throw new RangeError("negative initial balance");
    }
    this.balance = initial;
  }

  deposit(amount: bigint): void {
    if (amount <= 0n) {
      throw new RangeError("deposit must be positive");
    }
    this.balance = this.balance + amount;
  }

  withdraw(amount: bigint): void {
    if (amount <= 0n) {
      throw new RangeError("withdrawal must be positive");
    }
    if (amount > this.balance) {
      throw new Error("insufficient funds");
    }
    this.balance = this.balance - amount;
  }

  getBalance(): bigint {
    return this.balance;
  }
}

const acct = new Account(100n);
acct.deposit(50n);
try {
  acct.withdraw(500n);
} catch (e) {
  console.log("rejected");
}
acct.withdraw(30n);
console.log(String(acct.getBalance()));
