export function withdraw(balance: number, amount: number): number {
  if (amount > 0) {
    if (amount <= balance) {
      return balance - amount;
    } else {
      throw new RangeError("insufficient funds");
    }
  } else {
    throw new RangeError("amount must be positive");
  }
}
