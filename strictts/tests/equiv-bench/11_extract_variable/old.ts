export function price(qty: number, unit: number, taxRate: number): number {
  if (qty * unit > 100) {
    return qty * unit * (1 + taxRate) - 5;
  }
  return qty * unit * (1 + taxRate);
}
