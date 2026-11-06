export function price(qty: number, unit: number, taxRate: number): number {
  const net = qty * unit;
  const gross = net * (1 + taxRate);
  return net > 100 ? gross - 5 : gross;
}
