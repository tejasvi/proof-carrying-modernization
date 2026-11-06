export function canShip(inStock: boolean, blocked: boolean, weight: number): boolean {
  return !(!inStock || blocked || weight > 30);
}
