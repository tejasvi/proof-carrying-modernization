export class Cart {
  items: number[] = [];
  discount: number;
  constructor(discount: number) {
    this.discount = discount;
  }
  add(price: number): number {
    this.items.push(price);
    let t = 0;
    for (const p of this.items) t += p;
    return t - this.discount;
  }
}
