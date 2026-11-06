export class Cart {
  items: number[] = [];
  discount: number;
  constructor(discount: number) {
    this.discount = discount;
  }
  add(price: number): number {
    this.items.push(price);
    let t = 0;
    for (let i = 0; i < this.items.length; i++) {
      t = t + this.items[i];
    }
    return t - this.discount;
  }
}
