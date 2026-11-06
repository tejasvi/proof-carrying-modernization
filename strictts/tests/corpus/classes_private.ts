// @numbers
// Classes with #private fields, getters, static counters and method chaining.
class Vec {
  #x: number;
  #y: number;
  static created = 0;
  constructor(x: number, y: number) { this.#x = x; this.#y = y; Vec.created++; }
  get x(): number { return this.#x; }
  get y(): number { return this.#y; }
  add(o: Vec): Vec { return new Vec(this.#x + o.x, this.#y + o.y); }
  scale(k: number): Vec { this.#x *= k; this.#y *= k; return this; }
  toString(): string { return `(${this.#x}, ${this.#y})`; }
  get length(): number { return Math.sqrt(this.#x * this.#x + this.#y * this.#y); }
}
const v = new Vec(1, 2).add(new Vec(2, 2));
console.log(`${v.toString()} len=${v.length}`);
console.log(v.scale(2).scale(0.5).toString());
console.log(`created ${Vec.created}`);
