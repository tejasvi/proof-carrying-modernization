// A generic class used at two instantiations (monomorphised).
class Stack<T> {
  private items: T[] = [];
  push(x: T): void { this.items.push(x); }
  pop(): T | undefined { return this.items.pop(); }
  peek(): T | undefined { return this.items.at(-1); }
  isEmpty(): boolean { return this.items.length === 0; }
}
const s = new Stack<string>();
s.push("a"); s.push("b"); s.push("c");
const top = s.pop();
console.log(`popped ${top ?? "none"}`);
const n = new Stack<bigint>();
n.push(1n); n.push(2n);
let sum = 0n;
let v = n.pop();
while (v !== undefined) { sum += v; v = n.pop(); }
console.log(`sum ${sum} empty=${n.isEmpty()}`);
console.log(`peek ${s.peek() ?? "none"}`);
