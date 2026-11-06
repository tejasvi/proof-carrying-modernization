// Multi-file program: imports across modules (whole-program translation).
import { next, label, total, Item } from "./util";
import { Square } from "./shapes";
console.log("main module body runs");
console.log(`${next()} ${next()} ${label("x")}`);
const items: Item[] = [{ name: "a", qty: 2n }, { name: "b", qty: 5n }];
console.log(`total ${total(items)}`);
const sq = new Square(4n);
console.log(`${sq.describe()} area ${sq.area()}`);
