// @reject no-this
// the methods of an Iterator record are called through its fields without a receiver, so a method
// that uses `this` is rejected (Node prints 1: there `this` is the iterator)
const it: Iterator<number> = { next() { return { value: this === undefined ? 0 : 1, done: false }; } };
const r = it.next();
console.log(r.done ? "done" : String(r.value));
