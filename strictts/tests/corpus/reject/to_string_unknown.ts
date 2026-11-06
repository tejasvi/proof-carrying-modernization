// @reject unsupported-conversion
// an instance of a class with its own toString cannot become an unknown value (String(x) of
// unknown values assumes Object.prototype.toString for objects)
class Money { constructor(public c: number) {} toString(): string { return `$${this.c}`; } }
const u: unknown = new Money(5);
console.log(String(u));
