// @reject no-prototype
class A { m(): string { return "m"; } }
console.log(String(A.prototype === undefined));
