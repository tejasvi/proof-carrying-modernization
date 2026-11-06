// @reject no-extends
class A { x = 1n; }
class B extends A { y = 2n; }
console.log(`${new B().y}`);
