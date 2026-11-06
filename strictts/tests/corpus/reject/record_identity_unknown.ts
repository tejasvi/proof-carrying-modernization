// @reject record-identity
// P is compared by identity; an unknown value held in a variable may be cast more than once,
// and each cast would make another object (Node prints true)
interface P { x: number }
const raw: unknown = JSON.parse('{"x":1}');
const a = raw as P;
const b = raw as P;
console.log(`${a === b}`);
