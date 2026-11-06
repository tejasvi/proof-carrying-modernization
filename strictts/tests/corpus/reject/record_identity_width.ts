// @reject record-identity
// P is compared by identity (indexOf), so its values are objects; q, an object of a wider type,
// would become a second object for each conversion (Node prints 0)
interface P { x: bigint }
interface Q { x: bigint; y: bigint }
const q: Q = { x: 1n, y: 2n };
const ps: P[] = [q];
console.log(`${ps.indexOf(q)}`);
