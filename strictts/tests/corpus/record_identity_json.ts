// @extern
// Objects compared by identity given to external code (JSON.stringify): the external function
// receives their values, also inside arrays and other objects; the result of an external call
// cast to such a type (JSON.parse) is a new object.
interface P { x: number; tag: string }
const p: P = { x: 1, tag: "a" };
const q: P = { x: 1, tag: "a" };
const ps: P[] = [p, q, p];
const maybe: P | undefined = ps.find((e) => e.x === 1);
console.log(`${ps.indexOf(q)} ${JSON.stringify(p)} ${JSON.stringify(ps)}`);
console.log(`${JSON.stringify({ first: p, n: ps.length })} ${JSON.stringify(maybe)} ${maybe === p}`);
const parsed = JSON.parse(JSON.stringify(p)) as P;
const again = parsed;
console.log(`${parsed === p} ${again === parsed} ${ps.includes(parsed)} ${parsed.x}${parsed.tag}`);
