// Interfaces as immutable records; width subtyping (projection); optional fields.
interface Point { x: bigint; y: bigint }
interface Named { name: string }
interface City { name: string; pos: Point; population?: bigint }
function show(p: Point): string { return `(${p.x}, ${p.y})`; }
function label(n: Named): string { return `<${n.name}>`; }
const paris: City = { name: "Paris", pos: { x: 2n, y: 48n }, population: 2100000n };
const nowhere: City = { pos: { y: 0n, x: 0n }, name: "Nowhere" };
console.log(`${label(paris)} at ${show(paris.pos)} pop ${paris.population ?? 0n}`);
console.log(`${label(nowhere)} at ${show(nowhere.pos)} pop ${nowhere.population ?? 0n}`);
const p3 = { x: 1n, y: 2n, z: 3n };
console.log(show(p3));
function move(p: Point, dx: bigint): Point { return { ...p, x: p.x + dx }; }
console.log(show(move(paris.pos, 10n)));
const cities: City[] = [paris, nowhere];
console.log(cities.map(c => c.name).join("+"));
