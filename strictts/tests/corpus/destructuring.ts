// Destructuring in declarations, parameters and for-of; defaults and rest.
interface Opts { width: bigint; height?: bigint; title: string }
function area({ width, height = 10n }: Opts): bigint { return width * height; }
console.log(`${area({ width: 3n, title: "a" })} ${area({ width: 3n, height: 2n, title: "b" })}`);
const { title, ...dims } = { title: "box", width: 4n, height: 5n };
console.log(`${title} ${dims.width}x${dims.height}`);
const [first, second, ...others] = ["a", "b", "c", "d"];
console.log(`${first} ${second} [${others.join(",")}]`);
const points: { x: bigint; y: bigint }[] = [{ x: 1n, y: 2n }, { x: 3n, y: 4n }];
for (const { x, y } of points) console.log(`x=${x} y=${y}`);
function sumPair([a, b]: [bigint, bigint]): bigint { return a + b; }
console.log(`${sumPair([20n, 22n])}`);
const nested = { inner: { val: "deep" }, list: ["p", "q"] };
const { inner: { val }, list: [p0] } = nested;
console.log(`${val} ${p0}`);
let x = "1", y = "2";
[x, y] = [y, x];
console.log(`${x} ${y}`);
