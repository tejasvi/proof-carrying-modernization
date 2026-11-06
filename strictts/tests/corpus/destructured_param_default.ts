// A destructured parameter with a default value: the default where the argument is undefined,
// then the pattern with its own defaults (es-toolkit's windowed).
function windowed(arr: readonly number[], size: number, { partialWindows = false }: { partialWindows?: boolean } = {}): number[][] {
  const result: number[][] = [];
  for (let i = 0; i < arr.length; i += 1) {
    const w = arr.slice(i, i + size);
    if (w.length === size || (partialWindows && w.length > 0)) {
      result.push(w);
    }
  }
  return result;
}
function show(xs: number[][]): string {
  return xs.map(w => w.join("")).join(" ");
}
console.log(show(windowed([1, 2, 3, 4], 3)));
console.log(show(windowed([1, 2, 3, 4], 3, {})));
console.log(show(windowed([1, 2, 3, 4], 3, { partialWindows: true })));
console.log(show(windowed([1, 2, 3, 4], 3, undefined)));
function point({ x, y = 10 }: { x: number; y?: number } = { x: 1 }): string {
  return `${x},${y}`;
}
console.log(`${point()} ${point({ x: 5 })} ${point({ x: 5, y: 6 })}`);
