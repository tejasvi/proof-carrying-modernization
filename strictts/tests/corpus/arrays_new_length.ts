// `new Array(n)` / `Array(n)` in a function, filled before any other use (range, at and chunk in
// es-toolkit): the array starts empty and grows by element writes at its end; every other use
// checks that its length reached n. A length that is not an integer in [0, 2^32 - 1] throws
// JavaScript's RangeError. Without a type argument TypeScript types the array any[]; its elements
// then have the type of the values written (rangeRight, tail).
function range(start: number, end: number, step: number): number[] {
  const length = Math.max(Math.ceil((end - start) / step), 0);
  const result = new Array<number>(length);
  for (let i = 0; i < length; i++) {
    result[i] = start + i * step;
  }
  return result;
}
function at(arr: readonly number[], indices: readonly number[]): Array<number | undefined> {
  const result = new Array<number | undefined>(indices.length);
  for (let i = 0; i < indices.length; i++) {
    const index = indices[i];
    result[i] = index < 0 ? arr[arr.length + index] : arr[index];
  }
  return result;
}
function chunk(arr: readonly string[], size: number): string[][] {
  const chunkLength = Math.ceil(arr.length / size);
  const result: string[][] = Array(chunkLength);
  for (let index = 0; index < chunkLength; index++) {
    const start = index * size;
    result[index] = arr.slice(start, start + size);
  }
  return result;
}
function rangeRight(start: number, end: number): number[] {
  const length = Math.max(end - start, 0);
  const result = new Array(length);
  for (let i = 0; i < length; i++) {
    result[i] = end - i - 1;
  }
  return result;
}
function tail(arr: readonly string[]): string[] {
  const len = arr.length;
  if (len <= 1) {
    return [];
  }
  const result = new Array(len - 1);
  for (let i = 1; i < len; i++) {
    result[i - 1] = arr[i];
  }
  return result;
}
function overwrite(n: number): string[] {
  const out = new Array<string>(n);
  for (let i = 0; i < n; i++) out[i] = "x";
  out[0] = "first";
  out[n] = "grown";
  return out;
}
function lengthOf(n: number): string {
  try {
    const a = new Array<number>(n);
    for (let i = 0; i < n; i++) a[i] = i;
    return `${a.length}`;
  } catch (e) {
    return e instanceof RangeError ? `RangeError: ${e.message}` : "other";
  }
}
console.log(range(0, 10, 3).join(","));
console.log(range(5, 0, -2).join(","));
console.log(`${range(0, 0, 1).length}`);
console.log(at([10, 20, 30], [0, -1, 5]).map(x => x ?? "u").join(","));
console.log(chunk(["a", "b", "c", "d", "e"], 2).map(c => c.join("")).join("|"));
console.log(`${rangeRight(2, 6).join(",")} ${tail(["a", "b", "c"]).join("")} ${tail(["a"]).length}`);
console.log(overwrite(3).join(","));
console.log([0, 2, -1, 1.5, NaN, 4294967296, -0].map(n => lengthOf(n)).join(" / "));
