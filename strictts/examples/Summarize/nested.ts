export function sumProducts(xs: number[], ys: number[]): number {
  let s = 0;
  for (const x of xs) {
    for (const y of ys) {
      s += x * y;
    }
  }
  return s;
}

export function countLess(xs: number[]): number {
  let c = 0;
  for (let i = 0; i < xs.length; i++) {
    for (let j = 0; j < xs.length; j++) {
      if (xs[i] < xs[j]) c++;
    }
  }
  return c;
}

export function uniqVals(arr: number[]): number[] {
  const result: number[] = [];
  for (let i = 0; i < arr.length; i++) {
    const item = arr[i];
    const isUniq = result.every(v => v !== item);
    if (isUniq) {
      result.push(item);
    }
  }
  return result;
}

export function diffWith(xs: number[], ys: number[]): number[] {
  return xs.filter(x => ys.every(y => x !== y));
}

function isBig(x: number): boolean {
  return x > 100;
}

export function anyBig(xs: number[]): boolean {
  return xs.some(x => isBig(x));
}

function sumTo(n: number): number {
  let s = 0;
  for (let i = 0; i < 10; i++) {
    s += i * n;
  }
  return s;
}

export function sumSums(xs: number[]): number {
  let s = 0;
  for (const x of xs) {
    s += sumTo(x);
  }
  return s;
}

export function doubleInPlace(arr: number[]): number[] {
  for (let i = 0; i < arr.length; i++) {
    arr[i] = arr[i] * 2;
  }
  return arr;
}

export function addLen(xs: number[], ys: number[]): number[] {
  return xs.map(x => x + ys.length);
}

console.log(`${sumProducts([1, 2], [3, 4])} ${countLess([3, 1, 2])} ${uniqVals([1, 1, 2]).length} ${diffWith([1, 2, 3], [2]).length} ${anyBig([1, 200])} ${sumSums([1, 2])} ${doubleInPlace([1, 2]).length} ${addLen([1], [2]).length}`);
