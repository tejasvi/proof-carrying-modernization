export function anyNegative(xs: number[]): boolean {
  for (const x of xs) {
    if (x < 0) return true;
  }
  return false;
}

export function anyNegativeSome(xs: number[]): boolean {
  return xs.some((x) => x < 0);
}

export function allShort(words: string[], max: number): boolean {
  for (const w of words) {
    if (!(w.length <= max)) return false;
  }
  return true;
}

export function allShortEvery(words: string[], max: number): boolean {
  return words.every((w) => w.length <= max);
}

export function firstBig(xs: number[]): number | undefined {
  for (const x of xs) {
    if (x > 100) return x;
  }
  return undefined;
}

export function firstBigFind(xs: number[]): number | undefined {
  return xs.find((x) => x > 100);
}

export function indexOfLong(words: string[], n: number): number {
  for (let i = 0; i < words.length; i++) {
    if (words[i].length > n) return i;
  }
  return -1;
}

export function indexOfLongFind(words: string[], n: number): number {
  return words.findIndex((w) => w.length > n);
}

export function sumUntilNegative(xs: number[]): number {
  let s = 0;
  for (const x of xs) {
    if (x < 0) return s;
    s += x;
  }
  return -1;
}

console.log(`${anyNegative([1, -2])} ${allShort(["ab", "abc"], 2)} ${firstBig([5, 200, 300])} ${indexOfLong(["a", "abc"], 2)} ${sumUntilNegative([1, 2, -1, 4])}`);
