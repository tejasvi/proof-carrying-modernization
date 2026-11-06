export function mapEvery(m: Map<number, number>): boolean {
  for (const [k, v] of m) {
    if (!(v > 0)) {
      return false;
    }
  }
  return true;
}

export function mapFindKey(m: Map<number, number>): number | undefined {
  let result: number | undefined = undefined;
  for (const [k, v] of m) {
    if (v > 10) {
      result = k;
      break;
    }
  }
  return result;
}

export function setSome(s: Set<number>): boolean {
  for (const x of s) {
    if (x < 0) {
      return true;
    }
  }
  return false;
}

export function setFind(s: Set<number>): number | undefined {
  for (const x of s) {
    if (x > 100) {
      return x;
    }
  }
  return undefined;
}

export function strHasSpace(s: string): boolean {
  for (const ch of s) {
    if (ch === " ") {
      return true;
    }
  }
  return false;
}

export function strWordLen(s: string): number {
  let n = 0;
  for (const ch of s) {
    if (ch === " ") {
      break;
    }
    n++;
  }
  return n;
}

const m = new Map<number, number>([[1, 5], [2, 20]]);
console.log(`${mapEvery(m)} ${mapFindKey(m)} ${setSome(new Set([1, -2]))} ${setFind(new Set([5, 200]))} ${strHasSpace("a b")} ${strWordLen("ab cd")}`);
