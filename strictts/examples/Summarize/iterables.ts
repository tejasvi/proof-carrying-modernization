// for…of loops over strings (code points), Maps (entries) and Sets (elements).
export function sumValues(m: Map<string, number>): number {
  let total = 0;
  for (const [k, v] of m) {
    total = total + v;
  }
  return total;
}

export function countPositiveIn(s: Set<number>): number {
  let n = 0;
  for (const x of s) {
    if (x > 0) {
      n = n + 1;
    }
  }
  return n;
}

export function countA(str: string): number {
  let n = 0;
  for (const ch of str) {
    if (ch === "a") {
      n = n + 1;
    }
  }
  return n;
}

export function keysOf(m: Map<string, number>): string[] {
  const out: string[] = [];
  for (const [k, v] of m) {
    out.push(k);
  }
  return out;
}

export function splitSigns(xs: number[]): number {
  const pos: number[] = [];
  const neg: number[] = [];
  for (const x of xs) {
    if (x > 0) {
      pos.push(x);
    } else {
      neg.push(x);
    }
  }
  return pos.length - neg.length;
}

export function pushBoth(xs: number[]): number {
  const a: number[] = [];
  const b: number[] = [];
  for (const x of xs) {
    a.push(x);
    b.push(x + 1);
  }
  return a.length + b.length;
}

export function pushBothCount(xs: number[]): number {
  const a: number[] = [];
  const b: number[] = [];
  let n = 0;
  for (const x of xs) {
    a.push(x);
    b.push(x + 1);
    n = n + 1;
  }
  return a.length + b.length + n;
}

const m0 = new Map<string, number>([["x", 1], ["y", 2]]);
console.log(`${sumValues(m0)} ${countPositiveIn(new Set([1, -2, 3]))} ${countA("banana")} ${keysOf(m0).length}`);
console.log(`${splitSigns([1, -2, 3])}`);
console.log(`${pushBoth([1, 2])}`);
console.log(`${pushBothCount([1, 2])}`);
