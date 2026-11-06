export function sumDown(xs: number[]): number {
  let s = 0;
  for (let i = xs.length - 1; i >= 0; i--) {
    s += xs[i];
  }
  return s;
}

export function sumUpTo(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length - 1; i++) {
    s += xs[i + 1] - xs[i];
  }
  return s;
}

export function isSorted(arr: number[]): boolean {
  for (let i = 0; i < arr.length - 1; i++) {
    if (arr[i] >= arr[i + 1]) {
      return false;
    }
  }
  return true;
}

export function sumLe(): number {
  let s = 0;
  for (let i = 0; i <= 10; i++) {
    s += i;
  }
  return s;
}

export function sumLeLast(xs: number[]): number {
  let s = 0;
  for (let i = 1; i <= xs.length - 1; i++) {
    s += xs[i];
  }
  return s;
}

export function sumDown10(): number {
  let s = 0;
  for (let i = 10; i > 0; i--) {
    s += i;
  }
  return s;
}

export function lastNeg(xs: number[]): number {
  for (let i = xs.length - 1; i >= 0; i--) {
    if (xs[i] < 0) {
      return i;
    }
  }
  return -1;
}

export function dropRightPos(xs: number[]): number[] {
  for (let i = xs.length - 1; i >= 0; i--) {
    if (!(xs[i] > 0)) {
      return xs.slice(0, i + 1);
    }
  }
  return [];
}

export function countWhile(): number {
  let c = 0;
  let i = 0;
  while (i < 10) {
    c += 2;
    i++;
  }
  return c;
}

export function sumWhile(xs: number[]): number {
  let s = 0;
  let i = 0;
  while (i < xs.length) {
    s += xs[i];
    i = i + 1;
  }
  return s;
}

export function sumWhileDown(xs: number[]): number {
  let s = 0;
  let i = xs.length - 1;
  while (i >= 0) {
    s += xs[i];
    i--;
  }
  return s;
}

export function countDown5(): string {
  let out = "";
  let i = 5;
  while (i > 0) {
    out = out + String(i) + " ";
    i = i - 1;
  }
  return out;
}

export function countDownMin(n: number): string {
  let out = "";
  for (let i = Math.min(Math.floor(n), 50); i > 0; i--) {
    out += `${i} `;
  }
  return out;
}

console.log(`${sumDown([1, 2, 3])} ${sumUpTo([1, 4, 9])} ${isSorted([1, 2, 3])} ${sumLe()} ${sumLeLast([5, 6, 7])} ${sumDown10()} ${lastNeg([1, -2, 3])} ${dropRightPos([-1, 2, 3]).length} ${countWhile()} ${sumWhile([1, 2])} ${sumWhileDown([1, 2])} ${countDown5()} ${countDownMin(3.5)}`);
