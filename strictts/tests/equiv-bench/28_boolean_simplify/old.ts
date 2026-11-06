export function inRange(x: number, lo: number, hi: number): boolean {
  if (x >= lo && x <= hi) {
    return true;
  } else {
    return false;
  }
}
