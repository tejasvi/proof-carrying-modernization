export function countDown(n: number): string {
  let out = "";
  let i = Math.min(Math.floor(n), 50);
  while (i > 0) {
    out = out + String(i) + " ";
    i = i - 1;
  }
  return out;
}
