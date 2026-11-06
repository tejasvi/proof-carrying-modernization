import { sumTo } from './util';
export class Counter {
  private n = 0;
  add(k: number): number { this.n += k; return this.n; }
  total(): number { return sumTo(this.n); }
}
export function countWords(s: string): Record<string, number> {
  const out: Record<string, number> = {};
  for (const w of s.split(" ")) out[w] = (out[w] ?? 0) + 1;
  return out;
}
