// `x == null` / `x != null` (loose comparison against null or undefined): true exactly for null and
// undefined; narrowing in if/else, ternaries, early returns and && chains; the operand runs once.
function lenOr(s?: string | null): number {
  if (s == null) return -1;
  return s.length;
}
function describe(x: number | undefined): string {
  return x == null ? 'none' : x.toFixed(1);
}
function both(v: string | null | undefined): string {
  if (v != null) return `got ${v.toUpperCase()}`;
  return 'nullish';
}
function firstPositive(o: { k: number } | null): boolean {
  return o != null && o.k > 0;
}
let calls = 0;
function tick(): number { calls++; return calls; }
const vals: unknown[] = [0, '', false, NaN, null, undefined, {}, [], 'a'];
console.log(`${lenOr('abc')} ${lenOr(null)} ${lenOr(undefined)} ${lenOr('')}`);
console.log(`${describe(2.25)} ${describe(undefined)} ${describe(0)}`);
console.log(`${both('x')} ${both(null)} ${both(undefined)} ${both('')}`);
console.log(`${firstPositive({ k: 3 })} ${firstPositive({ k: -1 })} ${firstPositive(null)}`);
console.log(vals.map(v => v == null).join(' '));
console.log(vals.map(v => v != undefined).join(' '));
console.log(`${vals.map(v => null == v).join(' ')} | ${vals.map(v => void 0 != v).join(' ')}`);
const n = 5;
console.log(`${n == null} ${n != null} ${tick() == null} ${calls}`);
const m: number | null = calls > 0 ? null : 1;
console.log(`${m == undefined} ${m != undefined}`);
