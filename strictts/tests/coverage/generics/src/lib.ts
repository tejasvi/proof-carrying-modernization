// Generic functions without call sites in the project: `--emit-generics number` emits each at
// one instance (unconstrained := number, `extends string` := string, `extends number` := number);
// the last one has another constraint and is left out with that reason.
export function chunkBy<T>(xs: T[], n: number): T[][] {
  const out: T[][] = [];
  for (let i = 0; i < xs.length; i += n) out.push(xs.slice(i, i + n));
  return out;
}
export const firstOr = <T>(xs: T[], d: T): T => (xs.length > 0 ? xs[0] : d);
export function longest<S extends string>(xs: S[]): S | undefined {
  let best: S | undefined;
  for (const x of xs) if (best === undefined || x.length > best.length) best = x;
  return best;
}
export function clampAll<N extends number>(xs: N[], hi: N): number[] { return xs.map((x) => Math.min(x, hi)); }
export function sizeOf<T extends { length: number }>(x: T): number { return x.length; }
