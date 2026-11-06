// Functions that read module-level constants: a number, a string, a Set and an array. Their
// statements assume the initialised module world (`World.ModuleInit`); `ts_auto` computes the
// constants' cells by running the module body symbolically.

const LIMIT = 3;
const PREFIX = "user:";
const NAMES = new Set(["ann", "bob"]);
const WEIGHTS = [1, 2, 3];

export function clampToLimit(x: number): number {
  return x > LIMIT ? LIMIT : x;
}

export function userKey(id: string): string {
  return PREFIX + id;
}

export function isKnown(name: string): boolean {
  return NAMES.has(name);
}

export function countAboveLimit(xs: number[]): number {
  let n = 0;
  for (const x of xs) {
    if (x > LIMIT) {
      n++;
    }
  }
  return n;
}

export function weightedSum(): number {
  let s = 0;
  for (const w of WEIGHTS) {
    s += w;
  }
  return s;
}

export function checkedLimit(x: number): number {
  if (x > LIMIT) {
    throw new RangeError("over the limit");
  }
  return LIMIT - x;
}
