// A module imported by main.ts; its top-level code runs first.
export const PREFIX = "util";
console.log("util module body runs");
let counter = 0n;
export function next(): bigint { counter += 1n; return counter; }
export function label(s: string): string { return `${PREFIX}:${s}`; }
export interface Item { name: string; qty: bigint }
export function total(items: Item[]): bigint { return items.reduce((a, it) => a + it.qty, 0n); }
