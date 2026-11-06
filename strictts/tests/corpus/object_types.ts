// `object` values are unknown values (any non-primitive value with its runtime type); `{}` is
// the record without fields (e.g. the default of an optional spread).
function kind(o: object): string { return Array.isArray(o) ? "array" : o instanceof Error ? "error" : typeof o; }
console.log([kind([1]), kind({ a: 1 }), kind(new Error("e")), kind(new Map<string, number>()), kind(() => 1)].join(","));
function hasK(o: object): string { return "k" in o ? "has k" : "no k"; }
console.log(`${hasK({ k: 1 })} ${hasK({ j: 2 })} ${String({ k: 1 } as object)}`);
function withOpts(o: { a?: number } | undefined): { a?: number; b: number } { return { b: 2, ...(o ?? {}) }; }
const w1 = withOpts({ a: 5 });
const w2 = withOpts(undefined);
console.log(`${w1.a ?? "-"} ${w1.b} ${w2.a ?? "-"} ${w2.b}`);
const empty: {} = {};
console.log(`${typeof empty} ${JSON_KEYS(empty)}`);
function JSON_KEYS(_: {}): number { return 0; }
