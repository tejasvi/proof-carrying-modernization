// @numbers
// SameValueZero keys: NaN and -0 in Map/Set; object identity keys; array includes vs indexOf.
const m = new Map<number, string>();
m.set(NaN, "nan");
m.set(-0, "zero");
console.log(`${m.get(NaN) ?? "?"} ${m.get(0) ?? "?"} ${m.has(+0)} ${m.size}`);
for (const k of m.keys()) console.log(`key ${k} ${1 / k}`);
const s = new Set<number>([NaN, NaN, 0, -0]);
console.log(`set size ${s.size}`);
const xs = [NaN, 1];
console.log(`${xs.includes(NaN)} ${xs.indexOf(NaN)}`);
class K { constructor(public id: string) {} }
const k1 = new K("a"), k2 = new K("a");
const byObj = new Map<K, number>([[k1, 1]]);
console.log(`${byObj.get(k1) ?? -1} ${byObj.get(k2) ?? -1}`);
