// Set: add/has/delete, uniqueness, iteration order, forEach, conversion to array.
const s = new Set<string>();
s.add("b").add("a").add("b").add("c");
console.log(`${[...s].join("")} has a: ${s.has("a")} has z: ${s.has("z")}`);
s.delete("a");
console.log([...s.values()].join(""));
const nums = new Set<bigint>([3n, 1n, 3n, 2n, 1n]);
console.log(Array.from(nums).join(" "));
let acc = "";
nums.forEach((v, v2, set) => { acc += `${v}${v === v2}${set === nums} `; });
console.log(acc);
const objs = new Set<bigint[]>();
const arr: bigint[] = [1n];
objs.add(arr); objs.add(arr); objs.add([1n]);
console.log(`identity-based: ${objs.size === 2}`);
