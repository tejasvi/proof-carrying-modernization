// Higher-order array methods with bigint data.
const nums: bigint[] = [5n, 3n, 8n, 1n, 9n, 2n];
const doubled = nums.map((n) => n * 2n);
const evens = nums.filter((n) => n % 2n === 0n);
const total = nums.reduce((a, b) => a + b, 0n);
const maxv = nums.reduce((a, b) => (a > b ? a : b));
console.log(`doubled ${doubled.join(",")} evens ${evens.join(",")} total ${total} max ${maxv}`);
console.log(`some>8 ${nums.some((n) => n > 8n)} every>0 ${nums.every((n) => n > 0n)}`);
const found = nums.find((n) => n > 5n);
console.log(`find ${found ?? -1n} findLast ${nums.findLast((n) => n < 3n) ?? -1n}`);
const idx = nums.findIndex((n) => n === 8n);
console.log(`findIndex is 2: ${idx === 2}`);
let log = "";
nums.forEach((n, i) => { log += `${n}${i === 0 ? "@0" : ""} `; });
console.log(log);
const words = ["apple", "kiwi", "fig"];
console.log(words.map((w, i, arr) => `${w}/${arr === words}`).join(" "));
console.log(words.flatMap((w) => [w, w]).join(","));
const right = ["a", "b", "c"].reduceRight((acc, s) => acc + s, ">");
console.log(right);
function isShort(s: string, _i?: number): boolean { return s === "fig" || s === "kiwi"; }
console.log(words.filter(isShort).join(" "));
