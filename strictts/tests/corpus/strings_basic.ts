// String concatenation, comparison, templates with bigint/boolean holes, iteration.
const a = "foo";
const b = "bar";
const c = a + b;
console.log(c);
console.log(`${a < b} ${a > b} ${a === "foo"} ${c !== "foobar"}`);
let acc = "";
for (const ch of "héllo😀!") acc = `[${ch}]` + acc;
console.log(acc);
const parts: string[] = [];
for (const word of ["x", "y", "z"]) parts.push(word + word);
console.log(parts.join("-"));
const big = 12345678901234567890n;
console.log(`big=${big} neg=${-big} bool=${big > 0n}`);
console.log(String(true) + String(99n) + String("s"));
const multi = `line1
line2`;
console.log(multi);
console.log(`nested ${`inner ${a}`} end`);
