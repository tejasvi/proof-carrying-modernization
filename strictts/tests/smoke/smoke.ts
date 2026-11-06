function fact(n: bigint): bigint { return n <= 0n ? 1n : n * fact(n - 1n); }
console.log(String(fact(20n)));
const xs: string[] = ["b", "a", "c"];
xs.push("d");
console.log(xs.join(","));
const m = new Map<string, bigint>();
m.set("x", 1n); m.set("y", 2n); m.set("x", 3n);
for (const t of m) console.log(t[0] + "=" + String(t[1]));
async function f(): Promise<bigint> { console.log("f1"); const a = await Promise.resolve(5n); console.log("f2"); return a + 1n; }
f().then((v: bigint) => { console.log("then " + String(v)); });
console.log("sync end");
