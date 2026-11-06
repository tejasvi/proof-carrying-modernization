// new Promise: resolve/reject functions, only the first settlement counts, executor errors.
const p = new Promise<string>((resolve, reject) => {
  console.log("executor runs synchronously");
  resolve("first");
  resolve("second");
  reject(new Error("ignored"));
});
p.then((v) => console.log(`resolved with ${v}`));
const q = new Promise<bigint>((_resolve, reject) => { reject(new RangeError("nope")); });
q.catch((e) => { console.log(`rejected: ${e.name} ${e.message}`); return 0n; });
const r = new Promise<string>(() => { throw new Error("executor threw"); });
r.catch((e) => { console.log(`caught: ${e.message}`); return ""; });
const resolvers: ((v: string) => void)[] = [];
const later = new Promise<string>((res) => { resolvers.push(res); });
later.then((v) => console.log(`later ${v}`));
console.log("before resolveLater");
for (const res of resolvers) res("now");
console.log("sync end");
