// then chains, then returning promises (thenP), catch and finally ordering.
const p1 = Promise.resolve(1n);
p1.then((x) => { console.log(`p1 then ${x}`); return x + 1n; })
  .then((y) => { console.log(`p1 then2 ${y}`); return Promise.resolve(y * 10n); })
  .then((z) => console.log(`p1 then3 ${z}`));
const p2 = Promise.resolve("two");
p2.then((s) => console.log(`p2 then ${s}`));
const p3: Promise<string> = Promise.reject(new Error("bad"));
p3.catch((e) => { console.log(`p3 catch ${e.message}`); return "recovered"; })
  .then((s) => console.log(`p3 then ${s}`))
  .finally(() => console.log("p3 finally"));
Promise.resolve(5n).finally(() => console.log("finally on fulfilled")).then((v) => console.log(`value kept ${v}`));
console.log("sync done");
