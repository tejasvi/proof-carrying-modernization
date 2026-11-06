// await inside loops, conditions and nested blocks.
async function count(n: bigint): Promise<bigint> { await null; return n; }
async function main(): Promise<void> {
  let total = 0n;
  for (let i = 0n; i < 3n; i++) total += await count(i);
  console.log(`for total ${total}`);
  let j = 0n;
  while ((await count(j)) < 3n) j++;
  console.log(`while j ${j}`);
  for (const x of ["a", "b"]) {
    if ((await count(1n)) === 1n) console.log(`for-of ${x}`);
  }
  let k = 5n;
  do { k = await count(k - 2n); } while (k > 0n);
  console.log(`do k ${k}`);
  const arr = [await count(1n), await count(2n)];
  console.log(`arr ${arr.join(",")}`);
  const cond = (await count(0n)) === 0n ? await count(10n) : await count(20n);
  console.log(`cond ${cond}`);
}
main();
console.log("sync after main()");
