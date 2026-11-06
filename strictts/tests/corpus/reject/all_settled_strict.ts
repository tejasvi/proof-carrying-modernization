// @strict
// @reject any-type
// Promise.allSettled in the original subset: the reason of a rejected result is typed `any`,
// which has no type there.
async function counts(): Promise<void> {
  const rs = await Promise.allSettled([Promise.resolve(1), Promise.reject<number>(new Error("x"))]);
  console.log(`${rs.length}`);
}
counts();
