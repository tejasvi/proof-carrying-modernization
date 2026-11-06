// An async function: its promise is fulfilled with 2n once the microtask queue has run.
export async function double(n: bigint): Promise<bigint> {
  const a = await Promise.resolve(n);
  return a * 2n;
}

double(21n).then((v) => {
  console.log(String(v));
});
