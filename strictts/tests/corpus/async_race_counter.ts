// A lost update: two concurrent calls of an async increment that reads the counter before an
// `await` and writes it after. Under the JavaScript job semantics the outcome is
// deterministic: both calls read 0, so the counter ends at 1. Reading after the `await`
// (or not awaiting between the read and the write) gives 2.
export class Counter {
  n = 0;
}

export async function incRacy(c: Counter): Promise<void> {
  const v = c.n;
  await Promise.resolve();
  c.n = v + 1;
}

export async function incFixed(c: Counter): Promise<void> {
  await Promise.resolve();
  c.n = c.n + 1;
}

export async function runRacy(c: Counter): Promise<void> {
  await Promise.all([incRacy(c), incRacy(c)]);
}

export async function runFixed(c: Counter): Promise<void> {
  await Promise.all([incFixed(c), incFixed(c)]);
}

const racy = new Counter();
const fixed = new Counter();
runRacy(racy).then(() => console.log(`racy: ${racy.n}`));
runFixed(fixed).then(() => console.log(`fixed: ${fixed.n}`));
