// Async ordering corner cases: throw before the first await, await of then-chains,
// nested async calls without await, finally ordering with await inside.
async function throwsEarly(): Promise<string> {
  throw new Error("early");
}
async function awaitsChain(): Promise<string> {
  const v = await Promise.resolve("x").then((s) => s + "y").then((s) => s + "z");
  return v;
}
async function withFinally(): Promise<string> {
  try {
    await null;
    return "from try";
  } finally {
    console.log("finally before resolution");
    await null;
    console.log("finally after await");
  }
}
async function fireAndForget(): Promise<void> {
  console.log("ff start");
  await null;
  console.log("ff after await");
}
console.log("start");
const p = throwsEarly();
console.log("after calling throwsEarly (no synchronous exception)");
p.catch((e) => { console.log(`caught ${e.message}`); return ""; });
awaitsChain().then((v) => console.log(`chain ${v}`));
withFinally().then((v) => console.log(`withFinally ${v}`));
fireAndForget();
console.log("end of sync");
