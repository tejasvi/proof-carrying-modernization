// Rejections: try/catch around await, async throws, catch handlers, finally.
async function mayFail(fail: boolean): Promise<string> {
  await null;
  if (fail) throw new TypeError("failed");
  return "fine";
}
async function main(): Promise<void> {
  try {
    console.log(await mayFail(false));
    console.log(await mayFail(true));
    console.log("not reached");
  } catch (e) {
    if (e instanceof TypeError) console.log(`caught ${e.name}: ${e.message}`);
  } finally {
    console.log("finally");
  }
  const r = await mayFail(true).catch((e) => `handled ${e.message}`);
  console.log(r);
}
main().then(() => console.log("done"));
