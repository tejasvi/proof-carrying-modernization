// @numbers
// Common async idioms: sleep via setTimeout, sequential vs concurrent awaits, retry loops.
function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}
async function job(name: string, ms: number): Promise<string> {
  console.log(`${name} start`);
  await sleep(ms);
  console.log(`${name} end`);
  return name.toUpperCase();
}
async function main(): Promise<void> {
  const a = await job("seq1", 200);
  const b = await job("seq2", 100);
  console.log(`sequential: ${a} ${b}`);
  const results = await Promise.all([job("par1", 300), job("par2", 100), job("par3", 200)]);
  console.log(`concurrent: ${results.join(" ")}`);
  let attempts = 0;
  async function flaky(): Promise<string> {
    attempts++;
    await sleep(5);
    if (attempts < 3) throw new Error(`attempt ${attempts} failed`);
    return `ok after ${attempts}`;
  }
  for (;;) {
    try {
      console.log(await flaky());
      break;
    } catch (e) {
      console.log((e as Error).message);
    }
  }
}
main().then(() => console.log("all done"));
