async function step(log: string[], name: string): Promise<void> {
  log.push(name + "1");
  await Promise.resolve();
  log.push(name + "2");
}
export async function run(a: string, b: string): Promise<string> {
  const log: string[] = [];
  const p = step(log, a);
  const q = step(log, b);
  await p;
  await q;
  return log.join(",");
}
