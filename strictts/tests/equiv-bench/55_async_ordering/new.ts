async function step(log: string[], name: string): Promise<void> {
  log.push(name + "1");
  await Promise.resolve();
  log.push(name + "2");
}
export async function run(a: string, b: string): Promise<string> {
  const log: string[] = [];
  await step(log, a);
  await step(log, b);
  return log.join(",");
}
