export function greet(name: string, n: number, vip: boolean): string {
  return `Hello ${name}, you have ${n} messages${vip ? " (vip)" : ""}`;
}
