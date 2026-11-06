export function greet(name: string, n: number, vip: boolean): string {
  return "Hello " + name + ", you have " + String(n) + " messages" + (vip ? " (vip)" : "");
}
