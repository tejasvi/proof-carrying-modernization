export type Op = "add" | "sub" | "mul" | "div";
export function apply(op: Op, a: number, b: number): number {
  if (op === "add") return a + b;
  if (op === "sub") return a - b;
  if (op === "mul") return a * b;
  return a / b;
}
