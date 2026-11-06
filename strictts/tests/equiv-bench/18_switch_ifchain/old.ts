export type Op = "add" | "sub" | "mul" | "div";
export function apply(op: Op, a: number, b: number): number {
  switch (op) {
    case "add": return a + b;
    case "sub": return a - b;
    case "mul": return a * b;
    case "div": return a / b;
  }
}
