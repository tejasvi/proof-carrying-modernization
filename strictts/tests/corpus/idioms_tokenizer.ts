// @numbers
// A tokenizer and recursive-descent evaluator over strings (charAt, charCodeAt, indices).
type Tok = { kind: "num"; value: number } | { kind: "op"; op: string } | { kind: "paren"; open: boolean };
function tokenize(src: string): Tok[] {
  const toks: Tok[] = [];
  let i = 0;
  while (i < src.length) {
    const c = src.charAt(i);
    if (c === " ") { i++; continue; }
    if (c === "(" || c === ")") { toks.push({ kind: "paren", open: c === "(" }); i++; continue; }
    if ("+-*/".includes(c)) { toks.push({ kind: "op", op: c }); i++; continue; }
    let j = i;
    while (j < src.length && src.charCodeAt(j) >= 48 && src.charCodeAt(j) <= 57) j++;
    if (j === i) throw new SyntaxError(`unexpected ${c} at ${i}`);
    toks.push({ kind: "num", value: Number(src.slice(i, j)) });
    i = j;
  }
  return toks;
}
class Parser {
  private pos = 0;
  constructor(private toks: Tok[]) {}
  private peek(): Tok | undefined { return this.toks[this.pos]; }
  expr(): number {
    let v = this.term();
    for (;;) {
      const t = this.peek();
      if (t === undefined || t.kind !== "op" || (t.op !== "+" && t.op !== "-")) return v;
      this.pos++;
      const r = this.term();
      v = t.op === "+" ? v + r : v - r;
    }
  }
  term(): number {
    let v = this.atom();
    for (;;) {
      const t = this.peek();
      if (t === undefined || t.kind !== "op" || (t.op !== "*" && t.op !== "/")) return v;
      this.pos++;
      const r = this.atom();
      v = t.op === "*" ? v * r : v / r;
    }
  }
  atom(): number {
    const t = this.peek();
    this.pos++;
    if (t === undefined) throw new SyntaxError("unexpected end");
    if (t.kind === "num") return t.value;
    if (t.kind === "paren" && t.open) {
      const v = this.expr();
      this.pos++;
      return v;
    }
    if (t.kind === "op" && t.op === "-") return -this.atom();
    throw new SyntaxError("unexpected token");
  }
}
for (const src of ["1 + 2 * 3", "(1 + 2) * 3", "10 / 4 - -2", "2 * (3 + 4) * 5", "7 $ 2"]) {
  try {
    console.log(`${src} = ${new Parser(tokenize(src)).expr()}`);
  } catch (e) {
    console.log(`${src}: ${(e as Error).name}: ${(e as Error).message}`);
  }
}
