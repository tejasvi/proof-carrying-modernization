// A recursive union type built with reduce from an array of optional values (`atoms[0]!`): the
// value is converted to the named type and read back at once (the translation must not leave
// `unfold (fold …)`, whose intermediate type Lean cannot infer).
type Cond = { t: "true" } | { t: "flag"; id: string; neg: boolean } | { t: "and" | "or"; a: Cond; b: Cond };
function atom(s: string): Cond | undefined {
  if (s === "true") return { t: "true" };
  if (s.length > 0 && s.length < 9) return { t: "flag", id: s.startsWith("!") ? s.slice(1) : s, neg: s.startsWith("!") };
  return undefined;
}
function parse(src: string): Cond | undefined {
  const atoms = src.split("&&").map((q) => atom(q.trim()));
  if (atoms.some((a) => !a)) return undefined;
  return atoms.slice(1).reduce<Cond>((acc, a) => ({ t: "and", a: acc, b: a! }), atoms[0]!);
}
function show(c: Cond): string {
  switch (c.t) {
    case "true": return "T";
    case "flag": return (c.neg ? "!" : "") + c.id;
    default: return `(${show(c.a)} ${c.t} ${show(c.b)})`;
  }
}
for (const s of ["true", "a && !b", "a && b && true", "a && toolongname"]) {
  const c = parse(s);
  console.log(c ? show(c) : "invalid");
}
