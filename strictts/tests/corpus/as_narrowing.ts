// A narrowing `as` (to a type TypeScript considers narrower) is a checked narrowing: the value
// is converted, and a wrong cast panics (not exercised here); not in the strict subset.
type Shape = { kind: "a"; x: bigint } | { kind: "b"; y: bigint };
function fa(s: Shape): bigint { return (s as { kind: "a"; x: bigint }).x; }
console.log(`${fa({ kind: "a", x: 1n })}`);
const env: Record<string, string | undefined> = { LANG: "pt", PORT: "8080" };
const lang = env.LANG as "en" | "pt" | "es";
const port = Number(env.PORT as string);
const maybe: number | undefined = [5, 6].find((v) => v > 5);
console.log(`${lang} ${port + 1} ${(maybe as number) * 2}`);
type Lang = "en" | "pt";
function greet(l: string): string { const k = l as Lang; return k === "pt" ? "olá" : "hello"; }
console.log(`${greet("pt")} ${greet("en")}`);
