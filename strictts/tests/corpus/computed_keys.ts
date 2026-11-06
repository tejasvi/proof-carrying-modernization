// Computed property reads with a key of a string-literal union whose cases are all properties:
// a case split on the key (records and mutable objects).
type Lang = "en" | "pt" | "es";
const LABELS = { en: "hello", pt: "olá", es: "hola", de: "hallo" };
function greet(l: Lang): string { return LABELS[l]; }
console.log((["en", "pt", "es"] as Lang[]).map(greet).join(" "));
const LIMITS: Record<Lang, number> = { en: 1, pt: 2, es: 3 };
let total = 0;
for (const l of ["es", "en"] as Lang[]) total += LIMITS[l];
console.log(`${total}`);
class Stats { hits = 0; misses = 2; }
const st = new Stats();
st.hits = 5;
function get(s: Stats, k: "hits" | "misses"): number { return s[k]; }
console.log(`${get(st, "hits")} ${get(st, "misses")}`);
type Key = keyof typeof LABELS;
const keys: Key[] = ["de", "en"];
console.log(keys.map((k) => LABELS[k].length).join(","));
