// @extern
// Regular expressions as values: a literal used as a value, a const bound to one, or
// `new RegExp(pattern, flags)` is the record of its flags and source, and test / exec / match /
// replace / split / search through a value are the replayed externs (called with its source and
// flags); `new RegExp` with a bad pattern throws Node's SyntaxError, and its source escapes "/".
const PATTERNS: RegExp[] = [/^a+$/, /b/i, /(\d+)-(\d+)/];
function firstMatch(s: string, res: RegExp[]): number { return res.findIndex((re) => re.test(s)); }
console.log([firstMatch("aaa", PATTERNS), firstMatch("xBx", PATTERNS), firstMatch("12-34", PATTERNS), firstMatch("zz", PATTERNS)].join(" "));
const range = PATTERNS[2];
const m = range.exec("from 12-34 to");
console.log(m ? `${m[0]} ${m[1]} ${m[2]} ${m.index}` : "none");
const word = new RegExp("w(or)d", "gi");
console.log(`${word.source} ${word.flags} ${word.global} ${word.ignoreCase} ${word.sticky}`);
console.log("Word word WORD".replace(word, "X"));
const all = "a1b22c333".match(new RegExp("\\d+", "g"));
console.log(all ? `${all.length} ${all[0]} ${all[2]}` : "none");
const one = "x7y".match(new RegExp("(\\d)"));
console.log(one ? `${one[0]} ${one[1]} ${one.index}` : "none");
console.log(`${"hello world".search(new RegExp("o w"))} ${"abc".replaceAll(new RegExp("b", "g"), "-")}`);
console.log(`${"a1b2c".split(new RegExp("\\d")).join("|")} ${"a1b2c".split(new RegExp("(\\d)")).join("|")}`);
function build(p: string, f?: string): string {
  try { const re = new RegExp(p, f); return `ok ${re.source} ${re.flags}`; } catch (e) { return e instanceof Error ? e.name : "?"; }
}
console.log(`${build("a(b")} ${build("a/b")} ${build("x", "gg")} ${build("x", "im")}`);
const LIT = /x\/y/;
const held = [LIT, /z/m];
console.log(`${held[0].source} ${held[0].test("x/y")} ${held[1].multiline} ${RegExp("q+").test("qq")}`);
