// @numbers
// String corner cases: replacement patterns, lone surrogates, astral characters, escapes.
console.log("abc".replace("b", "[$&]") + " " + "aaa".replaceAll("a", "$$") + " " + "x-y".replace("-", "$'|$`"));
const lone = "\uD800";
console.log(`${lone.length} ${lone.charCodeAt(0)} ${"\uDC00\uD800".length}`);
const astral = "𝔸𝔹";
console.log(`${astral.length} ${astral.codePointAt(0) ?? 0} ${astral.slice(0, 2)} ${[...astral].length}`);
console.log("tab\there \"quoted\" back\\slash");
// (non-ASCII case mapping is implementation-defined: Impl.host maps ASCII only)
console.log(`${"abz".toUpperCase()} ${"İ".length} ${"abc" < "abd"} ${"Z" < "a"} ${"10" < "9"}`);
console.log(`${"a".padStart(4, "")}|${"abc".padEnd(2)}|${"x".repeat(0)}|${"".split("").length}`);
console.log(`${9007199254740993} ${0.1 * 3} ${1e300 * 1e10} ${5e-324} ${-1e-7}`);
