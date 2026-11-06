// @extern
// String.raw as a tag: the raw text of the template (escapes as written: \n is two characters,
// \u0041 six, an invalid \u escape allowed), line breaks as LF, substitutions converted as in a
// template literal; a module variable holding a regex built from one (new RegExp(String.raw`…`)).
const DIGITS = new RegExp(String.raw`^\d+(\.\d+)?$`);
const PATH = String.raw`C:\new\table\u0041\unicode`;
const n = 3;
const mixed = String.raw`x\n${n}\t${"y"}${true}-${n * 2}`;
const empty = String.raw``;
const lines = String.raw`a
b\
c`;
console.log(`${DIGITS.test("12.5")} ${DIGITS.test("1.")} ${DIGITS.source}`);
console.log(`${PATH} ${PATH.length} ${mixed} ${mixed.length} [${empty}] ${lines.length} ${JSON.stringify(lines)}`);
