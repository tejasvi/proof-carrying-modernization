// @extern
// String.prototype.normalize is an external call (Unicode tables are outside the semantics).
const composed: string = "é";
const decomposed: string = "é";
console.log(`${composed === decomposed} ${composed.normalize() === decomposed.normalize()} ${decomposed.normalize("NFC").length} ${composed.normalize("NFD").length}`);
