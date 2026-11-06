// @extern
// @panic
// test / exec on a regex value whose flags are not known where it is used: a global or sticky one
// reads and writes its lastIndex, which is not modelled, so the Lean run panics there (the last
// line, where Node prints the result of the match).
function count(re: RegExp, s: string): number { let n = 0; if (re.test(s)) n++; return n; }
console.log(`${count(/a/, "aa")} ${count(new RegExp("b", "i"), "B")} ${count(/c/m, "x")}`);
console.log(`${count(new RegExp("a", "g"), "aa")}`);
