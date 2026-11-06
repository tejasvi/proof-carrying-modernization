// Dictionary (and array) reads tested for truthiness or compared with undefined are optional
// reads: a missing key reads as undefined (falsy), present falsy values (0, "") stay falsy, and
// present values are read; Object.prototype names keep panicking by design (not exercised).
class TrieNode { children: Record<string, TrieNode> = {}; end = false; }
class Trie {
  root = new TrieNode();
  add(w: string): void {
    let n = this.root;
    for (const ch of w) { if (!n.children[ch]) n.children[ch] = new TrieNode(); n = n.children[ch]; }
    n.end = true;
  }
  find(w: string): boolean {
    let n = this.root;
    for (const ch of w) { if (!n.children[ch]) return false; n = n.children[ch]; }
    return n.end;
  }
}
const t = new Trie();
t.add("ab");
t.add("b");
console.log(`${t.find("a")} ${t.find("ab")} ${t.find("abc")} ${t.find("b")} ${t.find("")} ${t.find("x")}`);
const counts: Record<string, number> = { zero: 0, one: 1 };
const names: Record<string, string> = { empty: "", x: "y" };
console.log(["zero", "one", "missing"].map((k) => `${counts[k] ? "T" : "F"}${!counts[k] ? "!" : ""}${counts[k] || 9}`).join(" "));
console.log(["empty", "x", "nope"].map((k) => `${names[k] ? "T" : "F"}${names[k] === undefined ? "u" : "d"}${names[k] ?? "?"}`).join(" "));
let found = 0;
for (const k of ["a", "zero", "one"]) { if (counts[k]) found++; }
const arr = [3, 0];
let i = 0;
while (arr[i]) i++;
console.log(`${found} ${i} ${arr[5] ? "yes" : "no"} ${counts.missing ? "has" : "lacks"}`);
const flags: boolean[] = [true];
const pos = [1, 2];
let j = 0;
while (pos[j]) j++;
console.log(`${j} ${!flags[3]} ${!flags[0]}`);
