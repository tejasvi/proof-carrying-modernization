// A loop over the host's match results (`String.prototype.matchAll`, an external call answered
// by the world's oracle) that reads `m.index` and `m[0]` of each match (external calls too). No
// iteration panics when the host keeps the guarantees of ECMA-262 that the code relies on: the
// matches form a fresh array, and element 0 of a match is the matched text
// (`World.MatchAllFresh`, `World.MatchElementZero`); the host may still throw.

export function prefixLines(text: string, prefix: string): string {
  let out = "";
  let last = 0;
  for (const m of text.matchAll(/\n/g)) {
    const i = m.index;
    out += text.slice(last, i) + m[0] + prefix;
    last = i + m[0].length;
  }
  return prefix + out + text.slice(last);
}

console.log(prefixLines("a\nb", "> "));
