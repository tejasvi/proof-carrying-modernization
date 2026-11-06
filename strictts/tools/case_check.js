#!/usr/bin/env node
// Check of Impl.host's case mapping (StrictTS/Str/Case.lean) against Node: every code point
// alone, plus random strings over a case-heavy alphabet (Greek sigma contexts, ß, ligatures,
// İ/ı, Georgian, Cherokee, Deseret, combining marks, lone surrogates). Writes a Lean file whose
// #eval prints the number of disagreements and the first few.
//   node tools/case_check.js OUT.lean [N]
//   tools/run.sh 0.3 590 lake env lean OUT.lean
'use strict';
const fs = require('fs');
const out = process.argv[2];
const n = Number(process.argv[3] || 3000);
const cases = [];
for (let c = 0x80; c <= 0x10ffff; c++) {
  if (c >= 0xd800 && c <= 0xdfff) continue;
  const s = String.fromCodePoint(c);
  if (s.toUpperCase() !== s || s.toLowerCase() !== s) cases.push(s);
}
const alpha = ['Σ', 'σ', 'ς', 'Α', 'α', ' ', '.', "'", 'ͅ', '́', 'ß', 'ﬀ', 'ŉ', 'İ', 'ı', 'i', 'I', 'Ⴀ', 'ა', 'Ꭰ', 'ꭰ', '𐐀', '𐐨', '\ud800', '\udc00', 'a', 'Z', '0', 'ǅ', 'ǆ', 'Ǆ', 'ΐ', 'ᾈ', 'ﬓ', '­', ':', '’'];
let seed = 12345;
const rnd = (k) => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed % k; };
for (let i = 0; i < n; i++) { let s = ''; const len = 1 + rnd(7); for (let j = 0; j < len; j++) s += alpha[rnd(alpha.length)]; cases.push(s); }
// one line per case: input, toUpperCase, toLowerCase as space-separated code units, ';'-separated
const enc = (x) => [...Array(x.length).keys()].map(i => x.charCodeAt(i)).join(' ');
const data = cases.map(s => `${enc(s)};${enc(s.toUpperCase())};${enc(s.toLowerCase())}`).join('\n');
const lean = `import StrictTS.Str.Case
open StrictTS

def data : String := ${JSON.stringify(data)}

def units (s : String) : List UInt16 := (s.splitOn " ").filter (· ≠ "") |>.map fun x => x.toNat!.toUInt16

#eval Id.run do
  let mut bad := 0
  let mut total := 0
  let mut first : List String := []
  for line in data.splitOn "\n" do
    match line.splitOn ";" with
    | [a, b, c] =>
      total := total + 1
      let s := units a
      let u := (JSStr.toUpperFull ⟨s⟩).units
      let l := (JSStr.toLowerFull ⟨s⟩).units
      if u != units b || l != units c then
        bad := bad + 1
        if first.length < 5 then first := first ++ [s!"{s}: upper {u} vs {units b}, lower {l} vs {units c}"]
    | _ => pure ()
  return s!"case check: {total} strings, {bad} disagreements {first}"
`;
fs.writeFileSync(out, lean);
console.log(`case_check: ${cases.length} strings written to ${out}`);
