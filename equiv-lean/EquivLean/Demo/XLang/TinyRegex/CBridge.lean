import EquivLean.Demo.XLang.TinyRegex.COneCh

/-!
# tiny-regex-c → model, C side: the C-level tests against the model's

The contracts state the C's tests on `char` values (`c = sc b` for the byte `b`); these lemmas
give the model's functions on the byte.
-/

namespace EquivLean.Demo.XLang.TinyRegex.C

open EquivLean.Demo.XLang.TinyRegex (Tok sc matchone Ctx DOT CHAR_CLASS INV_CHAR_CLASS DIGIT
  NOT_DIGIT ALPHA NOT_ALPHA WHITESPACE NOT_WHITESPACE isdigitC isalphaC isspaceC matchalphanum)

/-- `matchone` on a token of a type other than the classes: no UB, and the C test `oneChP`. -/
theorem matchone_ch_bridge (C : Ctx) (tok : Tok) {b : Nat} (hb : b < 256) (h8 : tok.type ≠ 8)
    (h9 : tok.type ≠ 9) :
    (matchone C tok b).2 = 0 ∧ ((matchone C tok b).1 = true ↔ oneChP tok.type tok.ch (sc b)) := by
  have hd := isdigitC_iff hb
  have ha := matchalphanum_iff hb
  have hs := isspaceC_iff hb
  unfold matchone oneChP
  simp only [DOT, CHAR_CLASS, INV_CHAR_CLASS, DIGIT, NOT_DIGIT, ALPHA, NOT_ALPHA, WHITESPACE,
    NOT_WHITESPACE]
  unfold alnumP alphaP digitP spaceP
  by_cases e1 : tok.type = 1
  · simp [e1]
  by_cases e10 : tok.type = 10
  · simp [e10, hd]
  by_cases e11 : tok.type = 11
  · simp only [e11, if_neg e1, if_neg e10]; cases hx : isdigitC b <;> simp_all <;> omega
  by_cases e12 : tok.type = 12
  · simp [e12, ha, or_assoc]
  by_cases e13 : tok.type = 13
  · simp only [e13]; cases hx : matchalphanum b <;> simp_all <;> omega
  by_cases e14 : tok.type = 14
  · simp [e14, hs]
  by_cases e15 : tok.type = 15
  · simp only [e15]; cases hx : isspaceC b <;> simp_all <;> omega
  simp [e1, e10, e11, e12, e13, e14, e15, h8, h9]

end EquivLean.Demo.XLang.TinyRegex.C
