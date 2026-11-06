import EquivLean.Demo.XLang.Jsmn.CBase

/-!
# jsmn → model, C side: one step of the model's string scan

Unfolding lemmas for the model's `strScan` (one byte, with or without `\uXXXX` digits pending) and for
`parseString`, in the form the contract of `jsmn_parse_string` uses them.
-/

open EquivLean.Demo.XLang.Jsmn (strScan live byteAt escChar hexDigit ERROR_PART ERROR_INVAL ERROR_NOMEM STRING
  parseString St Tok)

set_option linter.deprecated false

namespace EquivLean.Demo.XLang.Jsmn.C

theorem ss_dead (js : List Nat) (p hex : Nat) (h : ¬ live js p) : strScan js p hex = .error ERROR_PART := by
  rw [strScan, dif_neg h]

theorem ss_hex (js : List Nat) (p hex : Nat) (h : live js p) (h0 : 0 < hex) (hx : hexDigit (byteAt js p) = true) :
    strScan js p hex = strScan js (p + 1) (hex - 1) := by
  rw [strScan]; simp only [dif_pos h, h0, hx, ite_true]

theorem ss_nonhex (js : List Nat) (p hex : Nat) (h : live js p) (h0 : 0 < hex)
    (hx : hexDigit (byteAt js p) = false) : strScan js p hex = .error ERROR_INVAL := by
  rw [strScan]; simp only [dif_pos h, h0, hx, ite_true, Bool.false_eq_true, ite_false]

theorem ss_quote (js : List Nat) (p : Nat) (h : live js p) (hc : byteAt js p = 34) : strScan js p 0 = .ok p := by
  rw [strScan]; simp only [dif_pos h, Nat.lt_irrefl, ite_false, hc, ite_true]

theorem ss_esc (js : List Nat) (p : Nat) (h : live js p) (hc : byteAt js p = 92) (h1 : p + 1 < js.length)
    (he : escChar (byteAt js (p + 1)) = true) : strScan js p 0 = strScan js (p + 2) 0 := by
  rw [strScan]
  simp (config := { decide := true }) only [dif_pos h, Nat.lt_irrefl, ite_false, hc, h1, he, ite_true, and_self]

theorem ss_u (js : List Nat) (p : Nat) (h : live js p) (hc : byteAt js p = 92) (h1 : p + 1 < js.length)
    (he : byteAt js (p + 1) = 117) : strScan js p 0 = strScan js (p + 2) 4 := by
  rw [strScan]
  have he' : escChar (byteAt js (p + 1)) = false := by rw [he]; decide
  simp (config := { decide := true }) only [dif_pos h, Nat.lt_irrefl, ite_false, hc, h1, he', he, ite_true,
    and_self, Bool.false_eq_true]

theorem ss_bad (js : List Nat) (p : Nat) (h : live js p) (hc : byteAt js p = 92) (h1 : p + 1 < js.length)
    (he : escChar (byteAt js (p + 1)) = false) (hu : byteAt js (p + 1) ≠ 117) :
    strScan js p 0 = .error ERROR_INVAL := by
  rw [strScan]
  simp (config := { decide := true }) only [dif_pos h, Nat.lt_irrefl, ite_false, hc, h1, he, hu, ite_true,
    and_self, Bool.false_eq_true]

theorem ss_other (js : List Nat) (p : Nat) (h : live js p) (hc : byteAt js p ≠ 34)
    (hb : ¬ (byteAt js p = 92 ∧ p + 1 < js.length)) : strScan js p 0 = strScan js (p + 1) 0 := by
  rw [strScan]; simp only [dif_pos h, Nat.lt_irrefl, ite_false, hc, hb]

theorem ps_err (js : List Nat) (n : Nat) (st : St) (e : Int) (h : strScan js (st.pos + 1) 0 = .error e) :
    parseString js n st = .error e := by
  unfold parseString; rw [h]

theorem ps_nomem (js : List Nat) (n : Nat) (st : St) (q : Nat) (h : strScan js (st.pos + 1) 0 = .ok q)
    (hn : n ≤ st.toks.length) : parseString js n st = .error ERROR_NOMEM := by
  unfold parseString; rw [h]; simp only [hn, ite_true]

theorem ps_ok (js : List Nat) (n : Nat) (st : St) (q : Nat) (h : strScan js (st.pos + 1) 0 = .ok q)
    (hn : st.toks.length < n) :
    parseString js n st = .ok ⟨q, st.toks ++ [⟨STRING, st.pos + 1, q, 0⟩], st.sup⟩ := by
  unfold parseString; rw [h]; simp only [show ¬ n ≤ st.toks.length by omega, ite_false]

end EquivLean.Demo.XLang.Jsmn.C
