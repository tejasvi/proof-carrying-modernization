import EquivLean.Modernize.Cbtrn03c.JavaW.EditDefs
import EquivLean.Modernize.Cbtrn03c.JavaSpec

/-!
# CBTRN03C → Java: the helpers' strings as the model's lines

The strings the helpers build, as code points of the model (`jline`): the digits (`zpad`), the
zoned field, the padded field, the edited amount (`Model.editAmt`), the text of EBCDIC bytes
(`cp037Str`).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

theorem jline_append (a b : List Nat) : jline (a ++ b) = jline a ++ jline b := List.map_append ..

theorem jline_cons (u : Nat) (l : List Nat) : jline (u :: l) = BitVec.ofNat 16 u :: jline l := rfl

theorem jline_nil : jline [] = [] := rfl

theorem toDigits_succ' (n v : Nat) : Cobol.Digits.toDigits 10 (n + 1) v =
    Cobol.Digits.toDigits 10 n (v / 10) ++ [v % 10] := rfl

/-- `digits` builds the model's zero-padded digits. -/
theorem zpadJ_eq (c n : Nat) : zpadJ c n = jline (zpad n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [zpadJ, ih, zpad, zpad, toDigits_succ', List.map_append, jline_append]
    rfl

/-- `zoned` builds the model's signed DISPLAY field. -/
theorem zonedJ_eq (v : I64) (n : Nat) : zonedJ v n = jline (Model.zoned n v.toInt) := by
  rw [zonedJ, Model.zoned, jline_append, zpadJ_eq]
  rfl

/-- `n` copies of the character `u` (`repeat`). -/
theorem repJ_eq (u : Nat) (n : Nat) : repJ (BitVec.ofNat 16 u) n = jline (List.replicate n u) := by
  simp [repJ, jline, List.map_replicate]

theorem spJ_eq (n : Nat) : spJ n = jline (List.replicate n 32) := repJ_eq 32 n

/-- `pad` builds the model's padded field. -/
theorem fixJ_eq (l : List Nat) (n : Nat) : fixJ (jline l) n = jline (Model.pad l n) := by
  rw [fixJ_eq_padJ, padJ, Model.pad]
  simp [jline, spJ, repJ, space, List.map_take, List.map_replicate]

/-- The text of EBCDIC bytes: the model's code points (`Model.cps`). -/
theorem cp037Str_eq (bs : List UInt8) : cp037Str bs = jline (Model.cps bs) := by
  simp [cp037Str, cp037Unit, jline, Model.cps, cp037Code, List.map_map, Function.comp_def]

/-! ## The edited amount -/

theorem zzz_pattern : "ZZZ,ZZZ,ZZZ".toList = ['Z', 'Z', 'Z', ',', 'Z', 'Z', 'Z', ',', 'Z', 'Z', 'Z'] := by
  decide

theorem toDigits_lt10 {n v d : Nat} (h : d ∈ Cobol.Digits.toDigits 10 n v) : d < 10 := by
  induction n generalizing v with
  | zero => simp [Cobol.Digits.toDigits] at h
  | succ n ih =>
    rw [toDigits_succ'] at h
    rcases List.mem_append.1 h with h | h
    · exact ih h
    · rw [List.mem_singleton] at h
      subst h
      exact Nat.mod_lt _ (by decide)

theorem digit16_eq_48 {d : Nat} (h : d < 10) :
    (BitVec.ofNat 16 (48 + d) = BitVec.ofNat 16 48) = (d = 0) := by
  apply propext; constructor
  · intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    omega
  · rintro rfl; rfl

/-- The 11 digits of `m`: the 9 of `m / 100`, then two. -/
theorem toDigits_11 (m : Nat) : Cobol.Digits.toDigits 10 11 m =
    Cobol.Digits.toDigits 10 9 (m / 100) ++ [m / 10 % 10, m % 10] := by
  rw [toDigits_succ', toDigits_succ', Nat.div_div_eq_div_mul]
  simp

/-- The integer part `edit` builds is the model's `ZZZ,ZZZ,ZZZ` editing. -/
theorem edS_eq_zzz (ds : List Nat) (h9 : ds.length = 9) (hd : ∀ d ∈ ds, d < 10)
    (tail : List Nat) :
    edS (jline ((ds ++ tail).map (48 + ·))) 9 =
      jline (Model.zzz "ZZZ,ZZZ,ZZZ".toList ds true) := by
  match ds, h9 with
  | [d0, d1, d2, d3, d4, d5, d6, d7, d8], _ =>
    have h0 := hd d0 (by simp); have h1 := hd d1 (by simp); have h2 := hd d2 (by simp)
    have h3 := hd d3 (by simp); have h4 := hd d4 (by simp); have h5 := hd d5 (by simp)
    have h6 := hd d6 (by simp); have h7 := hd d7 (by simp); have h8 := hd d8 (by simp)
    rw [zzz_pattern]
    by_cases e0 : d0 = 0
    · subst e0
      by_cases e1 : d1 = 0
      · subst e1
        by_cases e2 : d2 = 0
        · subst e2
          by_cases e3 : d3 = 0
          · subst e3
            by_cases e4 : d4 = 0
            · subst e4
              by_cases e5 : d5 = 0
              · subst e5
                by_cases e6 : d6 = 0
                · subst e6
                  by_cases e7 : d7 = 0
                  · subst e7
                    by_cases e8 : d8 = 0
                    · subst e8
                      simp [edS, edB, Model.zzz, jline, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, digitJ, comma, space, digit16_eq_48 h0, digit16_eq_48 h1, digit16_eq_48 h2, digit16_eq_48 h3, digit16_eq_48 h4, digit16_eq_48 h5, digit16_eq_48 h6, digit16_eq_48 h7, digit16_eq_48 h8]
                    · simp [edS, edB, Model.zzz, jline, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, digitJ, comma, space, digit16_eq_48 h0, digit16_eq_48 h1, digit16_eq_48 h2, digit16_eq_48 h3, digit16_eq_48 h4, digit16_eq_48 h5, digit16_eq_48 h6, digit16_eq_48 h7, digit16_eq_48 h8, e8]
                  · simp [edS, edB, Model.zzz, jline, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, digitJ, comma, space, digit16_eq_48 h0, digit16_eq_48 h1, digit16_eq_48 h2, digit16_eq_48 h3, digit16_eq_48 h4, digit16_eq_48 h5, digit16_eq_48 h6, digit16_eq_48 h7, digit16_eq_48 h8, e7]
                · simp [edS, edB, Model.zzz, jline, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, digitJ, comma, space, digit16_eq_48 h0, digit16_eq_48 h1, digit16_eq_48 h2, digit16_eq_48 h3, digit16_eq_48 h4, digit16_eq_48 h5, digit16_eq_48 h6, digit16_eq_48 h7, digit16_eq_48 h8, e6]
              · simp [edS, edB, Model.zzz, jline, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, digitJ, comma, space, digit16_eq_48 h0, digit16_eq_48 h1, digit16_eq_48 h2, digit16_eq_48 h3, digit16_eq_48 h4, digit16_eq_48 h5, digit16_eq_48 h6, digit16_eq_48 h7, digit16_eq_48 h8, e5]
            · simp [edS, edB, Model.zzz, jline, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, digitJ, comma, space, digit16_eq_48 h0, digit16_eq_48 h1, digit16_eq_48 h2, digit16_eq_48 h3, digit16_eq_48 h4, digit16_eq_48 h5, digit16_eq_48 h6, digit16_eq_48 h7, digit16_eq_48 h8, e4]
          · simp [edS, edB, Model.zzz, jline, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, digitJ, comma, space, digit16_eq_48 h0, digit16_eq_48 h1, digit16_eq_48 h2, digit16_eq_48 h3, digit16_eq_48 h4, digit16_eq_48 h5, digit16_eq_48 h6, digit16_eq_48 h7, digit16_eq_48 h8, e3]
        · simp [edS, edB, Model.zzz, jline, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, digitJ, comma, space, digit16_eq_48 h0, digit16_eq_48 h1, digit16_eq_48 h2, digit16_eq_48 h3, digit16_eq_48 h4, digit16_eq_48 h5, digit16_eq_48 h6, digit16_eq_48 h7, digit16_eq_48 h8, e2]
      · simp [edS, edB, Model.zzz, jline, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, digitJ, comma, space, digit16_eq_48 h0, digit16_eq_48 h1, digit16_eq_48 h2, digit16_eq_48 h3, digit16_eq_48 h4, digit16_eq_48 h5, digit16_eq_48 h6, digit16_eq_48 h7, digit16_eq_48 h8, e1]
    · simp [edS, edB, Model.zzz, jline, List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, digitJ, comma, space, digit16_eq_48 h0, digit16_eq_48 h1, digit16_eq_48 h2, digit16_eq_48 h3, digit16_eq_48 h4, digit16_eq_48 h5, digit16_eq_48 h6, digit16_eq_48 h7, digit16_eq_48 h8, e0]

theorem jline_getD_9 (ds : List Nat) (h9 : ds.length = 9) (a b : Nat) :
    (jline ((ds ++ [a, b]).map (48 + ·))).getD 9 0 = BitVec.ofNat 16 (48 + a) ∧
    (jline ((ds ++ [a, b]).map (48 + ·))).getD 10 0 = BitVec.ofNat 16 (48 + b) := by
  match ds, h9 with
  | [_, _, _, _, _, _, _, _, _], _ => exact ⟨rfl, rfl⟩

/-- **`edit` builds the model's edited amount.** -/
theorem editJ_eq (v : Int) (plus : Bool) :
    editJ (decide (v < 0)) plus (v.natAbs % 100000000000) = jline (Model.editAmt v plus) := by
  unfold editJ Model.editAmt
  by_cases hm : v.natAbs % 100000000000 = 0
  · simp only [hm, ite_true]
    exact spJ_eq 15
  · simp only [hm, ite_false]
    have hds := Cobol.Digits.length_toDigits 10 9 (v.natAbs % 100000000000 / 100)
    have hlt : ∀ d ∈ Cobol.Digits.toDigits 10 9 (v.natAbs % 100000000000 / 100), d < 10 :=
      fun d hd => toDigits_lt10 hd
    rw [zpadJ_eq, zpad, toDigits_11]
    obtain ⟨g9, g10⟩ := jline_getD_9 _ hds ((v.natAbs % 100000000000) / 10 % 10)
      ((v.natAbs % 100000000000) % 10)
    rw [g9, g10, edS_eq_zzz _ hds hlt]
    have e1 : v.natAbs % 100000000000 % 100 / 10 = v.natAbs % 100000000000 / 10 % 10 := by
      rw [show (100 : Nat) = 10 * 10 by rfl, Nat.mod_mul_right_div_self]
    rw [e1]
    simp only [jline, List.map_cons, List.map_append, List.map_nil]
    congr 1
    unfold signJ space
    by_cases hv : v < 0
    · simp [hv]
    · by_cases hp : plus <;> simp [hv, hp]

/-! The report's string literals as code points. -/

theorem lit_pageTotal : JStr.ofString "Page Total" = jline (Model.txt "Page Total") := by decide
theorem lit_accountTotal : JStr.ofString "Account Total" = jline (Model.txt "Account Total") := by decide
theorem lit_grandTotal : JStr.ofString "Grand Total" = jline (Model.txt "Grand Total") := by decide
theorem lit_dalyrept : JStr.ofString "DALYREPT" = jline (Model.txt "DALYREPT") := by decide
theorem lit_dailyReport : JStr.ofString "Daily Transaction Report" = jline (Model.txt "Daily Transaction Report") := by decide
theorem lit_dateRange : JStr.ofString "Date Range: " = jline (Model.txt "Date Range: ") := by decide
theorem lit_to : JStr.ofString " to " = jline (Model.txt " to ") := by decide
theorem lit_tranId : JStr.ofString "Transaction ID" = jline (Model.txt "Transaction ID") := by decide
theorem lit_acctId : JStr.ofString "Account ID" = jline (Model.txt "Account ID") := by decide
theorem lit_tranType : JStr.ofString "Transaction Type" = jline (Model.txt "Transaction Type") := by decide
theorem lit_tranCat : JStr.ofString "Tran Category" = jline (Model.txt "Tran Category") := by decide
theorem lit_tranSource : JStr.ofString "Tran Source" = jline (Model.txt "Tran Source") := by decide
theorem lit_amount : JStr.ofString "        Amount" = jline (Model.txt "        Amount") := by decide
theorem lit_sp4 : JStr.ofString "    " = jline (Model.txt "    ") := by decide
theorem lit_sp2 : JStr.ofString "  " = jline (Model.txt "  ") := by decide

end EquivLean.Modernize.Cbtrn03c.Java
