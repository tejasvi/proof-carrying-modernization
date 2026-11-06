/-
# Alphanumeric lemmas

Byte-string comparison and filling, at the level symbolic execution needs: a nonnumeric
comparison of equal-length strings is `=` exactly when the byte lists are equal, and a
figurative constant fills with `List.replicate`.
-/
import Cobol.Logic.Basic

namespace Cobol

theorem cmpBytes_eq_iff : ∀ (l1 l2 : List UInt8), l1.length = l2.length →
    (Sem.cmpBytes l1 l2 = .eq ↔ l1 = l2)
  | [], [], _ => by simp [Sem.cmpBytes]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := cmpBytes_eq_iff as bs h
    simp only [Sem.cmpBytes, List.cons.injEq]
    by_cases hab : a < b
    · simp only [hab, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro he; subst he; exact absurd hab (UInt8.lt_irrefl a)
    · by_cases hba : b < a
      · simp only [hab, hba, ↓reduceIte, reduceCtorEq, false_iff, not_and]
        intro he; subst he; exact absurd hba (UInt8.lt_irrefl a)
      · have : a = b := by
          have h1 := UInt8.not_lt.mp hab
          have h2 := UInt8.not_lt.mp hba
          exact UInt8.le_antisymm h2 h1
        subst this
        simp only [UInt8.lt_irrefl, ↓reduceIte, true_and, ih]

@[simp, cobol_eval] theorem cmpBytes_eq_iff' (l1 l2 : List UInt8) (h : l1.length = l2.length) :
    (Sem.cmpBytes l1 l2 = .eq) = (l1 = l2) := propext (cmpBytes_eq_iff l1 l2 h)

@[simp, cobol_eval] theorem cmpBytes_beq_eq (l1 l2 : List UInt8) (h : l1.length = l2.length) :
    (Sem.cmpBytes l1 l2 == .eq) = decide (l1 = l2) := by
  have e := cmpBytes_eq_iff l1 l2 h
  by_cases hl : l1 = l2
  · rw [e.mpr hl]; simp [hl]
  · simp only [hl, decide_false]
    cases hc : Sem.cmpBytes l1 l2
    · rfl
    · exact absurd (e.mp hc) hl
    · rfl

/-- A string compared with itself (any length, symbolic contents). -/
@[simp, cobol_eval] theorem cmpBytes_self : ∀ l : List UInt8, Sem.cmpBytes l l = .eq
  | [] => rfl
  | a :: as => by simp [Sem.cmpBytes, UInt8.lt_irrefl, cmpBytes_self as]

@[simp, cobol_eval] theorem fillPattern_single (b : UInt8) (n : Nat) :
    Sem.fillPattern [b] n = List.replicate n b := by
  apply List.ext_getElem
  · simp [Sem.fillPattern]
  · intro i h1 h2; simp [Sem.fillPattern, Nat.mod_one]

attribute [cobol_eval] List.take_of_length_le List.length_replicate

theorem Mem.read_eq_cons (m : Mem) (off : Nat) : m.read off 1 = [m.get off] := by
  simp [Mem.read]

/-! `==` on the outcomes of a byte-string comparison. -/
section
@[cobol_eval] theorem ordering_beq_lt_lt : (Ordering.lt == Ordering.lt) = true := rfl
@[cobol_eval] theorem ordering_beq_lt_eq : (Ordering.lt == Ordering.eq) = false := rfl
@[cobol_eval] theorem ordering_beq_lt_gt : (Ordering.lt == Ordering.gt) = false := rfl
@[cobol_eval] theorem ordering_beq_eq_lt : (Ordering.eq == Ordering.lt) = false := rfl
@[cobol_eval] theorem ordering_beq_eq_eq : (Ordering.eq == Ordering.eq) = true := rfl
@[cobol_eval] theorem ordering_beq_eq_gt : (Ordering.eq == Ordering.gt) = false := rfl
@[cobol_eval] theorem ordering_beq_gt_lt : (Ordering.gt == Ordering.lt) = false := rfl
@[cobol_eval] theorem ordering_beq_gt_eq : (Ordering.gt == Ordering.eq) = false := rfl
@[cobol_eval] theorem ordering_beq_gt_gt : (Ordering.gt == Ordering.gt) = true := rfl
end

/-! ## Digit characters of a value (a numeric item compared with an alphanumeric one)

`Sem.digitChars` stays folded in symbolic execution; two digit strings compare equal exactly
when the values agree modulo `10^w`, and a digit string never equals a run of spaces. -/
theorem toDigits_mod10 (n v : Nat) : Digits.toDigits 10 n v = Digits.toDigits 10 n (v % 10 ^ n) := by
  have h := Digits.toDigits_ofDigits (b := 10) (Digits.toDigits 10 n v) (Digits.toDigits_lt (by decide) n v)
  rw [Digits.length_toDigits, Digits.ofDigits_toDigits] at h
  exact h.symm

theorem digitByte_inj (c : Config) {d e : Nat} (hd : d < 10) (he : e < 10)
    (h : c.digitByte d = c.digitByte e) : d = e := by
  unfold Config.digitByte at h
  cases hc : c.charset <;> simp only [hc] at h <;>
    (have h' := congrArg UInt8.toNat h; simp [UInt8.toNat_ofNat] at h'; omega)

theorem map_digitByte_inj (c : Config) : ∀ (l1 l2 : List Nat), (∀ d ∈ l1, d < 10) →
    (∀ d ∈ l2, d < 10) → l1.map c.digitByte = l2.map c.digitByte → l1 = l2
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: as, b :: bs, h1, h2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hab := digitByte_inj c (h1 a (by simp)) (h2 b (by simp)) h.1
    have ih := map_digitByte_inj c as bs (fun d hd => h1 d (by simp [hd]))
      (fun d hd => h2 d (by simp [hd])) h.2
    rw [hab, ih]

theorem digitChars_eq_iff (c : Config) (w a b : Nat) :
    Sem.digitChars c w a = Sem.digitChars c w b ↔ a % 10 ^ w = b % 10 ^ w := by
  unfold Sem.digitChars
  constructor
  · intro h
    have e := map_digitByte_inj c _ _ (Digits.toDigits_lt (by decide) w a)
      (Digits.toDigits_lt (by decide) w b) h
    have := congrArg (Digits.ofDigits 10) e
    rwa [Digits.ofDigits_toDigits, Digits.ofDigits_toDigits] at this
  · intro h
    rw [toDigits_mod10 w a, toDigits_mod10 w b, h]

@[cobol_eval] theorem length_digitChars (c : Config) (w n : Nat) :
    (Sem.digitChars c w n).length = w := by
  simp [Sem.digitChars]

@[cobol_eval] theorem digitChars_eq_eq (c : Config) (w a b : Nat) :
    (Sem.digitChars c w a = Sem.digitChars c w b) = (a % 10 ^ w = b % 10 ^ w) :=
  propext (digitChars_eq_iff c w a b)

@[cobol_eval] theorem digitChars_eq_cons (c : Config) (w a : Nat) (b : UInt8) (bs : List UInt8)
    (hw : 0 < w) (hb : b.toNat < (match c.charset with | .ebcdic => 0xF0 | .ascii => 0x30)) :
    (Sem.digitChars c w a = b :: bs) = False := by
  apply eq_false
  intro h
  have h0 := congrArg (fun l => l[0]?) h
  simp only [Sem.digitChars, List.getElem?_map, List.getElem?_cons_zero] at h0
  obtain ⟨d, hd, hdb⟩ : ∃ d, (Digits.toDigits 10 w a)[0]? = some d ∧ c.digitByte d = b := by
    cases hx : (Digits.toDigits 10 w a)[0]? with
    | none => simp [hx] at h0
    | some d => exact ⟨d, rfl, by simpa [hx] using h0⟩
  have hd10 : d < 10 := Digits.toDigits_lt (by decide) w a d (List.mem_of_getElem? hd)
  subst hdb
  have key : ∀ n, n < 256 → (UInt8.ofNat n).toNat = n := fun n h => by
    simp [UInt8.toNat_ofNat]; omega
  unfold Config.digitByte at hb
  cases hc : c.charset <;> simp only [hc] at hb
  · rw [key _ (by omega)] at hb; omega
  · rw [key _ (by omega)] at hb; omega

end Cobol
