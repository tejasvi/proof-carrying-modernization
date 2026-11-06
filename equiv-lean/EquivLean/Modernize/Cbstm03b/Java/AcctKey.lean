import EquivLean.Modernize.Cbstm03b.Java.Base

/-!
# CBSTM03B → Java, `acctProc`: the key loop

`acctProc` reads the account key from the first `LK-M03B-KEY-LN` characters of `LK-M03B-KEY` (`keySub`), a
digit at a time: `v = (v * 10 + d) % 10^11` (`jkey`). On a key of CP037 digits (`KeyOk`) this is the model's
`acctVal`: the key's decimal value, high-order truncated to 11 digits (`jkey_digits`, `acctVal_eq`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b EquivLean.Modernize.Cbstm03b.Java

/-- The digit the key loop takes from a character (`0` for a non-digit). -/
def jdig (c : JChar) : Nat := if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then c.toNat - 48 else 0

/-- The value of the key loop after reading `cs`. -/
def jkey (cs : JStr) : Nat := cs.foldl (fun v c => (v * 10 + jdig c) % 100000000000) 0

theorem jkey_append (cs : JStr) (c : JChar) :
    jkey (cs ++ [c]) = (jkey cs * 10 + jdig c) % 100000000000 := by
  simp [jkey, List.foldl_append]

theorem jkey_lt (cs : JStr) : jkey cs < 100000000000 := by
  induction cs using List.reverseRecOn with
  | nil => decide
  | append_singleton cs c _ => rw [jkey_append]; omega

theorem jdig_cp037_fin : ∀ n : Fin 256, 240 ≤ n.val → n.val ≤ 249 →
    jdig (cp037Unit (UInt8.ofNat n.val)) = n.val - 240 := by
  decide +kernel

theorem jdig_cp037 (b : UInt8) (h : 240 ≤ b ∧ b ≤ 249) : jdig (cp037Unit b) = b.toNat - 240 := by
  have := jdig_cp037_fin ⟨b.toNat, b.toNat_lt⟩ h.1 h.2
  simpa only [UInt8.ofNat_toNat] using this

theorem decDigit_fin : ∀ n : Fin 256, 240 ≤ n.val → n.val ≤ 249 →
    ({} : Cobol.Config).decDigit (UInt8.ofNat n.val) = some (n.val - 240) := by
  decide +kernel

theorem decDigit_of_digit (b : UInt8) (h : 240 ≤ b ∧ b ≤ 249) :
    ({} : Cobol.Config).decDigit b = some (b.toNat - 240) := by
  have := decDigit_fin ⟨b.toNat, b.toNat_lt⟩ h.1 h.2
  simpa only [UInt8.ofNat_toNat] using this

theorem jkey_digits (bs : List UInt8) (hb : ∀ b ∈ bs, 240 ≤ b ∧ b ≤ 249) :
    jkey (cp037Str bs) = Cobol.Digits.ofDigits 10 (bs.map fun b => b.toNat - 240) % 100000000000 := by
  have key : ∀ (l : List UInt8), (∀ b ∈ l, 240 ≤ b ∧ b ≤ 249) → ∀ a,
      (l.map cp037Unit).foldl (fun v c => (v * 10 + jdig c) % 100000000000) (a % 100000000000) =
      (l.map fun b => b.toNat - 240).foldl (fun v d => v * 10 + d) a % 100000000000 := by
    intro l
    induction l with
    | nil => intro _ a; rfl
    | cons b l ih =>
      intro hl a
      simp only [List.map_cons, List.foldl_cons]
      rw [jdig_cp037 b (hl b (List.mem_cons_self ..))]
      have e : (a % 100000000000 * 10 + (b.toNat - 240)) % 100000000000 =
          (a * 10 + (b.toNat - 240)) % 100000000000 := by omega
      rw [e, ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
  have := key bs hb 0
  simpa [jkey, cp037Str, Cobol.Digits.ofDigits] using this

theorem digitsVal_digits : ∀ (bs : List UInt8), (∀ b ∈ bs, 240 ≤ b ∧ b ≤ 249) →
    Cobol.digitsVal {} bs = some (Cobol.Digits.ofDigits 10 (bs.map fun b => b.toNat - 240)) := by
  intro bs hb
  unfold Cobol.digitsVal
  have : bs.mapM ({} : Cobol.Config).decDigit = some (bs.map fun b => b.toNat - 240) := by
    induction bs with
    | nil => rfl
    | cons b l ih =>
      simp only [List.mapM_cons, List.map_cons]
      rw [decDigit_of_digit b (hb b (List.mem_cons_self ..)),
        ih (fun x hx => hb x (List.mem_cons_of_mem _ hx))]
      rfl
  rw [this]; rfl

theorem zonedParts_digits (init : List UInt8) (last : UInt8) (hdi : ∀ b ∈ init, 240 ≤ b ∧ b ≤ 249)
    (hdl : 240 ≤ last ∧ last ≤ 249) :
    Cobol.zonedParts {} { digits := init.length + 1 } (init ++ [last]) =
      some (false, Cobol.Digits.ofDigits 10 (init.map fun b => b.toNat - 240) * 10 + (last.toNat - 240)) := by
  have h1 : ({} : Cobol.Config).decUnsLast last = some (last.toNat - 240) := by
    unfold Cobol.Config.decUnsLast; rw [decDigit_of_digit last hdl]
  unfold Cobol.zonedParts
  simp [Cobol.splitLast_append_singleton, h1, digitsVal_digits init hdi]

theorem fitNum11 (N : Nat) :
    (Cobol.Sem.fitNum {} { digits := 11 } (N : Int)).2 = ((N % 100000000000 : Nat) : Int) := by
  have hfb : Cobol.NumFmt.fullBinary {} { digits := 11 } = false := rfl
  simp only [Cobol.Sem.fitNum, hfb, Bool.false_eq_true, ↓reduceIte, Cobol.Sem.fitDec, Cobol.truncDigits,
    Int.natAbs_natCast, Nat.reducePow]
  split
  · omega
  · split <;> omega

/-- **The key loop computes `acctVal`** on a key of CP037 digits. -/
theorem acctVal_eq (key : List UInt8) (k : Nat) (hk : 1 ≤ k) (hlen : (key.take k).length = k)
    (hd : ∀ b ∈ key.take k, 240 ≤ b ∧ b ≤ 249) :
    Model.acctVal key k = ((Cobol.Digits.ofDigits 10 ((key.take k).map fun b => b.toNat - 240) %
      100000000000 : Nat) : Int) := by
  have hne : key.take k ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨init, last, hsplit⟩ : ∃ init last, key.take k = init ++ [last] :=
    ⟨_, _, (List.dropLast_append_getLast hne).symm⟩
  have hdi : ∀ b ∈ init, 240 ≤ b ∧ b ≤ 249 := fun b hb => hd b (by rw [hsplit]; exact List.mem_append_left _ hb)
  have hdl : 240 ≤ last ∧ last ≤ 249 :=
    hd last (by rw [hsplit]; exact List.mem_append_right _ (List.mem_singleton_self _))
  have hil : init.length + 1 = k := by rw [← hlen, hsplit, List.length_append, List.length_singleton]
  have hval : Cobol.Digits.ofDigits 10 ((key.take k).map fun b => b.toNat - 240) =
      Cobol.Digits.ofDigits 10 (init.map fun b => b.toNat - 240) * 10 + (last.toNat - 240) := by
    rw [hsplit, List.map_append, List.map_singleton, Cobol.Digits.ofDigits_append_singleton]
  have hlt : Cobol.Digits.ofDigits 10 ((key.take k).map fun b => b.toNat - 240) < 10 ^ k := by
    have := Cobol.Digits.ofDigits_lt (b := 10) (by decide) ((key.take k).map fun b => b.toNat - 240) (by
      intro d hm; rw [List.mem_map] at hm; obtain ⟨b, hb, rfl⟩ := hm
      have h2 : b.toNat ≤ 249 := (hd b hb).2
      omega)
    rwa [List.length_map, hlen] at this
  have hdec : Cobol.decodeNum {} { digits := k } (key.take k) =
      some ((Cobol.Digits.ofDigits 10 ((key.take k).map fun b => b.toNat - 240) : Nat) : Int) := by
    rw [hval] at hlt ⊢
    rw [hsplit]
    subst hil
    unfold Cobol.decodeNum
    dsimp only
    rw [if_neg (Nat.succ_ne_zero _)]
    unfold Cobol.decZoned
    rw [zonedParts_digits init last hdi hdl]
    dsimp only
    rw [if_pos ⟨hlt, rfl⟩]
    rfl
  unfold Model.acctVal
  rw [hdec, Option.getD_some, fitNum11]

/-- The key loop's value on the key's first `k` characters is `acctVal`. -/
theorem jkey_eq_acctVal (key : List UInt8) (k : Nat) (hk : 1 ≤ k) (hlen : (key.take k).length = k)
    (hd : ∀ b ∈ key.take k, 240 ≤ b ∧ b ≤ 249) :
    Model.acctVal key k = (jkey (cp037Str (key.take k)) : Int) := by
  rw [acctVal_eq key k hk hlen hd, jkey_digits _ hd]

end EquivLean.Modernize.Cbstm03b.Java.AcctP
