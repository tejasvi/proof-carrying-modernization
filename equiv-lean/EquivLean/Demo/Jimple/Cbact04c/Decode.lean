import EquivLean.Demo.Jimple.Cbact04c.Pure

/-!
# A rewritten account record, decoded

The fields a Java `Cbact04c.Account` holds (id, balance, cycle credit and debit, group), read from
an ACCOUNT-RECORD of 300 bytes (`CVACT01Y.cpy`): `decodeAcct (a.posted t) = some (jposted a t)`.
-/

open Cobol CardDemo.Cbact04c Jimple

namespace EquivLean.Demo.Cbact04c

theorem drop_app {α : Type} (l₁ l₂ : List α) (n : Nat) (h : l₁.length ≤ n) :
    (l₁ ++ l₂).drop n = l₂.drop (n - l₁.length) := by
  induction l₁ generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.cons_append, List.drop_succ_cons, List.length_cons]
      rw [ih n (by simp at h; omega)]
      congr 1
      omega

theorem take_app {α : Type} (l₁ l₂ : List α) (n : Nat) (h : l₁.length = n) :
    (l₁ ++ l₂).take n = l₁ := List.take_left' h

/-- The Java account fields of an account record: `ACCT-ID` (offset 0), `ACCT-CURR-BAL` (12),
`ACCT-CURR-CYC-CREDIT` (78), `ACCT-CURR-CYC-DEBIT` (90), `ACCT-GROUP-ID` (112, 10 bytes). -/
def decodeAcct (rec : List UInt8) : Option JAcct := do
  let id ← decodeNum {} ACCT_ID.fmt (rec.take 11)
  let bal ← decodeNum {} ACCT_CURR_BAL.fmt ((rec.drop 12).take 12)
  let cc ← decodeNum {} ACCT_CURR_CYC_CREDIT.fmt ((rec.drop 78).take 12)
  let cd ← decodeNum {} ACCT_CURR_CYC_DEBIT.fmt ((rec.drop 90).take 12)
  some ⟨BitVec.ofInt 64 id, BitVec.ofInt 64 bal, BitVec.ofInt 64 cc, BitVec.ofInt 64 cd,
    strOf ((rec.drop 112).take 10)⟩

theorem decodeAcct_posted (a : Acc) (ha : a.valid) (t : Int) :
    decodeAcct (a.posted t) = some (jposted a t) := by
  obtain ⟨hid, hid0, hs, hbal, hmid, hcc, hcd, hzip, hgrp, haf, -⟩ := ha
  have l1 : (encodeNum {} ACCT_ID.fmt a.id).length = 11 := length_encodeNum _ _ _ (by decide)
  have l2 : ∀ v, (encodeNum {} ACCT_CURR_BAL.fmt v).length = 12 := fun v => length_encodeNum _ _ _ (by decide)
  have l3 : ∀ v, (encodeNum {} ACCT_CURR_CYC_CREDIT.fmt v).length = 12 := fun v => length_encodeNum _ _ _ (by decide)
  have l4 : ∀ v, (encodeNum {} ACCT_CURR_CYC_DEBIT.fmt v).length = 12 := fun v => length_encodeNum _ _ _ (by decide)
  have d1 : decodeNum {} ACCT_ID.fmt (encodeNum {} ACCT_ID.fmt a.id) = some a.id :=
    decodeNum_encodeNum _ _ _ (by decide) (by decide) ⟨hid, fun _ => hid0⟩
  have hfit := fitNum_holds {} ACCT_CURR_BAL.fmt (a.bal + t)
  have d2 : decodeNum {} ACCT_CURR_BAL.fmt (encodeNum {} ACCT_CURR_BAL.fmt
      (Sem.fitNum {} ACCT_CURR_BAL.fmt (a.bal + t)).2) = some (Sem.fitNum {} ACCT_CURR_BAL.fmt (a.bal + t)).2 :=
    decodeNum_encodeNum _ _ _ (by decide) (by decide) hfit
  have d3 : decodeNum {} ACCT_CURR_CYC_CREDIT.fmt (encodeNum {} ACCT_CURR_CYC_CREDIT.fmt 0) = some 0 :=
    decodeNum_encodeNum _ _ _ (by decide) (by decide) ⟨by decide, fun _ => Int.le_refl _⟩
  have d4 : decodeNum {} ACCT_CURR_CYC_DEBIT.fmt (encodeNum {} ACCT_CURR_CYC_DEBIT.fmt 0) = some 0 :=
    decodeNum_encodeNum _ _ _ (by decide) (by decide) ⟨by decide, fun _ => Int.le_refl _⟩
  simp (disch := simp only [l1, l2, l3, l4, hs, hmid, hzip, hgrp]; decide) only [decodeAcct,
    Acc.posted, List.append_assoc, drop_app, l1, l2, hs, hmid, hzip, Nat.reduceSub, List.drop_zero]
  rw [take_app _ _ _ l1, d1, take_app _ _ _ (l2 _), d2, take_app _ _ _ (l3 _), d3,
    take_app _ _ _ (l4 _), d4, take_app _ _ _ hgrp]
  rfl

end EquivLean.Demo.Cbact04c
