/-
# Comparing bytes whose value is only bounded

A numeric item compared with an alphanumeric one is compared through its digit characters:
`UInt8.ofNat (0xF0 + v / 10 ^ k % 10)` against, say, a space `0x40`.  The digit is symbolic,
but its byte lies in `0xF0 .. 0xF9`, which decides the comparison.  `reduceUInt8Range`
decides `a = b` and `a < b` on bytes `UInt8.ofNat n` (or literals) from intervals of the
natural numbers `n`, built from literals, `+` and `% m`.
-/
import Lean
import Cobol.Logic.Attr

namespace Cobol
open Lean Meta Simp

theorem natR_lit (n : Nat) : n ≤ n ∧ n ≤ n := ⟨Nat.le_refl n, Nat.le_refl n⟩

theorem natR_add {a b la ha lb hb : Nat} (h1 : la ≤ a ∧ a ≤ ha) (h2 : lb ≤ b ∧ b ≤ hb) :
    la + lb ≤ a + b ∧ a + b ≤ ha + hb :=
  ⟨Nat.add_le_add h1.1 h2.1, Nat.add_le_add h1.2 h2.2⟩

theorem natR_mod (x m : Nat) (hm : 0 < m) : 0 ≤ x % m ∧ x % m ≤ m - 1 :=
  ⟨Nat.zero_le _, by have := Nat.mod_lt x hm; omega⟩

theorem u8_toNat_ofNat_of_lt {a : Nat} (h : a < 256) : (UInt8.ofNat a).toNat = a := by
  simp [UInt8.toNat_ofNat]; omega

theorem u8_eq_false {a b la ha lb hb : Nat} (h1 : la ≤ a ∧ a ≤ ha) (h2 : lb ≤ b ∧ b ≤ hb)
    (hh1 : ha < 256) (hh2 : hb < 256) (hd : ha < lb ∨ hb < la) :
    (UInt8.ofNat a = UInt8.ofNat b) = False := by
  apply eq_false
  intro h
  have := congrArg UInt8.toNat h
  rw [u8_toNat_ofNat_of_lt (by omega), u8_toNat_ofNat_of_lt (by omega)] at this
  omega

theorem u8_lt_true {a b la ha lb hb : Nat} (h1 : la ≤ a ∧ a ≤ ha) (h2 : lb ≤ b ∧ b ≤ hb)
    (hh1 : ha < 256) (hh2 : hb < 256) (hd : ha < lb) :
    (UInt8.ofNat a < UInt8.ofNat b) = True := by
  apply eq_true
  rw [UInt8.lt_iff_toNat_lt, u8_toNat_ofNat_of_lt (by omega), u8_toNat_ofNat_of_lt (by omega)]
  omega

theorem u8_lt_false {a b la ha lb hb : Nat} (h1 : la ≤ a ∧ a ≤ ha) (h2 : lb ≤ b ∧ b ≤ hb)
    (hh1 : ha < 256) (hh2 : hb < 256) (hd : hb ≤ la) :
    (UInt8.ofNat a < UInt8.ofNat b) = False := by
  apply eq_false
  rw [UInt8.lt_iff_toNat_lt, u8_toNat_ofNat_of_lt (by omega), u8_toNat_ofNat_of_lt (by omega)]
  omega

/-- `[lo, hi]` and a proof of `lo ≤ e ∧ e ≤ hi` for a natural-number term. -/
partial def natRange? (e : Lean.Expr) : MetaM (Option (Nat × Nat × Lean.Expr)) := do
  if let some n ← getNatValue? e then
    return some (n, n, mkApp (mkConst ``natR_lit) e)
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    let some (la, ha, pa) ← natRange? a | return none
    let some (lb, hb, pb) ← natRange? b | return none
    return some (la + lb, ha + hb, ← mkAppM ``natR_add #[pa, pb])
  | HMod.hMod _ _ _ _ x m =>
    let some mv ← getNatValue? m | return none
    if mv == 0 then return none
    let hm ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, m])
    return some (0, mv - 1, mkApp3 (mkConst ``natR_mod) x m hm)
  | _ => return none

/-- A byte as `UInt8.ofNat n` (literals are converted): `n` and its interval. -/
def byteRange? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Nat × Nat × Lean.Expr)) := do
  let n ← match_expr e with
    | UInt8.ofNat n => pure n
    | _ =>
      if e.hasFVar || e.hasMVar then return none
      let v ← try unsafe evalExpr UInt8 (mkConst ``UInt8) e catch _ => return none
      pure (mkNatLit v.toNat)
  let some (lo, hi, pf) ← natRange? n | return none
  if hi < 256 then return some (n, lo, hi, pf) else return none

private def ltProof (a b : Nat) : MetaM Lean.Expr := do
  mkDecideProof (← mkAppM ``LT.lt #[mkNatLit a, mkNatLit b])

private def leProof (a b : Nat) : MetaM Lean.Expr := do
  mkDecideProof (← mkAppM ``LE.le #[mkNatLit a, mkNatLit b])

/-- Decide `a = b` and `a < b` on bounded bytes (at least one side not closed). -/
simproc_decl reduceUInt8Range (_) := fun e => do
  let (isEq, a, b) ← match_expr e with
    | Eq ty a b => if ty.isConstOf ``UInt8 then pure (true, a, b) else return .continue
    | LT.lt ty _ a b => if ty.isConstOf ``UInt8 then pure (false, a, b) else return .continue
    | _ => return .continue
  unless a.hasFVar || b.hasFVar do return .continue
  let some (na, la, ha, pa) ← byteRange? a | return .continue
  let some (nb, lb, hb, pb) ← byteRange? b | return .continue
  let h1 ← ltProof ha 256
  let h2 ← ltProof hb 256
  let target ← if isEq then mkEq (mkApp (mkConst ``UInt8.ofNat) na) (mkApp (mkConst ``UInt8.ofNat) nb)
    else mkAppM ``LT.lt #[mkApp (mkConst ``UInt8.ofNat) na, mkApp (mkConst ``UInt8.ofNat) nb]
  let pL ← mkAppM ``LT.lt #[mkNatLit ha, mkNatLit lb]
  let pR ← mkAppM ``LT.lt #[mkNatLit hb, mkNatLit la]
  let res ← if isEq then
      if ha < lb then
        let hd ← mkAppOptM ``Or.inl #[pL, pR, ← ltProof ha lb]
        pure (some (false, ← mkAppM ``u8_eq_false #[pa, pb, h1, h2, hd]))
      else if hb < la then
        let hd ← mkAppOptM ``Or.inr #[pL, pR, ← ltProof hb la]
        pure (some (false, ← mkAppM ``u8_eq_false #[pa, pb, h1, h2, hd]))
      else pure none
    else
      if ha < lb then pure (some (true, ← mkAppM ``u8_lt_true #[pa, pb, h1, h2, ← ltProof ha lb]))
      else if hb ≤ la then pure (some (false, ← mkAppM ``u8_lt_false #[pa, pb, h1, h2, ← leProof hb la]))
      else pure none
  let some (val, pf) := res | return .continue
  -- `pf : target = True/False`; `e` is `target` up to unfolding literals
  let pf ← mkExpectedTypeHint pf (← mkEq e (mkConst (if val then ``True else ``False)))
  let _ := target
  return .done { expr := mkConst (if val then ``True else ``False), proof? := some pf }

theorem u8_toNat_ofNat_range {a la ha : Nat} (h : la ≤ a ∧ a ≤ ha) (hh : ha < 256) :
    (UInt8.ofNat a).toNat = a := u8_toNat_ofNat_of_lt (by omega)

/-- `(UInt8.ofNat n).toNat = n` when the interval of `n` is within a byte. -/
simproc_decl reduceUInt8ToNatRange (UInt8.toNat _) := fun e => do
  let_expr UInt8.toNat x := e | return .continue
  let_expr UInt8.ofNat n := x | return .continue
  unless n.hasFVar do return .continue
  let some (_, hi, pf) ← natRange? n | return .continue
  unless hi < 256 do return .continue
  let p ← mkAppM ``u8_toNat_ofNat_range #[pf, ← ltProof hi 256]
  return .done { expr := n, proof? := some p }

theorem nat_le_true {a b la ha lb hb : Nat} (h1 : la ≤ a ∧ a ≤ ha) (h2 : lb ≤ b ∧ b ≤ hb)
    (h : ha ≤ lb) : (a ≤ b) = True := eq_true (by omega)
theorem nat_le_false {a b la ha lb hb : Nat} (h1 : la ≤ a ∧ a ≤ ha) (h2 : lb ≤ b ∧ b ≤ hb)
    (h : hb < la) : (a ≤ b) = False := eq_false (by omega)
theorem nat_lt_true {a b la ha lb hb : Nat} (h1 : la ≤ a ∧ a ≤ ha) (h2 : lb ≤ b ∧ b ≤ hb)
    (h : ha < lb) : (a < b) = True := eq_true (by omega)
theorem nat_lt_false {a b la ha lb hb : Nat} (h1 : la ≤ a ∧ a ≤ ha) (h2 : lb ≤ b ∧ b ≤ hb)
    (h : hb ≤ la) : (a < b) = False := eq_false (by omega)

/-- Decide `a ≤ b` and `a < b` on natural numbers from their intervals (digit arithmetic:
literals, `+`, `% m`), when at least one side is not closed. -/
simproc_decl reduceNatCmpRange (_) := fun e => do
  let (isLe, a, b) ← match_expr e with
    | LE.le ty _ a b => if ty.isConstOf ``Nat then pure (true, a, b) else return .continue
    | LT.lt ty _ a b => if ty.isConstOf ``Nat then pure (false, a, b) else return .continue
    | _ => return .continue
  unless a.hasFVar || b.hasFVar do return .continue
  let some (la, ha, pa) ← natRange? a | return .continue
  let some (lb, hb, pb) ← natRange? b | return .continue
  let res : Option (Bool × Lean.Expr) ← if isLe then
      if ha ≤ lb then pure (some (true, ← mkAppM ``nat_le_true #[pa, pb, ← leProof ha lb]))
      else if hb < la then pure (some (false, ← mkAppM ``nat_le_false #[pa, pb, ← ltProof hb la]))
      else pure none
    else
      if ha < lb then pure (some (true, ← mkAppM ``nat_lt_true #[pa, pb, ← ltProof ha lb]))
      else if hb ≤ la then pure (some (false, ← mkAppM ``nat_lt_false #[pa, pb, ← leProof hb la]))
      else pure none
  let some (val, pf) := res | return .continue
  return .done { expr := mkConst (if val then ``True else ``False), proof? := some pf }

end Cobol
