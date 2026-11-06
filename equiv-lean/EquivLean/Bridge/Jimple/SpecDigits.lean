import EquivLean.Bridge.Jimple.SpecCalls
import EquivLean.Bridge.Jimple.CobolRec

/-!
# Record and digit helpers of the CardDemo translations

`jrec_flat h hv` turns a record object (`JRecAt`) holding a valid record into its fields' facts,
one hypothesis per field, for the VC generator.

`zeroPad(v, n)`/`fmtNum(v, n)` fill a `char[n]` from the right with the decimal digits of `v`
(`buf[i] = (char) ('0' + v % 10); v /= 10`) and return `new String(buf)`: the text is
`zpad n v` (`EquivLean.Cobol.Rec`). The lemmas below are what a loop invariant over that buffer
needs: the buffer at index `k` (`zpBuf`: zeros, then the digits written so far), one step of the
loop (`zpBuf_step`: the Java digit and the `long` division), entry and exit.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Jimple.Spec

/-! ## Zero-padded digits -/

theorem toDigits_succ_front (j v : Nat) :
    Cobol.Digits.toDigits 10 (j + 1) v = (v / 10 ^ j % 10) :: Cobol.Digits.toDigits 10 j v := by
  induction j generalizing v with
  | zero => simp [Cobol.Digits.toDigits]
  | succ j ih =>
    rw [Cobol.Digits.toDigits, ih (v / 10), Cobol.Digits.toDigits]
    simp [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem zpad_succ_front (j v : Nat) : zpad (j + 1) v = (48 + v / 10 ^ j % 10) :: zpad j v := by
  simp [zpad, toDigits_succ_front]

theorem set_replicate_append {α : Type} (x y : α) (L : List α) :
    ∀ k : Nat, (List.replicate (k + 1) x ++ L).set k y = List.replicate k x ++ y :: L
  | 0 => by simp
  | k + 1 => by
    rw [List.replicate_succ, List.cons_append, List.set_cons_succ, set_replicate_append x y L k,
      List.replicate_succ, List.cons_append]

/-- The Java digit: `(char) ('0' + (int) (w % 10))`, stored into a `char[]`. -/
theorem jdigit (w : I64) (hw : 0 ≤ w.toInt) :
    JInt.toChar (JInt.toChar (48#32 + JLong.toInt (w.srem 10#64))) =
      BitVec.ofNat 32 (48 + w.toInt.toNat % 10) := by
  have key : ∀ d, d < 10 →
      JInt.toChar (JInt.toChar (48#32 + JLong.toInt (BitVec.ofNat 64 d))) = BitVec.ofNat 32 (48 + d) := by
    decide
  have hs : w.srem 10#64 = BitVec.ofNat 64 (w.toInt.toNat % 10) := by
    apply BitVec.eq_of_toInt_eq
    have h10 : (10#64).toInt = 10 := by decide
    rw [BitVec.toInt_srem, Int.tmod_eq_emod_of_nonneg hw, h10, BitVec.toInt_ofNat']
    have : ((w.toInt.toNat % 10 : Nat) : Int) = w.toInt % 10 := by omega
    rw [this, Jimple.bmod64_of_bounds] <;> omega
  rw [hs]
  exact key _ (Nat.mod_lt _ (by decide))

/-- The same with one `(char)` cast: the form `jvc` leaves when its simp set merges the two casts
(`JInt.toChar_toChar`, JimpleLean 1546Z). -/
theorem jdigit1 (w : I64) (hw : 0 ≤ w.toInt) :
    JInt.toChar (48#32 + JLong.toInt (w.srem 10#64)) = BitVec.ofNat 32 (48 + w.toInt.toNat % 10) := by
  have key : ∀ d, d < 10 →
      JInt.toChar (48#32 + JLong.toInt (BitVec.ofNat 64 d)) = BitVec.ofNat 32 (48 + d) := by
    decide
  have hs : w.srem 10#64 = BitVec.ofNat 64 (w.toInt.toNat % 10) := by
    apply BitVec.eq_of_toInt_eq
    have h10 : (10#64).toInt = 10 := by decide
    rw [BitVec.toInt_srem, Int.tmod_eq_emod_of_nonneg hw, h10, BitVec.toInt_ofNat']
    have : ((w.toInt.toNat % 10 : Nat) : Int) = w.toInt % 10 := by omega
    rw [this, Jimple.bmod64_of_bounds] <;> omega
  rw [hs]
  exact key _ (Nat.mod_lt _ (by decide))

theorem jsdiv10 (w : I64) (hw : 0 ≤ w.toInt) : (w.sdiv 10#64).toInt = w.toInt / 10 := by
  rw [BitVec.toInt_sdiv]
  have h10 : (10#64).toInt = 10 := by decide
  rw [h10, Int.tdiv_eq_ediv_of_nonneg hw]
  have h1 := i64_toInt_le w
  rw [Jimple.bmod64_of_bounds] <;> omega

theorem charsOf_digits (L : List Nat) :
    Native.charsOf (L.map fun c => Value.int (BitVec.ofNat 32 c)) = L.map (BitVec.ofNat 16) := by
  simp only [Native.charsOf, List.map_map]
  apply List.map_congr_left
  intro c _
  apply BitVec.eq_of_toNat_eq
  simp


/-- The buffer of `zeroPad(v, n)` when the index is `k`: zeros up to `k`, then the digits of
the positions already written. -/
def zpBuf (v : Nat) (n k : Int) : List Value :=
  List.replicate (k + 1).toNat (.int 0#32) ++
    (zpad (n - 1 - k).toNat v).map fun c => Value.int (BitVec.ofNat 32 c)

theorem zpBuf_init (v : Nat) {n : Int} (hn : 0 ≤ n) :
    zpBuf v n (n - 1) = List.replicate n.toNat (.int 0#32) := by
  have e1 : (n - 1 + 1).toNat = n.toNat := by omega
  have e2 : (n - 1 - (n - 1)).toNat = 0 := by omega
  simp only [zpBuf, e1, e2, zpad, Cobol.Digits.toDigits, List.map_nil, List.append_nil]

theorem zpBuf_length (v : Nat) {n k : Int} (h1 : -1 ≤ k) (h2 : k < n) :
    (zpBuf v n k).length = n.toNat := by
  simp only [zpBuf, List.length_append, List.length_replicate, List.length_map, zpad,
    Cobol.Digits.length_toDigits]
  omega

theorem charsOf_zpBuf_done (v : Nat) {n k : Int} (h1 : -1 ≤ k) (h2 : k < 0) :
    Native.charsOf (zpBuf v n k) = (zpad n.toNat v).map (BitVec.ofNat 16) := by
  have e1 : (k + 1).toNat = 0 := by omega
  have e2 : (n - 1 - k).toNat = n.toNat := by omega
  rw [zpBuf, e1, e2, List.replicate_zero, List.nil_append, charsOf_digits]

theorem toNat_ediv_pow10 {v : Int} (hv : 0 ≤ v) (m : Nat) : (v / 10 ^ m).toNat = v.toNat / 10 ^ m := by
  obtain ⟨V, rfl⟩ := Int.eq_ofNat_of_zero_le hv
  rw [show ((10 : Int) ^ m) = ((10 ^ m : Nat) : Int) by simp, ← Int.natCast_ediv, Int.toNat_natCast,
    Int.toNat_natCast]

theorem zpBuf_step {v : Int} {n k : Int} {w : I64} (hv : 0 ≤ v) (h0 : 0 ≤ k) (hk : k < n)
    (hw0 : 0 ≤ w.toInt) (hw : w.toInt = v / 10 ^ (n - 1 - k).toNat) :
    (zpBuf v.toNat n k).set k.toNat
        (.int (JInt.toChar (JInt.toChar (48#32 + JLong.toInt (w.srem 10#64))))) =
      zpBuf v.toNat n (k + -1) := by
  rw [jdigit w hw0, hw, toNat_ediv_pow10 hv]
  have e1 : (k + 1).toNat = k.toNat + 1 := by omega
  have e2 : (k + -1 + 1).toNat = k.toNat := by omega
  have e3 : (n - 1 - (k + -1)).toNat = (n - 1 - k).toNat + 1 := by omega
  rw [zpBuf, zpBuf, e1, e2, e3, set_replicate_append, zpad_succ_front, List.map_cons]

/-- `zpBuf_step` with one `(char)` cast (see `jdigit1`). -/
theorem zpBuf_step1 {v : Int} {n k : Int} {w : I64} (hv : 0 ≤ v) (h0 : 0 ≤ k) (hk : k < n)
    (hw0 : 0 ≤ w.toInt) (hw : w.toInt = v / 10 ^ (n - 1 - k).toNat) :
    (zpBuf v.toNat n k).set k.toNat (.int (JInt.toChar (48#32 + JLong.toInt (w.srem 10#64)))) =
      zpBuf v.toNat n (k + -1) := by
  rw [jdigit1 w hw0, hw, toNat_ediv_pow10 hv]
  have e1 : (k + 1).toNat = k.toNat + 1 := by omega
  have e2 : (k + -1 + 1).toNat = k.toNat := by omega
  have e3 : (n - 1 - (k + -1)).toNat = (n - 1 - k).toNat + 1 := by omega
  rw [zpBuf, zpBuf, e1, e2, e3, set_replicate_append, zpad_succ_front, List.map_cons]

theorem zp_pow_pred (V : Nat) {n k : Int} (hk : k < n) :
    V / 10 ^ (n - 1 - (k + -1)).toNat = V / 10 ^ (n - 1 - k).toNat / 10 := by
  have e3 : (n - 1 - (k + -1)).toNat = (n - 1 - k).toNat + 1 := by omega
  rw [e3, Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem zp_pow_pred_int (V : Int) {n k : Int} (hk : k < n) :
    V / 10 ^ (n - 1 - (k + -1)).toNat = V / 10 ^ (n - 1 - k).toNat / 10 := by
  have e3 : (n - 1 - (k + -1)).toNat = (n - 1 - k).toNat + 1 := by omega
  rw [e3, Int.pow_succ, Int.ediv_ediv_of_nonneg (Int.pow_nonneg (by decide))]

theorem zp_pow_init (V : Int) (n : Int) : V / 10 ^ (n - 1 - (n - 1)).toNat = V := by
  simp

theorem zpBuf_done (v : Nat) {n k : Int} (h1 : -1 ≤ k) (h2 : k < 0) :
    zpBuf v n k = (zpad n.toNat v).map fun c => Value.int (BitVec.ofNat 32 c) := by
  have e1 : (k + 1).toNat = 0 := by omega
  have e2 : (n - 1 - k).toNat = n.toNat := by omega
  rw [zpBuf, e1, e2, List.replicate_zero, List.nil_append]

/-! ## Record objects, field by field -/

theorem forall2_cons_inv {α β : Type} {R : α → β → Prop} {a : α} {l : List α} {v : List β}
    (h : Forall2 R (a :: l) v) : ∃ b bs, v = b :: bs ∧ R a b ∧ Forall2 R l bs := by
  cases h with | cons hab h' => exact ⟨_, _, rfl, hab, h'⟩

theorem forall2_cons_cons {α β : Type} {R : α → β → Prop} {a : α} {l : List α} {b : β}
    {bs : List β} (h : Forall2 R (a :: l) (b :: bs)) : R a b ∧ Forall2 R l bs := by
  cases h with | cons hab h' => exact ⟨hab, h'⟩

theorem forall2_nil_inv {α β : Type} {R : α → β → Prop} {v : List β}
    (h : Forall2 R ([] : List α) v) : v = [] := by
  cases h; rfl

/-- An alphanumeric field of a record object: a string reference to the CP037 text. -/
theorem jfield_alnum {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)} {f : Field}
    {j : Bool} {w : EquivLean.Cobol.Rec.FVal} (hk : f.desc.kind = .alnum j) (he : jFieldAt σ cls fs f w)
    (hv : f.Valid w) : ∃ bs x, w = .str bs ∧ Fields.get fs (cls, f.jname) = some (.ref x) ∧
      σ.heap x = some (.str (cp037Str bs)) ∧ bs.length = f.desc.len := by
  cases w with
  | num n => obtain ⟨fmt, hk', -⟩ := hv; rw [hk] at hk'; cases hk'
  | str bs =>
    obtain ⟨s, hs, x, rfl, hx⟩ := he
    exact ⟨bs, x, rfl, hs, hx, hv.2⟩

/-- An unsigned DISPLAY numeric field: a `long` holding the value, `0 ≤ n < 10^digits`. -/
theorem jfield_num {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)} {f : Field}
    {d : Nat} {w : EquivLean.Cobol.Rec.FVal} (hk : f.desc.kind = .num { digits := d })
    (he : jFieldAt σ cls fs f w) (hv : f.Valid w) : ∃ n, w = .num n ∧
      Fields.get fs (cls, f.jname) = some (.long (BitVec.ofInt 64 n)) ∧ 0 ≤ n ∧
      n.natAbs < 10 ^ d ∧ d ≤ 18 := by
  cases w with
  | str bs => obtain ⟨⟨j, hk'⟩, -⟩ := hv; rw [hk] at hk'; cases hk'
  | num n =>
    obtain ⟨fmt, hk', hd0, hd, hh, -⟩ := hv
    rw [hk] at hk'; cases hk'
    simp [Cobol.NumFmt.Holds, Cobol.NumFmt.fullBinary] at hh hd
    exact ⟨n, rfl, he, hh.2, hh.1, hd⟩

/-- The `long` of a numeric field holds its value. -/
theorem toInt_ofInt64_of_digits {n : Int} {d : Nat} (h0 : 0 ≤ n) (h1 : n.natAbs < 10 ^ d)
    (hd : d ≤ 18) : (BitVec.ofInt 64 n).toInt = n := by
  have h2 : 10 ^ d ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) hd
  rw [BitVec.toInt_ofInt]; exact Jimple.bmod64_of_bounds (by omega) (by omega)

theorem jrec_step {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)} {f : Field}
    {l : List Field} {v : List EquivLean.Cobol.Rec.FVal}
    (h : Forall2 (fun f val => jFieldAt σ cls fs f val) (f :: l) v)
    (hv : Forall2 Field.Valid (f :: l) v) :
    ∃ w v', v = w :: v' ∧ jFieldAt σ cls fs f w ∧ f.Valid w ∧
      Forall2 (fun f val => jFieldAt σ cls fs f val) l v' ∧ Forall2 Field.Valid l v' := by
  cases h with
  | cons e h' => cases hv with
    | cons ev hv' => exact ⟨_, _, rfl, e, ev, h', hv'⟩

theorem jrec_nil {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)}
    {v : List EquivLean.Cobol.Rec.FVal}
    (h : Forall2 (fun f val => jFieldAt σ cls fs f val) [] v) : v = [] := by
  cases h; rfl

set_option hygiene false in
/-- One field of `jrec_flat`. -/
macro "jrec_flat_step" h:ident hv:ident : tactic => `(tactic| (
    have jrec_hstep := EquivLean.Jimple.Spec.jrec_step $h $hv
    clear $h:ident $hv:ident
    obtain ⟨_, _, rfl, jrec_e, jrec_ev, $h:ident, $hv:ident⟩ := jrec_hstep
    first
      | obtain ⟨_, _, rfl, _, _, _⟩ := EquivLean.Jimple.Spec.jfield_alnum rfl jrec_e jrec_ev
      | obtain ⟨_, rfl, _, _, _, _⟩ := EquivLean.Jimple.Spec.jfield_num rfl jrec_e jrec_ev
    clear jrec_e jrec_ev))

set_option hygiene false in
/-- `jrec_flat h hv`: for `h : Forall2 (fun f val => jFieldAt σ cls fs f val) fields vals` and
`hv : Forall2 Field.Valid fields vals` over a concrete field list, the values field by field:
`vals` becomes a list of `.str bs`/`.num n`, with the field's reference and string (alphanumeric)
or `long` and bounds (unsigned DISPLAY numeric) as hypotheses. -/
macro "jrec_flat" h:ident hv:ident : tactic => `(tactic| (
  simp only at $h:ident $hv:ident
  repeat jrec_flat_step $h $hv
  have jrec_hnil := EquivLean.Jimple.Spec.jrec_nil $h
  subst jrec_hnil
  clear $h:ident $hv:ident
  try simp only at *))

end EquivLean.Jimple.Spec
