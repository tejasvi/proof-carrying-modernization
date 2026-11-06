import EquivLean.Modernize.Cbact04c.JavaRunLib

/-!
# CBACT04C → Java: the arithmetic and string helpers

Contracts of `pow10`, `trunc`, `fmtU`, `spaces` and `fixLen`, each proved once with `jverify`
against the contracts of its callees.
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java

theorem targets_static {P : Program} {sig : MethodSig} {m : MethodRef}
    (h : P.selectStatic sig = .jimple m) (hb : m.decl.body.isSome = true) : Targets P sig m :=
  ⟨Or.inl h, hb⟩

/-! ## `pow10` -/

abbrev pow10Ref : MethodRef := Gen.Cbact04c.«pow10(int)».ref

def pow10Spec : Spec := Spec.of
  (fun args _ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 18)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     r = some (.long (BitVec.ofNat 64 (10 ^ n.toInt.toNat))) ∧ σ' = σ)

def pow10Inv : Invariants := [(3, fun args σ0 fr σ => ∀ n : I32, args = [.int n] →
  ∃ i : I32, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧
    fr.get 2 = some (.long (BitVec.ofNat 64 (10 ^ i.toInt.toNat))) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ = σ0)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pow10_vc : MethodVC Gen.prog (fun _ => none) 0 pow10Ref pow10Spec pow10Inv 30 := by
  jverify [pow10Spec, pow10Inv]

def pow10Sig : MethodSig :=
  { cls := "Cbact04c", ret := .prim .long, name := "pow10", params := [.prim .int] }

/-! ## `trunc` -/

abbrev truncRef : MethodRef := Gen.Cbact04c.«trunc(long,int)».ref

def truncSpec : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 18 ∧
     σ.initOf "Cbact04c" = .done)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     r = some (.long (v.srem (BitVec.ofNat 64 (10 ^ n.toInt.toNat)))) ∧ σ' = σ)

def truncC : Contracts := [(pow10Sig, pow10Spec)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem trunc_vc : MethodVC Gen.prog truncC.env 0 truncRef truncSpec [] 30 := by
  jverify [truncSpec, truncC, pow10Sig, pow10Spec, ofNat_pow10_eq_zero_iff]
  all_goals exact targets_static rfl rfl

/-! ## `fmtU` -/

abbrev fmtURef : MethodRef := Gen.Cbact04c.«fmtU(long,int)».ref

/-- `fmtU v n`: the last `n` digits of `|v|`. -/
def fmtUSpec : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧ 1 ≤ n.toInt ∧ n.toInt ≤ 18 ∧
     -9223372036854775808 < v.toInt ∧ σ.initOf "Cbact04c" = .done)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (zpadJ v.toInt.natAbs n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the loop head (statement 12): positions `i+1 …` of the array hold the digits written so
far, and the rest of the number is `a`. -/
def fmtUInv : Invariants := [(12, fun args σ0 fr σ => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
  ∃ arr i a xs, fr.get 4 = some (.int i) ∧ fr.get 1 = some (.long a) ∧ fr.get 6 = some (.ref arr) ∧
    σ.heap arr = some (.array (.prim .char) xs) ∧ xs.length = n.toInt.toNat ∧
    0 ≤ a.toInt ∧ -1 ≤ i.toInt ∧ i.toInt < n.toInt ∧
    zpadJ v.toInt.natAbs n.toInt.toNat =
      zpadJ a.toNat (i.toInt + 1).toNat ++ Native.charsOf (xs.drop (i.toInt + 1).toNat) ∧
    σ0.next ≤ arr ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

def fmtUC : Contracts := [(pow10Sig, pow10Spec)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem fmtU_vc : MethodVC Gen.prog fmtUC.env 0 fmtURef fmtUSpec fmtUInv 60 := by
  jverify [fmtUSpec, fmtUInv, fmtUC, pow10Sig, pow10Spec, Grows, zpadJ, digitJ,
    sdiv10_toNat_of_nonneg, sdiv10_nonneg, digit_char, drop_set_self, cmp_zero_nonneg_iff,
    ofNat_pow10_eq_zero_iff, zpadJ_srem_pos, zpadJ_srem_neg, srem_pow10_nonneg_pos,
    srem_pow10_nonneg_neg, toNat_add_one_of_neg, int_add_neg_one_add_one, toChar_toChar,
    charsOf_cons, charsOf_nil]
  all_goals exact targets_static rfl rfl

/-! ## `spaces` -/

abbrev spacesRef : MethodRef := Gen.Cbact04c.«spaces(int)».ref

def spacesSpec : Spec := Spec.of
  (fun args _ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 1000)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (spJ n.toInt.toNat)) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the loop head (statement 4): the builder holds `i` spaces. -/
def spacesInv : Invariants := [(4, fun args σ0 fr σ => ∀ n : I32, args = [.int n] →
  ∃ sb i, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧ fr.get 2 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (spJ i.toInt.toNat)) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_vc : MethodVC Gen.prog (fun _ => none) 0 spacesRef spacesSpec spacesInv 60 := by
  jverify [spacesSpec, spacesInv, Grows, spJ_succ, valueOfArg_char]

/-! ## `fixLen` (on a string of the length asked) -/

abbrev fixLenRef : MethodRef := Gen.Cbact04c.«fixLen(java.lang.String,int)».ref

def fixLenSpec : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (n : I32) (s : JStr), args = [.ref x, .int n] ∧
     σ.heap x = some (.str s) ∧ s.length = n.toInt.toNat ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 1000)
  (fun args σ r σ' => ∀ (x : Addr) (n : I32) (s : JStr), args = [.ref x, .int n] →
     σ.heap x = some (.str s) →
     ∃ y, r = some (.ref y) ∧ σ'.heap y = some (.str s) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem fixLen_vc : MethodVC Gen.prog (fun _ => none) 0 fixLenRef fixLenSpec [] 60 := by
  jverify [fixLenSpec, Grows]

end EquivLean.Modernize.Cbact04c.Java
