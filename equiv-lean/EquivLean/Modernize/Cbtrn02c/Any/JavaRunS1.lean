import EquivLean.Modernize.Cbtrn02c.Any.JavaRunLib

/-!
# CBTRN02C → Java: the searches `findXref`, `findAccount`

Each returns the first index whose key field holds the key, or `-1` (`firstIdx`), read off the
objects (`strFieldOf`, `longFieldOf`); the state is unchanged.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-! ### `findXref` -/

abbrev xrefCardKey : FieldKey := ("Cbtrn02c$CardXrefRecord", "xrefCardNum")

/-- Every element of `xs` is a cross-reference object whose card number field holds a string. -/
def XrefShapes (σ : State) (xs : List Value) : Prop :=
  ∀ v ∈ xs, ∃ x fs s cs, v = .ref x ∧ σ.heap x = some (.plain "Cbtrn02c$CardXrefRecord" fs) ∧
    Fields.get fs xrefCardKey = some (.ref s) ∧ σ.heap s = some (.str cs)

abbrev findXrefRef : MethodRef := Gen.Cbtrn02c.«findXref(Cbtrn02c$CardXrefRecord[],java.lang.String)».ref

def findXrefSpec : Spec := Spec.of
  (fun args σ => ∃ (f k : Addr) (et : JType) (xs : List Value) (kcs : JStr),
     args = [.ref f, .ref k] ∧ σ.heap f = some (.array et xs) ∧ xs.length < 2147483648 ∧
     σ.heap k = some (.str kcs) ∧ XrefShapes σ xs)
  (fun args σ r σ' => ∀ (f k : Addr) (et : JType) (xs : List Value) (kcs : JStr),
     args = [.ref f, .ref k] → σ.heap f = some (.array et xs) → σ.heap k = some (.str kcs) →
     r = some (.int (BitVec.ofInt 32 (firstIdx (fun v => strFieldOf σ xrefCardKey v == some kcs) xs))) ∧
       σ' = σ)

/-- At the loop head (statement 3): no element before `i` matches. -/
def findXrefInv : Invariants := [(3, fun args σ0 fr σ =>
  ∀ (f k : Addr) (et : JType) (xs : List Value) (kcs : JStr),
  args = [.ref f, .ref k] → σ0.heap f = some (.array et xs) → σ0.heap k = some (.str kcs) →
  ∃ i : I32, fr.get 0 = some (.ref f) ∧ fr.get 4 = some (.ref k) ∧ fr.get 3 = some (.int i) ∧
    σ = σ0 ∧ 0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧
    NoMatch (fun v => strFieldOf σ0 xrefCardKey v == some kcs) xs i.toInt.toNat)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findXref_vc : MethodVC Gen.prog (fun _ => none) 0 findXrefRef findXrefSpec findXrefInv 40 := by
  jverify [findXrefSpec, findXrefInv, XrefShapes, noMatch_zero]
  all_goals first
    | exact exit_idx _ _ _ (by assumption) (by assumption) (by assumption)
    | (apply found_idx _ _ _ (by assumption) (by assumption) _ (by assumption)
       intro h
       simp_all [strFieldOf])
    | (apply noMatch_succ _ _ _ (by assumption) (by assumption)
       intro h
       simp_all [strFieldOf] <;> exact Ne.symm (by assumption))

/-! ### `findAccount` -/

abbrev acctIdKey : FieldKey := ("Cbtrn02c$AccountRecord", "acctId")

/-- Every element of `xs` is an account object with a `long` id field. -/
def AcctShapes (σ : State) (xs : List Value) : Prop :=
  ∀ v ∈ xs, ∃ x fs l, v = .ref x ∧ σ.heap x = some (.plain "Cbtrn02c$AccountRecord" fs) ∧
    Fields.get fs acctIdKey = some (.long l)

abbrev findAccountRef : MethodRef := Gen.Cbtrn02c.«findAccount(Cbtrn02c$AccountRecord[],long)».ref

def findAccountSpec : Spec := Spec.of
  (fun args σ => ∃ (f : Addr) (key : I64) (et : JType) (xs : List Value),
     args = [.ref f, .long key] ∧ σ.heap f = some (.array et xs) ∧ xs.length < 2147483648 ∧
     AcctShapes σ xs)
  (fun args σ r σ' => ∀ (f : Addr) (key : I64) (et : JType) (xs : List Value),
     args = [.ref f, .long key] → σ.heap f = some (.array et xs) →
     r = some (.int (BitVec.ofInt 32 (firstIdx (fun v => longFieldOf σ acctIdKey v == some key) xs))) ∧
       σ' = σ)

/-- At the loop head (statement 3): no element before `i` matches. -/
def findAccountInv : Invariants := [(3, fun args σ0 fr σ =>
  ∀ (f : Addr) (key : I64) (et : JType) (xs : List Value),
  args = [.ref f, .long key] → σ0.heap f = some (.array et xs) →
  ∃ i : I32, fr.get 1 = some (.ref f) ∧ fr.get 5 = some (.long key) ∧ fr.get 4 = some (.int i) ∧
    σ = σ0 ∧ 0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧
    NoMatch (fun v => longFieldOf σ0 acctIdKey v == some key) xs i.toInt.toNat)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findAccount_vc :
    MethodVC Gen.prog (fun _ => none) 0 findAccountRef findAccountSpec findAccountInv 40 := by
  jverify [findAccountSpec, findAccountInv, AcctShapes, noMatch_zero]
  all_goals first
    | exact exit_idx _ _ _ (by assumption) (by assumption) (by assumption)
    | (apply found_idx _ _ _ (by assumption) (by assumption) _ (by assumption)
       intro h
       simp_all [longFieldOf, jlong_cmp_eq_zero])
    | (apply noMatch_succ _ _ _ (by assumption) (by assumption)
       intro h
       simp_all [longFieldOf, jlong_cmp_eq_zero] <;>
         first
           | exact Ne.symm (by assumption)
           | (intro h; subst h; omega)
           | (intro h; exact absurd h.symm (by assumption))
           | omega)

end EquivLean.Modernize.Cbtrn02c.Java
