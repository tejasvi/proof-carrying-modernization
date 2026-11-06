import EquivLean.Modernize.Cbtrn02c.Any.JavaRunLib

/-!
# CBTRN02C → Java: the searches `findTcatbal`, `findKey`

Searches of `ArrayList`s: the first index whose key fields hold the key, or `-1` (`firstIdx`);
the state is unchanged.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-! ### `findTcatbal` -/

abbrev tcAcctKey : FieldKey := ("Cbtrn02c$TranCatBalRecord", "trancatAcctId")
abbrev tcTypeKey : FieldKey := ("Cbtrn02c$TranCatBalRecord", "trancatTypeCd")
abbrev tcCdKey : FieldKey := ("Cbtrn02c$TranCatBalRecord", "trancatCd")

/-- Every element of `xs` is a category balance object with its key fields. -/
def TcatShapes (σ : State) (xs : List Value) : Prop :=
  ∀ v ∈ xs, ∃ x fs a ts tcs c, v = .ref x ∧
    σ.heap x = some (.plain "Cbtrn02c$TranCatBalRecord" fs) ∧
    Fields.get fs tcAcctKey = some (.long a) ∧ Fields.get fs tcTypeKey = some (.ref ts) ∧
    σ.heap ts = some (.str tcs) ∧ Fields.get fs tcCdKey = some (.long c)

/-- The key test of `findTcatbal`. -/
def tcMatch (σ : State) (acct : I64) (tcs : JStr) (cd : I64) (v : Value) : Bool :=
  longFieldOf σ tcAcctKey v == some acct && strFieldOf σ tcTypeKey v == some tcs &&
    longFieldOf σ tcCdKey v == some cd

abbrev findTcatbalRef : MethodRef :=
  Gen.Cbtrn02c.«findTcatbal(java.util.List,long,java.lang.String,long)».ref

def findTcatbalSpec : Spec := Spec.of
  (fun args σ => ∃ (f : Addr) (acct : I64) (ty : Addr) (cd : I64) (lk : ListKind)
       (xs : List Value) (m : Nat) (tcs : JStr),
     args = [.ref f, .long acct, .ref ty, .long cd] ∧ σ.heap f = some (.list lk xs m) ∧
     xs.length < 2147483648 ∧ σ.heap ty = some (.str tcs) ∧ TcatShapes σ xs)
  (fun args σ r σ' => ∀ (f : Addr) (acct : I64) (ty : Addr) (cd : I64) (lk : ListKind)
       (xs : List Value) (m : Nat) (tcs : JStr),
     args = [.ref f, .long acct, .ref ty, .long cd] → σ.heap f = some (.list lk xs m) →
     σ.heap ty = some (.str tcs) →
     r = some (.int (BitVec.ofInt 32 (firstIdx (tcMatch σ acct tcs cd) xs))) ∧ σ' = σ)

/-- At the loop head (statement 5): no element before `i` matches. -/
def findTcatbalInv : Invariants := [(5, fun args σ0 fr σ =>
  ∀ (f : Addr) (acct : I64) (ty : Addr) (cd : I64) (lk : ListKind) (xs : List Value) (m : Nat)
    (tcs : JStr),
  args = [.ref f, .long acct, .ref ty, .long cd] → σ0.heap f = some (.list lk xs m) →
  σ0.heap ty = some (.str tcs) →
  ∃ i : I32, fr.get 4 = some (.ref f) ∧ fr.get 1 = some (.long acct) ∧
    fr.get 9 = some (.ref ty) ∧ fr.get 2 = some (.long cd) ∧ fr.get 7 = some (.int i) ∧
    σ = σ0 ∧ 0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧ NoMatch (tcMatch σ0 acct tcs cd) xs i.toInt.toNat)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findTcatbal_vc :
    MethodVC Gen.prog (fun _ => none) 0 findTcatbalRef findTcatbalSpec findTcatbalInv 40 := by
  jverify [findTcatbalSpec, findTcatbalInv, TcatShapes, noMatch_zero]
  all_goals first
    | exact exit_idx _ _ _ (by assumption) (by assumption) (by assumption)
    | (apply found_idx _ _ _ (by assumption) (by assumption) _ (by assumption)
       intro h
       simp_all [tcMatch, longFieldOf, strFieldOf, jlong_cmp_eq_zero])
    | (apply noMatch_succ _ _ _ (by assumption) (by assumption)
       intro h
       simp_all [tcMatch, longFieldOf, strFieldOf, jlong_cmp_eq_zero] <;>
         first
           | exact Ne.symm (by assumption)
           | (intro h; subst h; omega)
           | (intro h; exact absurd h.symm (by assumption))
           | omega)

/-! ### `findKey` -/

/-- Every element of `xs` is a string. -/
def StrShapes (σ : State) (xs : List Value) : Prop :=
  ∀ v ∈ xs, ∃ s cs, v = .ref s ∧ σ.heap s = some (.str cs)

abbrev findKeyRef : MethodRef := Gen.Cbtrn02c.«findKey(java.util.List,java.lang.String)».ref

def findKeySpec : Spec := Spec.of
  (fun args σ => ∃ (f k : Addr) (lk : ListKind) (xs : List Value) (m : Nat) (kcs : JStr),
     args = [.ref f, .ref k] ∧ σ.heap f = some (.list lk xs m) ∧ xs.length < 2147483648 ∧
     σ.heap k = some (.str kcs) ∧ StrShapes σ xs)
  (fun args σ r σ' => ∀ (f k : Addr) (lk : ListKind) (xs : List Value) (m : Nat) (kcs : JStr),
     args = [.ref f, .ref k] → σ.heap f = some (.list lk xs m) → σ.heap k = some (.str kcs) →
     r = some (.int (BitVec.ofInt 32 (firstIdx (fun v => strOfV σ v == some kcs) xs))) ∧ σ' = σ)

/-- At the loop head (statement 3): no element before `i` matches. -/
def findKeyInv : Invariants := [(3, fun args σ0 fr σ =>
  ∀ (f k : Addr) (lk : ListKind) (xs : List Value) (m : Nat) (kcs : JStr),
  args = [.ref f, .ref k] → σ0.heap f = some (.list lk xs m) → σ0.heap k = some (.str kcs) →
  ∃ i : I32, fr.get 0 = some (.ref f) ∧ fr.get 4 = some (.ref k) ∧ fr.get 2 = some (.int i) ∧
    σ = σ0 ∧ 0 ≤ i.toInt ∧ i.toInt ≤ xs.length ∧
    NoMatch (fun v => strOfV σ0 v == some kcs) xs i.toInt.toNat)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findKey_vc : MethodVC Gen.prog (fun _ => none) 0 findKeyRef findKeySpec findKeyInv 40 := by
  jverify [findKeySpec, findKeyInv, StrShapes, noMatch_zero]
  all_goals first
    | exact exit_idx _ _ _ (by assumption) (by assumption) (by assumption)
    | (apply found_idx _ _ _ (by assumption) (by assumption) _ (by assumption)
       intro h
       simp_all [strOfV])
    | (apply noMatch_succ _ _ _ (by assumption) (by assumption)
       intro h
       simp_all [strOfV] <;> exact Ne.symm (by assumption))

end EquivLean.Modernize.Cbtrn02c.Java
