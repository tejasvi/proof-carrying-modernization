import EquivLean.Demo.Thrift.Java.Rv32P

/-!
# Thrift → Java (T4): the varint methods as contracts of the callers

The field and list headers call `readVarint32()` / `writeVarint32(int)` (private, through
`readI16`/`writeI16`). Their bodies have loops, which a caller cannot execute inline, so the callers
use the proved contracts. JimpleLean's `Valid` asks a contract of an instance method to hold for
every application subclass as well (`VSat`), so the callers' theorems assume `NoRedecl`: no
application subclass of `TCompactProtocol` declares a method of the same signature (true of the
Thrift library: its only subclass `TTupleProtocol` does not).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

def rv32Sig : MethodSig := ⟨cpCls, .prim .int, "readVarint32", []⟩
def wv32Sig : MethodSig := ⟨cpCls, .void, "writeVarint32", [.prim .int]⟩

/-- No application subclass of `TCompactProtocol` redeclares `sig`: virtual selection gives `m`. -/
def NoRedecl (P : Program) (sig : MethodSig) (m : MethodRef) : Prop :=
  ∀ c, P.isProgClass c = true → P.isSubclass c cpCls = some true → P.selectVirtual c sig.sub = .jimple m

/-- `readVarint32()`'s results, with the protocol object named by its fields (premises the symbolic
execution instantiates). -/
def rv32NA (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)), args = [.ref p] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    ∃ v rest, Spec.readVarint 5 (R.src σ t) = some (v, rest) ∧ r = some (.int (BitVec.ofNat 32 v)) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ CPAtH P R σ' p t tmp ∧ PFrame R σ σ' t tmp ∧
      OwnsMono R σ σ' t

def rv32EA (P : Program) (R : TRep) (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)), args = [.ref p] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    (Spec.VarintOverlong 5 (R.src σ t) ∧ ∃ fs, σ'.heap e = some (.plain tpeCls fs)) ∨
    (Spec.VarintTruncated 5 (R.src σ t) ∧ ∃ fs, σ'.heap e = some (.plain ttExcCls fs))

def rv32SpecA (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr), args = [.ref p] ∧ CPAt P R σ p t tmp ∧ σ.initOf tpeCls = .done)
  (rv32NA P R) (rv32EA P R)

/-- `writeVarint32(n)`'s results, with the protocol object named by its fields. -/
def wv32NA (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (n : I32), args = [.ref p, .int n] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) →
    r = none ∧ CPAtH P R σ' p t tmp ∧ R.sink σ' t = R.sink σ t ++ Spec.varint n.toNat ∧
      R.src σ' t = R.src σ t ∧ PFrame R σ σ' t tmp

def wv32SpecA (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp : Addr) (n : I32), args = [.ref p, .int n] ∧ CPAt P R σ p t tmp)
  (wv32NA P R)
  (fun _ _ _ _ => False)

/-- The fields of the protocol object name its transport and scratch array. -/
theorem cpAt_fields {P : Program} {R : TRep} {σ : State} {p t tmp t' tmp' : Addr}
    {fs : List (FieldKey × Value)} (h : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (htr : Fields.get fs (tpCls, "trans_") = some (.ref t'))
    (hte : Fields.get fs (cpCls, "temp") = some (.ref tmp')) : t' = t ∧ tmp' = tmp := by
  obtain ⟨fs0, -, -, -, hp0, htr0, hte0, -⟩ := h
  rw [hp0] at hp
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp
  subst hp
  rw [htr0] at htr
  rw [hte0] at hte
  simp only [Option.some.injEq, Value.ref.injEq] at htr hte
  exact ⟨htr.symm, hte.symm⟩

theorem rv32A_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC])
    (hV : Valid P (tContracts R).env) : Sat P rv32Ref (rv32SpecA P R) := by
  intro args σ o hpre hm
  have hpost := rv32_sat R hF hV args σ o hpre hm
  obtain ⟨p, t, tmp, hargs, hCP, -⟩ := hpre
  subst hargs
  cases o with
  | normal r σ' =>
    simp only [rv32Spec, rv32SpecA, Spec.of] at hpost ⊢
    unfold rv32N at hpost
    intro p' t' tmp' fs hargs hp htr hte
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    subst hargs
    obtain ⟨rfl, rfl⟩ := cpAt_fields hCP hp htr hte
    obtain ⟨v, rest, h1, h2, h3, h4, h5, h6⟩ := hpost _ _ _ rfl hCP
    exact ⟨v, rest, h1, h2, h3, h4, CPAtH.intro h5, h6⟩
  | exc e σ' =>
    simp only [rv32Spec, rv32SpecA, Spec.of] at hpost ⊢
    unfold rv32E at hpost
    intro p' t' tmp' fs hargs hp htr hte
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    subst hargs
    obtain ⟨rfl, rfl⟩ := cpAt_fields hCP hp htr hte
    exact hpost _ _ _ rfl hCP
  | wrong msg => simp only [rv32Spec, Spec.of] at hpost

theorem wv32A_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) : Sat P wv32Ref (wv32SpecA P R) := by
  intro args σ o hpre hm
  have hpost := wv32_sat R hF hV args σ o hpre hm
  obtain ⟨p, t, tmp, n, hargs, hCP⟩ := hpre
  subst hargs
  cases o with
  | normal r σ' =>
    simp only [wv32SpecP, wv32SpecA, Spec.of] at hpost ⊢
    unfold wv32N at hpost
    intro p' t' tmp' fs n' hargs hp htr hte
    simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at hargs
    obtain ⟨rfl, rfl⟩ := hargs
    obtain ⟨rfl, rfl⟩ := cpAt_fields hCP hp htr hte
    obtain ⟨h1, h2, h3, h4, h5⟩ := hpost _ _ _ _ rfl hCP
    exact ⟨h1, CPAtH.intro h2, h3, h4, h5⟩
  | exc e σ' => simp only [wv32SpecP, Spec.of] at hpost
  | wrong msg => simp only [wv32SpecP, Spec.of] at hpost

end EquivLean.Demo.Thrift.Java
