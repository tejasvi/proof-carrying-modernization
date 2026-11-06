import EquivLean.Demo.Thrift.Java.FhRD
import EquivLean.Demo.Thrift.Java.WfbP

/-!
# Thrift → Java (T4): the field header theorems for Thrift's own program

`EquivLean.Gen.ThriftJ.prog` is the jar's class set (277 classes: the jar's 262 classes and the
15 lambda classes Soot generates). On it, `NoRedeclR` and `NoRedeclW` hold: every application
subclass of `TCompactProtocol` (the class itself and `TTupleProtocol`) selects the
`TCompactProtocol` declaration of each of the methods. Checked by kernel evaluation
(`decide +kernel`; no `native_decide`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The class whose declaration a virtual call of `sub` on `c` finds (none if abstract). -/
def chainCls (P : Program) (c : ClassName) (sub : SubSig) : Option ClassName :=
  match P.chainN P.fuel c sub false with
  | .jimple m => if m.decl.mods.isAbstract then none else some m.cls
  | _ => none

/-- Every application subclass of `TCompactProtocol` finds the `TCompactProtocol` declaration of
each signature in `subs`. -/
def noRedeclCheck (P : Program) (subs : List SubSig) : Bool :=
  P.index.toList.all fun d =>
    P.isSubclass d.name cpCls != some true || subs.all fun sub => chainCls P d.name sub == some cpCls

theorem chainN_jimple {P : Program} : ∀ (n : Nat) (c : ClassName) (sub : SubSig) (st : Bool)
    (m : MethodRef), P.chainN n c sub st = .jimple m →
    ∃ d, P.findClass m.cls = some d ∧ Program.ClassDecl.findMethod d sub st = some m.decl
  | 0, c, sub, st, m, h => by simp [Program.chainN] at h
  | n + 1, c, sub, st, m, h => by
    rw [Program.chainN.eq_2] at h
    cases hf : P.findClass c with
    | none =>
      rw [hf] at h
      simp only [] at h
      split at h <;> cases h
    | some d =>
      rw [hf] at h
      simp only [] at h
      cases hm : Program.ClassDecl.findMethod d sub st with
      | some m' =>
        rw [hm] at h
        simp only [Program.Target.jimple.injEq] at h
        subst h
        exact ⟨d, hf, hm⟩
      | none =>
        rw [hm] at h
        simp only [] at h
        cases hs : d.super with
        | some s =>
          rw [hs] at h
          exact chainN_jimple n s sub st m h
        | none =>
          rw [hs] at h
          cases h

theorem noRedecl_of_check {P : Program} {subs : List SubSig} (h : noRedeclCheck P subs = true)
    (hcp : P.findClass cpCls = some cpC) {sig : MethodSig} (hsig : sig.sub ∈ subs) {decl : MethodDecl}
    (hm : Program.ClassDecl.findMethod cpC sig.sub false = some decl) : NoRedecl P sig ⟨cpCls, decl⟩ := by
  intro c hprog hsub
  unfold Program.isProgClass at hprog
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hprog
  obtain ⟨hmem, hname⟩ := ClassTree.mem_toList_of_find hd
  have hc := List.all_eq_true.mp h d hmem
  rw [hname, hsub] at hc
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at hc
  have hcc := hc sig.sub hsig
  unfold chainCls at hcc
  unfold Program.selectVirtual
  revert hcc
  cases hch : P.chainN P.fuel c sig.sub false with
  | jimple m =>
    intro hcc
    dsimp only at hcc
    by_cases ha : m.decl.mods.isAbstract = true
    · rw [if_pos ha] at hcc; simp at hcc
    · rw [if_neg ha] at hcc
      simp only [beq_iff_eq, Option.some.injEq] at hcc
      simp only [ha, if_false, Bool.false_eq_true]
      obtain ⟨d', hd', hm'⟩ := chainN_jimple _ _ _ _ _ hch
      rw [hcc, hcp] at hd'
      simp only [Option.some.injEq] at hd'
      subst hd'
      rw [hm] at hm'
      simp only [Option.some.injEq] at hm'
      cases m
      simp only at hcc hm'
      subst hcc hm'
      rfl
  | native lc => intro hcc; simp at hcc
  | none why => intro hcc; simp at hcc

/-- The signatures the field header reader and writer call. -/
def fhSubs : List SubSig :=
  [rbSig.sub, gttSig.sub, rfiSig.sub, rv32Sig.sub, wv32Sig.sub, wbdSig.sub, wi16Sig.sub]

/-- The program has the 277 classes of the drop-in. -/
theorem thrift_classes_length : EquivLean.Gen.ThriftJ.prog.classes.length = 277 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- In Thrift's program, no application subclass of `TCompactProtocol` redeclares the seven
methods (kernel evaluation over the class index). -/
theorem thrift_noRedeclCheck : noRedeclCheck EquivLean.Gen.ThriftJ.prog fhSubs = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem thrift_findClass_cp : EquivLean.Gen.ThriftJ.prog.findClass cpCls = some cpC := rfl

/-- `NoRedeclR` for Thrift's program. -/
theorem thrift_noRedeclR : NoRedeclR EquivLean.Gen.ThriftJ.prog :=
  ⟨noRedecl_of_check thrift_noRedeclCheck thrift_findClass_cp (by simp [fhSubs]) rfl,
   noRedecl_of_check thrift_noRedeclCheck thrift_findClass_cp (by simp [fhSubs]) rfl,
   noRedecl_of_check thrift_noRedeclCheck thrift_findClass_cp (by simp [fhSubs]) rfl,
   noRedecl_of_check thrift_noRedeclCheck thrift_findClass_cp (by simp [fhSubs]) rfl,
   noRedecl_of_check thrift_noRedeclCheck thrift_findClass_cp (by simp [fhSubs]) rfl⟩

/-- `NoRedeclW` for Thrift's program. -/
theorem thrift_noRedeclW : NoRedeclW EquivLean.Gen.ThriftJ.prog :=
  ⟨noRedecl_of_check thrift_noRedeclCheck thrift_findClass_cp (by simp [fhSubs]) rfl,
   noRedecl_of_check thrift_noRedeclCheck thrift_findClass_cp (by simp [fhSubs]) rfl,
   noRedecl_of_check thrift_noRedeclCheck thrift_findClass_cp (by simp [fhSubs]) rfl,
   noRedecl_of_check thrift_noRedeclCheck thrift_findClass_cp (by simp [fhSubs]) rfl⟩

set_option maxRecDepth 100000 in
/-- Thrift's program contains the protocol classes the field header theorems name, and shadows no
library class. -/
theorem thrift_contains :
    Contains EquivLean.Gen.ThriftJ.prog [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC] := by
  refine Contains.of_check (by decide +kernel) ?_
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **Field header, Thrift's program**: the reader theorems (`rfb_D`, `rfb_exStopNibble`,
`rfb_I16Overflow_short`, `rfb_exIdOutOfRange`, `rfb_exDelta15_long`) and the writer theorems
(`wfb_E`, `wfb_exDelta15`, `wfb_exI16Overflow`) hold for `EquivLean.Gen.ThriftJ.prog` under the
transport contracts alone: their program hypotheses are discharged here. -/
theorem thrift_fh_hyps :
    Contains EquivLean.Gen.ThriftJ.prog [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC] ∧
      NoRedeclR EquivLean.Gen.ThriftJ.prog ∧ NoRedeclW EquivLean.Gen.ThriftJ.prog :=
  ⟨thrift_contains, thrift_noRedeclR, thrift_noRedeclW⟩

end EquivLean.Demo.Thrift.Java
