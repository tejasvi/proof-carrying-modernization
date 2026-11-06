import EquivLean.Demo.Thrift.Java.ThriftProg
import EquivLean.Demo.Thrift.Java.RsbP
import EquivLean.Demo.Thrift.Java.WcbP

/-!
# Thrift → Java (T4): the list/set header theorems for Thrift's own program

On `EquivLean.Gen.ThriftJ.prog`, `NoRedeclL` and `NoRedeclS` hold: every application subclass of
`TCompactProtocol` selects the `TCompactProtocol` declaration of `checkContainerReadLength(int)` and
`readListBegin()`, and the `TProtocol` declaration of `checkReadBytesAvailable(TList)`. Checked by
kernel evaluation (`decide +kernel`; no `native_decide`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- Every application subclass of `TCompactProtocol` finds the declaration in class `cls` of each
signature in `subs`. -/
def noRedeclCheckIn (P : Program) (cls : ClassName) (subs : List SubSig) : Bool :=
  P.index.toList.all fun d =>
    P.isSubclass d.name cpCls != some true || subs.all fun sub => chainCls P d.name sub == some cls

theorem noRedecl_of_checkIn {P : Program} {cls : ClassName} {cd : ClassDecl} {subs : List SubSig}
    (h : noRedeclCheckIn P cls subs = true) (hcd : P.findClass cls = some cd) {sig : MethodSig}
    (hsig : sig.sub ∈ subs) {decl : MethodDecl}
    (hm : Program.ClassDecl.findMethod cd sig.sub false = some decl) : NoRedecl P sig ⟨cls, decl⟩ := by
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
      rw [hcc, hcd] at hd'
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

/-- The `TCompactProtocol` signatures the list/set header readers add. -/
def collSubs : List SubSig := [ccrlSig.sub, rlbSig.sub]

/-- The inherited `TProtocol` signature `readListBegin()` calls. -/
def collSubsTp : List SubSig := [crbaSig.sub]

set_option maxRecDepth 100000 in
theorem thrift_noRedeclCheck_coll : noRedeclCheck EquivLean.Gen.ThriftJ.prog collSubs = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem thrift_noRedeclCheck_tp :
    noRedeclCheckIn EquivLean.Gen.ThriftJ.prog tpCls collSubsTp = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem thrift_findClass_tp : EquivLean.Gen.ThriftJ.prog.findClass tpCls = some tpC := rfl

/-- `NoRedeclL` for Thrift's program. -/
theorem thrift_noRedeclL : NoRedeclL EquivLean.Gen.ThriftJ.prog :=
  ⟨thrift_noRedeclR.1, thrift_noRedeclR.2.1,
   noRedecl_of_check thrift_noRedeclCheck_coll thrift_findClass_cp (by simp [collSubs]) rfl,
   noRedecl_of_checkIn thrift_noRedeclCheck_tp thrift_findClass_tp (by simp [collSubsTp]) rfl,
   thrift_noRedeclR.2.2.2.1, thrift_noRedeclR.2.2.2.2⟩

/-- `NoRedeclS` for Thrift's program. -/
theorem thrift_noRedeclS : NoRedeclS EquivLean.Gen.ThriftJ.prog :=
  ⟨thrift_noRedeclL,
   noRedecl_of_check thrift_noRedeclCheck_coll thrift_findClass_cp (by simp [collSubs]) rfl⟩

set_option maxRecDepth 100000 in
/-- Thrift's program contains the classes the list/set header readers name. -/
theorem thrift_contains_coll :
    Contains EquivLean.Gen.ThriftJ.prog [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC] := by
  refine Contains.of_check (by decide +kernel) ?_
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **List/set header, Thrift's program**: the program hypotheses of the writer theorem `wcb_E`,
the list reader theorems `rlb_D`, `rlb_exNegSize`, `rlb_uuid` and the set reader theorems `rsb_D`,
`rsb_exNegSize` hold for `EquivLean.Gen.ThriftJ.prog`; they hold there under the transport
contracts alone. -/
theorem thrift_coll_hyps :
    Contains EquivLean.Gen.ThriftJ.prog [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC] ∧
      NoRedeclW EquivLean.Gen.ThriftJ.prog ∧
      Contains EquivLean.Gen.ThriftJ.prog [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC] ∧
      NoRedeclL EquivLean.Gen.ThriftJ.prog ∧
      Contains EquivLean.Gen.ThriftJ.prog [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC, tsC] ∧
      NoRedeclS EquivLean.Gen.ThriftJ.prog :=
  ⟨thrift_contains, thrift_noRedeclW,
   contains_sub thrift_contains_coll (by
     intro d hd
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
     rcases hd with h | h | h | h | h | h | h | h | h <;> simp [h]),
   thrift_noRedeclL, thrift_contains_coll, thrift_noRedeclS⟩

end EquivLean.Demo.Thrift.Java
