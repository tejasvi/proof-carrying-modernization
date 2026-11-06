-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermLeafC.lean (sha256 96f345f1fd9a6007...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM1
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM2
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM2xd
import EquivLean.Modernize.TermCommon

/-!
# CBTRN02C → Java, termination: thin VCs of `writeReject`, `abend`, the copies and assignments

The thin twins of `writeReject_vc` (`JavaRunM1`), `abend_vc` (`JavaRunM2`), `abend22i_vc`
(`JavaRunM2xd`), `copyTcat_vc`, `assignTcat_vc` (`JavaRunR1`), `copyAccount_vc`, `copyTran_vc`
(`JavaRunR2`, the preamble of the originals), `assignXref_vc`, `assignAccount_vc` (`JavaRunR2b`).
None of them has a loop.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem writeReject_thin :
    ThinVC Gen.prog wrCallees.env 1 writeRejectRef writeRejectSpec [] (fun _ _ _ _ _ => 0) 60 := by
  jthin [writeRejectSpec, wrCallees, dalytranTextSig, dalytranTextSpec, padNumSig, padNumSpec,
    reasonDescSig, reasonDescSpec, fitSig, fitSpecF, Grows, FrameS, trailerJ, narrow_cls, refField,
    listOf, fieldsOf, argText, strOfV, evalDynamic, concatRecipe, Native.valueOfArg, valueOfObj_eq,
    valueOfObjN_ref, Native.nObjStr, Native.primStr, JType.isRef, jstrLitT]

theorem abend_thin :
    ThinVC Gen.prog (fun _ => none) 0 abendRef abendSpec [] (fun _ _ _ _ _ => 0) 10 := by
  jthin [abendSpec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem abend22i_thin :
    ThinVC Gen.prog (fun _ => none) 2 abendRef abendSpec22 [] (fun _ _ _ _ _ => 0) 80 := by
  jthin [abendSpec22, Grows, FrameS, jstrLitT, argText, listOf, fieldsOf, strOfV, refField,
    evalDynamic, concatRecipe, Native.valueOfArg, valueOfObj_eq, valueOfObjN_ref, Native.nObjStr,
    Native.primStr, JType.isRef]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem copyTcat_thin :
    ThinVC Gen.prog (fun _ => none) 1 copyTcatRef copyTcatSpec [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [copyTcatSpec, tcKeys, Grows, List.forall_mem_cons, List.forall_mem_nil,
    Option.isSome_iff_exists, narrow_long, narrow_cls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem assignTcat_thin :
    ThinVC Gen.prog (fun _ => none) 0 assignTcatRef assignTcatSpec [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [assignTcatSpec, tcKeys, List.forall_mem_cons, List.forall_mem_nil,
    Option.isSome_iff_exists, narrow_long, narrow_cls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem assignXref_thin :
    ThinVC Gen.prog (fun _ => none) 0 assignXrefRef assignXrefSpec [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [assignXrefSpec, xrKeys, List.forall_mem_cons, List.forall_mem_nil,
    Option.isSome_iff_exists, narrow_long, narrow_cls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem assignAccount_thin :
    ThinVC Gen.prog (fun _ => none) 0 assignAccountRef assignAccountSpec [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [assignAccountSpec, acKeys, List.forall_mem_cons, List.forall_mem_nil,
    Option.isSome_iff_exists, narrow_long, narrow_cls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem copyAccount_thin :
    ThinVC Gen.prog copyAccountC.env 0 copyAccountRef copyAccountSpec [] (fun _ _ _ _ _ => 0) 40 := by
  refine ⟨Gen.Cbtrn02c.«copyAccount(Cbtrn02c$AccountRecord)», rfl, ?_⟩
  intro args σ0 hpre
  obtain ⟨a, fs, rfl, ha, hall, hi⟩ := hpre
  simp only [acKeys, List.forall_mem_cons, List.forall_mem_nil, and_true, Option.isSome_iff_exists] at hall
  obtain ⟨⟨v1, e1⟩, ⟨v2, e2⟩, ⟨v3, e3⟩, ⟨v4, e4⟩, ⟨v5, e5⟩, ⟨v6, e6⟩, ⟨v7, e7⟩, ⟨v8, e8⟩, ⟨v9, e9⟩,
    ⟨v10, e10⟩, ⟨v11, e11⟩, ⟨v12, e12⟩, ⟨v13, e13⟩⟩ := hall
  refine ⟨?_, fun p hp => by simp at hp⟩
  jvc [copyAccountSpec, Invariants.inst, copyAccountC, ctorACSig, ctorACSpec, Grows, narrow_long,
    narrow_cls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem copyTran_thin :
    ThinVC Gen.prog copyTranC.env 0 copyTranRef copyTranSpec [] (fun _ _ _ _ _ => 0) 40 := by
  refine ⟨Gen.Cbtrn02c.«copyTran(Cbtrn02c$TranRecord)», rfl, ?_⟩
  intro args σ0 hpre
  obtain ⟨a, fs, rfl, ha, hall, hi⟩ := hpre
  simp only [trKeys, List.forall_mem_cons, List.forall_mem_nil, and_true, Option.isSome_iff_exists] at hall
  obtain ⟨⟨v1, e1⟩, ⟨v2, e2⟩, ⟨v3, e3⟩, ⟨v4, e4⟩, ⟨v5, e5⟩, ⟨v6, e6⟩, ⟨v7, e7⟩, ⟨v8, e8⟩, ⟨v9, e9⟩,
    ⟨v10, e10⟩, ⟨v11, e11⟩, ⟨v12, e12⟩, ⟨v13, e13⟩, ⟨v14, e14⟩⟩ := hall
  refine ⟨?_, fun p hp => by simp at hp⟩
  jvc [copyTranSpec, Invariants.inst, copyTranC, ctorTRSig, ctorTRSpec, Grows, narrow_long,
    narrow_cls]

end EquivLean.Modernize.Cbtrn02c.Java
