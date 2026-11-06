-- Termination package by JimpleLean's session: TermT4/BaseCp.lean (sha256 88b7bb1e4a6f6175...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Sel
import EquivLean.Demo.Thrift.Java.Term.Base

/-!
# Thrift → Java (T4), termination: protocol methods as callee contracts

The field and collection headers call protocol methods (`readVarint32()`, `readByte()`, …) through
contracts (`Γ2` … `Γ7`). Their termination premise is the callers' own (`TConc`), so the callee
premises are `cpX`: `TConc` for a method of `TCompactProtocol`, nothing for the transport's.
`contractTerm_cp` is `contractOK_cp` for termination: the method's termination and `NoRedecl` give the
contract's.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The callee premises: `TConc` for a method of `TCompactProtocol`, none otherwise. -/
def cpX (P : Program) (sig : MethodSig) (args : List Value) (σ : State) : Prop :=
  if sig.cls = cpCls then TConc P args σ else True

theorem tconc_intro {P : Program} {σ : State} {p t : Addr} {rest : List Value}
    {fs fst : List (FieldKey × Value)} {c : ClassName} (hp : σ.heap p = some (.plain cpCls fs))
    (ht : Fields.get fs (tpCls, "trans_") = some (.ref t)) (htc : σ.heap t = some (.plain c fst))
    (hc : P.concrete c = true) : TConc P (.ref p :: rest) σ :=
  ⟨p, rest, rfl, fs, t, c, fst, hp, ht, htc, hc⟩

/-- A contract of a `TCompactProtocol` instance method terminates, from the method's termination and
    `NoRedecl`. -/
theorem contractTerm_cp {P : Program} (hF : P.findClass cpCls = some cpC)
    (hT : P.findClass tpCls = some tpC) (hO : P.findClass "java.lang.Object" = none)
    {r : JType} {name : String} {ps : List JType} {m : MethodDecl} {S : Spec}
    (hm : Program.ClassDecl.findMethod cpC ⟨name, ps, r⟩ false = some m)
    (hm1 : Program.ClassDecl.findMethod cpC ⟨name, ps, r⟩ true = none)
    (hm2 : Program.ClassDecl.findMethod tpC ⟨name, ps, r⟩ true = none)
    (hcl : name ≠ "<clinit>") (hterm : ∀ args σ, S.pre args σ → MTerm P ⟨cpCls, m⟩ args σ)
    (hnr : NoRedecl P ⟨cpCls, r, name, ps⟩ ⟨cpCls, m⟩) :
    ContractTerm P ⟨cpCls, r, name, ps⟩ S := by
  refine ⟨fun m' ht args σ hp => ?_, fun c hc hs _ _ args σ hp => vterm_of_jimple (hnr c hc hs) hterm args σ hp⟩
  rw [targets_cp hF hT hO hm hm1 hm2 hcl ht]
  exact hterm args σ hp

end EquivLean.Demo.Thrift.Java
