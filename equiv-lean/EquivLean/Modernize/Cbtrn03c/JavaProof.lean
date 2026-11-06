import EquivLean.Modernize.Cbtrn03c.JavaSpec
import EquivLean.Modernize.Cbtrn03c.Glue

/-!
# CBTRN03C → Java: from the contract of `run` to the generated statement

* the COBOL side: `Glue.cobol_outputs` (coblean's `cbtrn03c_every` for the inputs built from the
  field values: GOBACK or the abend; the displays, the report records written and `abended` are
  `Model.run`'s);
* the Java side: the contract `runSpec` of `Cbtrn03c.run` (`JavaSpec.lean`: the `Result` holds
  `Model.run`'s outputs);
* the glue: a line of code points is the CP037 text of coblean's bytes (`jline`), a record object
  holds the field values coblean's record decodes to.

`statement_of_sat`: the contract implies the generated `Statement`.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

theorem initMem_eq : initMem = Glue.initMem := rfl

theorem cp037Str_eq_map (bs : List UInt8) :
    cp037Str bs = (bs.map cp037Code).map (BitVec.ofNat 16) := by
  simp [cp037Str, cp037Unit, cp037Code, List.map_map, Function.comp_def]

theorem forall2_of_map {α β γ : Type} {R : α → γ → Prop} {f : β → γ} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs (ys.map f) → Forall2 (fun x y => R x (f y)) xs ys
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: _, _ :: _, .cons h hs => .cons h (forall2_of_map hs)

/-- Objects holding field values, against records decoding to them. -/
theorem forall2_decode {α : Type} {R : α → List EquivLean.Cobol.Rec.FVal → Prop}
    {dec : List UInt8 → Option (List EquivLean.Cobol.Rec.FVal)} :
    ∀ {xs : List α} {vs : List (List EquivLean.Cobol.Rec.FVal)} {recs : List (List UInt8)},
      Forall2 R xs vs → recs.map dec = vs.map some →
        Forall2 (fun x rec => ∃ vals, R x vals ∧ dec rec = some vals) xs recs
  | [], [], [], .nil, _ => .nil
  | _ :: _, _ :: _, [], .cons _ _, h => by simp at h
  | _ :: _, v :: _, r :: _, .cons hx hs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons ⟨v, hx, h.1⟩ (forall2_decode hs h.2)

set_option maxRecDepth 20000 in
/-- **The contract of `run` implies the generated statement.** -/
theorem statement_of_sat (hrun : Sat Gen.prog runRef runSpec) : Statement := by
  intro vals1 vals2 vals3 vals4 vals5 hv1 hv2 hv3 hv4 hv5 hD _hjb n hn σ a1 a2 a3 a4 a5 hin1 hin2 hin3
    hin4 hin5 hcl hi2 hi3 hi4 hi5 hi6 hi7 hi8 hi9
  obtain ⟨hsig, hdisp, hwr, hab⟩ :=
    Glue.cobol_outputs vals1 vals2 vals3 vals4 vals5 hv1 hv2 hv3 hv4 hv5 hD n (by omega)
  rw [← initMem_eq] at hsig hdisp hwr hab
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbtrn03c.run {} (n + 60)
      (CardDemo.Cbtrn03c.initState initMem [(1, vals1.map TranRecord.encode),
        (2, vals2.map CardXrefRecord.encode), (3, vals3.map TranTypeRecord.encode),
        (4, vals4.map TranCatRecord.encode),
        (6, vals5.map (fun r => WsDateparmRecord.encode r ++ List.replicate 59 64))])) := by
    unfold EquivLean.Cobol.Ok
    rcases hsig with hs | hs <;> rw [hs] <;> rfl
  have hin : RunIn [.ref a1, .ref a2, .ref a3, .ref a4, .ref a5] σ vals1 vals2 vals3 vals4 vals5 :=
    ⟨a1, a2, a3, a4, a5, rfl, hin1, hin2, hin3, hin4, hin5, hv1, hv2, hv3, hv4, hv5⟩
  rw [EquivLean.Cobol.run]
  refine sim_of_sat ((EquivLean.Cobol.safe_exec_iff _).2 hok)
    ((EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩) hrun
    ⟨vals1, vals2, vals3, vals4, vals5, hin, hcl.1, hi2, hi9, hi5, hi3, hi6, hi4, hi7, hi8⟩ ?_
  intro o ho
  cases o with
  | normal r σ' =>
    obtain ⟨res, fs, l, k, xs, mods, lw, kw, ws, mw, hr, hres, hl', hlist, hpairs, hlw, hlwh, hws,
      habj⟩ := ho vals1 vals2 vals3 vals4 vals5 hin
    refine ⟨σ', res, fs, l, k, xs, mods, by rw [hr], hres, hl', hlist, ?_,
      ⟨lw, kw, ws, mw, hlw, hlwh, forall2_decode hws hwr⟩, ?_⟩
    · rw [← hdisp, List.map_map] at hpairs
      have e : (jline ∘ fun l => l.map cp037Code) = cp037Str := by
        funext bs; simp only [Function.comp_apply, jline, cp037Str_eq_map]
      rw [e] at hpairs
      exact forall2_of_map (R := JStrAt σ') (f := cp037Str) hpairs
    · rw [hab]
      exact habj
  | exc e σ' => simp [runSpec, Spec.of] at ho
  | wrong msg => simp [runSpec, Spec.of] at ho

end EquivLean.Modernize.Cbtrn03c.Java
