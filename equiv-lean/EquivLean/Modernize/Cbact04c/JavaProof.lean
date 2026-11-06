import EquivLean.Modernize.Cbact04c.JavaSpec
import EquivLean.Modernize.Cbact04c.Accs

/-!
# CBACT04C → Java: from the contract of `run` to the generated statement

* the COBOL side: `Glue.cobol_outputs` (coblean's `cbact04c_events` for the accounts built from
  the field values: GOBACK; the displays, written transactions and rewritten accounts are
  `Model.run`'s);
* the Java side: the contract `runSpec` of `Cbact04c.run` (`JavaSpec.lean`: the `Result` holds
  `Model.run`'s outputs, `abended` is 0);
* the glue: a line of code points is the CP037 text of coblean's bytes (`jline`), a record object
  holds the field values coblean's record decodes to.

`statement_of_sat`: the contract implies the generated `Statement`.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbact04c.Java

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
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 link1 hl clk hc hk1 _hk2 _hk3 _hk4 hD _hjb n hn σ
    a1 a2 a3 a4 p1 cs hin1 hin2 hin3 hin4 hlink hclk hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8
  obtain ⟨hstop, hdisp, hwr, hrw⟩ := Glue.cobol_outputs vals1 vals2 vals3 vals4 link1 clk
    hv1 hv2 hv3 hv4 hl hc hk1 hD n (by omega)
  rw [← initMem_eq] at hstop hdisp hwr hrw
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbact04c.run { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
        [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
          (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)])) := by
    rw [EquivLean.Cobol.Ok, hstop]; rfl
  have hin : RunIn [.ref a1, .ref a2, .ref a3, .ref a4, .ref p1, .ref cs] σ vals1 vals2 vals3
      vals4 link1 clk :=
    ⟨a1, a2, a3, a4, p1, cs, rfl, hin1, hin2, hin3, hin4, hlink, hclk, hc.1, hv1, hv2, hv3, hv4,
      hl, hD⟩
  rw [EquivLean.Cobol.run]
  refine sim_of_sat ((EquivLean.Cobol.safe_exec_iff _).2 hok)
    ((EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩) hrun
    ⟨vals1, vals2, vals3, vals4, link1, clk, hin, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8⟩ ?_
  intro o ho
  cases o with
  | normal r σ' =>
    obtain ⟨res, fs, l, k, xs, mods, lw, kw, ws, mw, lr, kr, rs, mr, hr, hres, hl', hlist, hpairs,
      hlw, hlistw, hws, hlr, hlistr, hrs, hab⟩ := ho vals1 vals2 vals3 vals4 link1 clk hin
    refine ⟨σ', res, fs, l, k, xs, mods, by rw [hr], hres, hl', hlist, ?_,
      ⟨lw, kw, ws, mw, hlw, hlistw, forall2_decode hws hwr⟩,
      ⟨lr, kr, rs, mr, hlr, hlistr, forall2_decode hrs hrw⟩, ?_⟩
    · rw [← hdisp, List.map_map] at hpairs
      have e : (jline ∘ fun l => l.map cp037Code) = cp037Str := by
        funext bs; simp only [Function.comp_apply, jline, cp037Str_eq_map]
      rw [e] at hpairs
      exact forall2_of_map (R := JStrAt σ') (f := cp037Str) hpairs
    · rw [hab, hstop]
      rfl
  | exc e σ' => simp [runSpec, Spec.of] at ho
  | wrong msg => simp [runSpec, Spec.of] at ho

end EquivLean.Modernize.Cbact04c.Java
