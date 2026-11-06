import EquivLean.Modernize.Cbact01c.JavaSpec
import EquivLean.Modernize.Cbact01c.Glue

/-!
# CBACT01C → Java: from the contract of `run` to the generated statement

* the COBOL side: `Glue.cobol_outputs` (coblean's `cbact01c_extracts` for the account records
  built from the field values: GOBACK; the displays and the records written to OUT-FILE,
  ARRY-FILE and VBRC-FILE are `Model.run`'s);
* the Java side: the contract `runSpec` of `Cbact01c.run` (`JavaSpec.lean`: the `Result` holds
  `Model.run`'s outputs, `abended` is 0);
* the glue: a line of code points is the CP037 text of coblean's bytes (`jline`), a record object
  holds the field values coblean's record decodes to.

`statement_of_sat`: the contract implies the generated `Statement`.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbact01c.Java

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

/-- Strings holding the lines `ls`, against the bytes whose CP037 text they are. -/
theorem forall2_lines {σ : Jimple.State} {xs : List Jimple.Value} {bss : List (List UInt8)}
    (h : Forall2 (JStrAt σ) xs ((bss.map (·.map cp037Code)).map jline)) :
    Forall2 (JLineAt σ) xs bss := by
  rw [List.map_map] at h
  have e : (jline ∘ fun l => l.map cp037Code) = cp037Str := by
    funext bs; simp only [Function.comp_apply, jline, cp037Str_eq_map]
  rw [e] at h
  exact forall2_of_map (R := JStrAt σ) (f := cp037Str) h

set_option maxRecDepth 20000 in
/-- **The contract of `run` implies the generated statement.** -/
theorem statement_of_sat (hrun : Sat Gen.prog runRef runSpec) : Statement := by
  intro vals1 hv1 _hjb n hn σ a1 hin1 hi1 hi2 hi3 hi4 hi5
  obtain ⟨hstop, hdisp, hout, harr, hvb⟩ := Glue.cobol_outputs vals1 hv1 n hn
  rw [← initMem_eq] at hstop hdisp hout harr hvb
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbact01c.run
      { call := Cobol.Ext.cardDemoCalls CardDemo.Cbact01c.cfg } (n + 40)
      (CardDemo.Cbact01c.initState initMem [(1, vals1.map AccountRecord.encode)])) := by
    unfold EquivLean.Cobol.Ok; rw [hstop]; rfl
  have hin : RunIn [.ref a1] σ vals1 := ⟨a1, rfl, hin1, hv1⟩
  rw [EquivLean.Cobol.run]
  refine sim_of_sat ((EquivLean.Cobol.safe_exec_iff _).2 hok)
    ((EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩) hrun ⟨vals1, hin, hi1, hi2, hi3, hi4, hi5⟩ ?_
  intro o ho
  cases o with
  | normal r σ' =>
    obtain ⟨res, fs, hr, hres, ⟨l, k, xs, mods, hl1, hl2, hl3⟩,
      ⟨l1, k1, w1, m1, h1a, h1b, h1c⟩, ⟨l2, k2, w2, m2, h2a, h2b, h2c⟩,
      ⟨l3, k3, w3, m3, h3a, h3b, h3c⟩, hab⟩ := ho vals1 hin
    refine ⟨σ', res, fs, l, k, xs, mods, by rw [hr], hres, hl1, hl2, ?_,
      ⟨l1, k1, w1, m1, h1a, h1b, forall2_decode h1c hout⟩,
      ⟨l2, k2, w2, m2, h2a, h2b, forall2_decode h2c harr⟩,
      ⟨l3, k3, w3, m3, h3a, h3b, ?_⟩, ?_⟩
    · rw [← hdisp] at hl3
      exact forall2_lines hl3
    · rw [← hvb] at h3c
      exact forall2_lines h3c
    · rw [hab, hstop]
      rfl
  | exc e σ' => simp [runSpec, Spec.of] at ho
  | wrong msg => simp [runSpec, Spec.of] at ho

end EquivLean.Modernize.Cbact01c.Java
