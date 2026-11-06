import EquivLean.Modernize.Cbstm03a.JavaSpec
import EquivLean.Modernize.Cbstm03a.Glue

/-!
# CBSTM03A → Java: from the contract of `run` to the generated statement

* the COBOL side: `Glue.cobol_outputs` (`stm_run_sorted`, `stm_run_abort_cust`,
  `stm_run_abort_acct`: GOBACK or abend; the displays after dropping the 11 walk lines, the
  `STMT-FILE` and `HTML-FILE` writes, and `abended` match `Model.run`);
* the Java side: the contract `runSpec` of `Cbstm03a.run` (`JavaSpec.lean`: the `Result` holds
  `Model.run`'s outputs, `abended` is 1 exactly when the model abends);
* the glue: a line of code points is the CP037 text of coblean's bytes (`jline`).

`statement_of_sat`: the contract implies the generated `Statement`.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

theorem initMemRuns_eq : initMemRuns = Glue.initMemRuns := rfl

theorem initMem_eq : initMem = Glue.initMem := by
  unfold initMem Glue.initMem
  rw [initMemRuns_eq]

theorem cp037Str_eq_map (bs : List UInt8) :
    cp037Str bs = (bs.map cp037Code).map (BitVec.ofNat 16) := by
  simp [cp037Str, cp037Unit, cp037Code, List.map_map, Function.comp_def]

theorem forall2_of_map {α β γ : Type} {R : α → γ → Prop} {f : β → γ} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs (ys.map f) → Forall2 (fun x y => R x (f y)) xs ys
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: _, _ :: _, .cons h hs => .cons h (forall2_of_map hs)

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
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 hD hjb n hn σ a1 a2 a3 a4
    hin1 hin2 hin3 hin4 hi1 hi2 hi3 hi4 hi5 hi6
  obtain ⟨hsig, hdisp, hstmt, hhtml, habC⟩ :=
    Glue.cobol_outputs vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 hD n (by omega)
  rw [← initMem_eq] at hsig hdisp hstmt hhtml habC
  have hok : EquivLean.Cobol.Ok (Cobol.Stm.Stm.run { addrSpace := Cobol.Stm.asp } (n + 100)
      (Cobol.Stm.Stm.initState initMem
        [(3, vals1.map TrnxRecord.encode), (4, vals2.map CardXrefRecord.encode),
          (5, vals3.map CustomerRecord.encode), (6, vals4.map AccountRecord.encode)])) := by
    unfold EquivLean.Cobol.Ok
    rcases hsig with hs | hs <;> rw [hs] <;> rfl
  have hin : RunIn [.ref a1, .ref a2, .ref a3, .ref a4] σ vals1 vals2 vals3 vals4 :=
    ⟨a1, a2, a3, a4, rfl, hin1, hin2, hin3, hin4, hv1, hv2, hv3, hv4, hD, hjb⟩
  rw [EquivLean.Cobol.run]
  refine sim_of_sat ((EquivLean.Cobol.safe_exec_iff _).2 hok)
    ((EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩) hrun
    ⟨vals1, vals2, vals3, vals4, hin, hi1, hi2, hi3, hi4, hi5, hi6⟩ ?_
  intro o ho
  cases o with
  | normal r σ' =>
    obtain ⟨res, fs, l, k, xs, mods, lw1, kw1, ws1, mw1, lw2, kw2, ws2, mw2,
      hr, hres, hl, hlist, hpairs, hlw1, hlistw1, hws1, hlw2, hlistw2, hws2, hab⟩ :=
      ho vals1 vals2 vals3 vals4 hin
    refine ⟨σ', res, fs, l, k, xs, mods, by rw [hr], hres, hl, hlist, ?_,
      ⟨lw1, kw1, ws1, mw1, hlw1, hlistw1, ?_⟩,
      ⟨lw2, kw2, ws2, mw2, hlw2, hlistw2, ?_⟩, ?_⟩
    · rw [← hdisp] at hpairs; exact forall2_lines hpairs
    · rw [← hstmt] at hws1; exact forall2_lines hws1
    · rw [← hhtml] at hws2; exact forall2_lines hws2
    · rw [habC]; exact hab
  | exc e σ' => simp [runSpec, Spec.of] at ho
  | wrong msg => simp [runSpec, Spec.of] at ho

end EquivLean.Modernize.Cbstm03a.Java
