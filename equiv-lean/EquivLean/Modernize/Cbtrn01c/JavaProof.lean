import EquivLean.Modernize.Cbtrn01c.JavaStatement
import EquivLean.Modernize.Cbtrn01c.Model

/-!
# CBTRN01C → Java: from the contract of `run` to the generated statement

* the COBOL side: coblean's `cbtrn01c_verifies_all` (the DISPLAY lines: the start message, each
  transaction followed by what its lookups display, the lookups of the last transaction once
  more, the end message), for the records built from the field values;
* the Java side: the contract `runSpec` of `Cbtrn01c.run` (the `displays` list holds the lines of
  `Model.displayText` as UTF-16 strings; `abended` is 0);
* the glue: `Model.displayText_eq` (the lines are the CP037 texts of coblean's).

`statement_of_sat`: the contract implies the generated `Statement`.  The customer, card and
transaction files (2, 4, 6) are opened and closed but never read, by the COBOL program and by the
translation alike.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

/-- A line of code points as a Java string (UTF-16 units). -/
def jline (l : List Nat) : JStr := l.map (BitVec.ofNat 16)

/-- The contract of `Cbtrn01c.run` (partial correctness). -/
def runSpec : Spec := Spec.of
  (fun args σ => ∃ a1 a2 a3 a4 a5 a6 vals1 vals3 vals5,
     args = [.ref a1, .ref a2, .ref a3, .ref a4, .ref a5, .ref a6] ∧
     DalytranFileAt σ a1 vals1 ∧ XrefFileAt σ a3 vals3 ∧ AccountFileAt σ a5 vals5 ∧
     (∀ v ∈ vals1, DalytranRecord.Valid v) ∧ (∀ v ∈ vals3, CardXrefRecord.Valid v) ∧
     (∀ v ∈ vals5, AccountRecord.Valid v) ∧
     σ.initOf "Cbtrn01c" = .done ∧ σ.initOf "Cbtrn01c$Result" = .done ∧
     σ.initOf "Cbtrn01c$AccountRecord" = .done ∧ σ.initOf "Cbtrn01c$CardXrefRecord" = .done ∧
     σ.initOf "Cbtrn01c$DalytranRecord" = .done ∧ σ.initOf "Cbtrn01c$FdCardfileRec" = .done ∧
     σ.initOf "Cbtrn01c$FdCustfileRec" = .done ∧ σ.initOf "Cbtrn01c$FdTranfileRec" = .done)
  (fun args σ r σ' => ∀ a1 a2 a3 a4 a5 a6 vals1 vals3 vals5,
     args = [.ref a1, .ref a2, .ref a3, .ref a4, .ref a5, .ref a6] →
     DalytranFileAt σ a1 vals1 → XrefFileAt σ a3 vals3 → AccountFileAt σ a5 vals5 →
     (∀ v ∈ vals1, DalytranRecord.Valid v) → (∀ v ∈ vals3, CardXrefRecord.Valid v) →
     (∀ v ∈ vals5, AccountRecord.Valid v) →
     ∃ res fs l k xs mods, r = some (.ref res) ∧
       σ'.heap res = some (.plain "Cbtrn01c$Result" fs) ∧
       Fields.get fs ("Cbtrn01c$Result", "displays") = some (.ref l) ∧
       σ'.heap l = some (.list k xs mods) ∧
       Forall2 (JStrAt σ') xs ((Model.displayText vals1 vals3 vals5).map jline) ∧
       Fields.get fs ("Cbtrn01c$Result", "abended") = some (.int 0))

/-! ## The statement from the contract -/

theorem dalytranRecord_eq : DalytranRecord = Model.DalytranRecord := rfl
theorem cardXrefRecord_eq : CardXrefRecord = Model.CardXrefRecord := rfl
theorem accountRecord_eq : AccountRecord = Model.AccountRecord := rfl
theorem initMem_eq : initMem = Model.initMem := rfl

theorem cp037Str_eq_map (bs : List UInt8) :
    cp037Str bs = (bs.map cp037Code).map (BitVec.ofNat 16) := by
  simp [cp037Str, cp037Unit, cp037Code, List.map_map, Function.comp_def]

theorem forall2_of_map {α β γ : Type} {R : α → γ → Prop} {f : β → γ} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs (ys.map f) → Forall2 (fun x y => R x (f y)) xs ys
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: _, _ :: _, .cons h hs => .cons h (forall2_of_map hs)

theorem displays_eq : CardDemo.Cbtrn01c.displays = EquivLean.Cobol.Rec.displays := rfl

/-- **The contract of `run` implies the generated statement.** -/
theorem statement_of_sat (hrun : Sat Gen.prog runRef runSpec) : Statement := by
  intro vals1 vals2 vals3 vals4 vals5 vals6 hv1 hv2 hv3 hv4 hv5 hv6 _hjb n hn σ a1 a2 a3 a4 a5 a6
    hin1 hin2 hin3 hin4 hin5 hin6 hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8
  have hm : initMem.size = 3441 := by rw [initMem_size, CardDemo.Cbtrn01c.memSize_eq]
  have htr : ∀ t ∈ vals1.map DalytranRecord.encode, t.length = 350 := by
    intro r hr
    obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hr
    exact Schema.length_encode dalytranRecord_contig (hv1 v hv')
  have hac : ∀ a ∈ vals5.map AccountRecord.encode, a.length = 300 := by
    intro r hr
    obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hr
    exact Schema.length_encode accountRecord_contig (hv5 v hv')
  have hxeq : vals3.map CardXrefRecord.encode =
      (vals3.map Model.xrefOf).map CardDemo.Cbtrn01c.Xref.bytes := by
    rw [List.map_map]
    exact List.map_congr_left fun x hx => (Model.xrefOf_bytes (hv3 x hx)).1.symm
  have hxv : ∀ x ∈ vals3.map Model.xrefOf, x.valid := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact (Model.xrefOf_bytes (hv3 y hy)).2
  obtain ⟨hstop, hdisp⟩ := CardDemo.Cbtrn01c.cbtrn01c_verifies_all initMem hm
    (vals1.map DalytranRecord.encode) htr (vals3.map Model.xrefOf) hxv
    (vals5.map AccountRecord.encode) hac (vals2.map FdCustfileRec.encode)
    (vals4.map FdCardfileRec.encode) (vals6.map FdTranfileRec.encode) n
    (by simp only [List.length_map]; omega)
  rw [← hxeq] at hstop hdisp
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbtrn01c.run {} (n + 40)
      (CardDemo.Cbtrn01c.initState initMem [(1, vals1.map DalytranRecord.encode),
        (2, vals2.map FdCustfileRec.encode), (3, vals3.map CardXrefRecord.encode),
        (4, vals4.map FdCardfileRec.encode), (5, vals5.map AccountRecord.encode),
        (6, vals6.map FdTranfileRec.encode)])) := by
    rw [EquivLean.Cobol.Ok, hstop]; rfl
  rw [EquivLean.Cobol.run]
  refine sim_of_sat ((EquivLean.Cobol.safe_exec_iff _).2 hok)
    ((EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩) hrun
    ⟨a1, a2, a3, a4, a5, a6, vals1, vals3, vals5, rfl, hin1, hin3, hin5, hv1, hv3, hv5,
      hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8⟩ ?_
  intro o ho
  cases o with
  | normal r σ' =>
    obtain ⟨res, fs, l, k, xs, mods, hr, hres, hl, hlist, hpairs, hab⟩ :=
      ho a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 rfl hin1 hin3 hin5 hv1 hv3 hv5
    refine ⟨σ', res, fs, l, k, xs, mods, by rw [hr], hres, hl, hlist, ?_, ?_⟩
    · rw [← displays_eq, hdisp]
      have e := Model.displayText_eq (trans := vals1) (xs := vals3) (accs := vals5) hv1 hv3 hv5
      rw [← dalytranRecord_eq, ← accountRecord_eq, ← initMem_eq] at e
      rw [e, List.map_map] at hpairs
      have e2 : (jline ∘ fun l => l.map cp037Code) = cp037Str := by
        funext bs; simp only [Function.comp_apply, jline, cp037Str_eq_map]
      rw [e2] at hpairs
      exact forall2_of_map (R := JStrAt σ') (f := cp037Str) hpairs
    · rw [hab, hstop]
      rfl
  | exc e σ' => simp [runSpec, Spec.of] at ho
  | wrong msg => simp [runSpec, Spec.of] at ho

end EquivLean.Modernize.Cbtrn01c.Java
