import EquivLean.Modernize.Cbstm03b.RustSpec
import EquivLean.Modernize.Cbstm03b.Glue

/-!
# CBSTM03B → Rust: from the equation of `call` to the generated statement

* the relations: the generated per-file relations, `StateRel`, `LkM03bAreaRel` and `EnvRel` are the glue's
  (`Glue.lean`) at the model's values of the translation's (`absSt`, `absOe`, `LkM03bArea.vals`); the schemas
  of the generated statement are the model's;
* the COBOL side: `Glue.call_run` (coblean's `cbstm03b_call`: the run ends with `GOBACK`, and the state and
  area after the model's call are related to the run's);
* the Rust side: `CallSpec` (`RustSpec.lean`: `cbstm03b.call` returns the model's state and area, never
  panics), whose hypotheses `CallHyp` the statement's premises give (`callHyp_of`).

`statement_of_call`: the equation implies the generated `Statement` (an `Equiv`: Aeneas computations are
total and deterministic).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std
open CardDemo.Cbstm03b (opReadK ddCust ddAcct Files st0)

namespace EquivLean.Modernize.Cbstm03b.Rust

/-! ## The generated relations are the glue's -/

theorem fdTrnxfileRec_eq : FdTrnxfileRec = Model.FdTrnxfileRec := rfl
theorem fdXreffileRec_eq : FdXreffileRec = Model.FdXreffileRec := rfl
theorem fdCustfileRec_eq : FdCustfileRec = Model.FdCustfileRec := rfl
theorem fdAcctfileRec_eq : FdAcctfileRec = Model.FdAcctfileRec := rfl
theorem lkM03bArea_eq : LkM03bArea = Model.LkM03bArea := rfl
theorem trnxfileStatus_eq : TrnxfileStatus = Glue.TrnxfileStatus := rfl
theorem xreffileStatus_eq : XreffileStatus = Glue.XreffileStatus := rfl
theorem custfileStatus_eq : CustfileStatus = Glue.CustfileStatus := rfl
theorem acctfileStatus_eq : AcctfileStatus = Glue.AcctfileStatus := rfl

theorem trnxFileRel_iff (f : cbstm03b.TrnxFile) (s : FileSt) :
    TrnxFileRel f s ↔ Glue.FileRel Model.FdTrnxfileRec (absTrnx f) s := by
  simp only [TrnxFileRel, Glue.FileRel, absTrnx, List.forall_mem_map, List.map_map, Function.comp_def,
    fdTrnxfileRec_eq]
  exact Iff.rfl

theorem xrefFileRel_iff (f : cbstm03b.XrefFile) (s : FileSt) :
    XrefFileRel f s ↔ Glue.FileRel Model.FdXreffileRec (absXref f) s := by
  simp only [XrefFileRel, Glue.FileRel, absXref, List.forall_mem_map, List.map_map, Function.comp_def,
    fdXreffileRec_eq]
  exact Iff.rfl

theorem custFileRel_iff (f : cbstm03b.CustFile) (s : FileSt) :
    CustFileRel f s ↔ Glue.FileRel Model.FdCustfileRec (absCust f) s := by
  simp only [CustFileRel, Glue.FileRel, absCust, List.forall_mem_map, List.map_map, Function.comp_def,
    fdCustfileRec_eq]
  exact Iff.rfl

theorem acctFileRel_iff (f : cbstm03b.AcctFile) (s : FileSt) :
    AcctFileRel f s ↔ Glue.FileRel Model.FdAcctfileRec (absAcct f) s := by
  simp only [AcctFileRel, Glue.FileRel, absAcct, List.forall_mem_map, List.map_map, Function.comp_def,
    fdAcctfileRec_eq]
  exact Iff.rfl

theorem stateRel_iff (st : cbstm03b.State) (cs : Cobol.State) : StateRel st cs ↔ Glue.StateRel (absSt st) cs := by
  simp only [StateRel, Glue.StateRel, absSt, trnxFileRel_iff, xrefFileRel_iff, custFileRel_iff, acctFileRel_iff,
    List.map_map, Function.comp_def, fdTrnxfileRec_eq, fdXreffileRec_eq, fdCustfileRec_eq, fdAcctfileRec_eq,
    trnxfileStatus_eq, xreffileStatus_eq, custfileStatus_eq, acctfileStatus_eq]

theorem lkM03bAreaRel_iff (q : cbstm03b.LkM03bArea) (m : Mem) :
    LkM03bAreaRel q m ↔ Glue.LkM03bAreaRel (LkM03bArea.vals q) m := Iff.rfl

theorem envRel_abs {oe : Std.Array (Option Std.U8) 4#usize} {env : Env} (h : EnvRel oe env) :
    Glue.EnvRel (absOe oe) env := fun i hi => by
  simp only [absOe, Nat.add_sub_cancel]
  exact (h i hi).1

/-! ## The premises give `CallHyp` -/

theorem callHyp_of {env : Env} {m : Mem} {fs : Files} {k v : Int}
    (hK : m.read 1216 1 = [opReadK] → (m.read 1208 8 = ddCust ∨ m.read 1208 8 = ddAcct) →
      decodeNum {} CardDemo.Cbstm03b.LK_M03B_KEY_LN.fmt (m.read 1244 4) = some k ∧ 1 ≤ k ∧ k ≤ 25)
    (hD : EquivLean.Modernize.Cbstm03b.Domain env m fs k v)
    {oe : Std.Array (Option Std.U8) 4#usize} {st : cbstm03b.State} {q : cbstm03b.LkM03bArea}
    (hE : EnvRel oe env) (hS : StateRel st (st0 m fs)) (hR : LkM03bAreaRel q m) : CallHyp oe st q := by
  obtain ⟨⟨_, -, f1⟩, ⟨_, -, f2⟩, ⟨_, -, f3⟩, ⟨_, -, f4⟩, v1, -, v2, -, v3, -, v4, -, -, -, -, -⟩ := hS
  have hR' := (lkM03bAreaRel_iff q m).1 hR
  -- the key length of a keyed READ of CUSTFILE or ACCTFILE is the area's
  have hk : Model.aOp (LkM03bArea.vals q) = opReadK →
      (Model.aDd (LkM03bArea.vals q) = ddCust ∨ Model.aDd (LkM03bArea.vals q) = ddAcct) →
      k = Model.aKeyLn (LkM03bArea.vals q) ∧ 1 ≤ k ∧ k ≤ 25 := fun ho hd => by
    obtain ⟨hdec, h1, h25⟩ := hK (by rw [Glue.area_op hR', ho]) (by rw [Glue.area_dd hR']; exact hd)
    rw [Glue.area_keyln hR'] at hdec
    exact ⟨(Option.some.inj hdec).symm, h1, h25⟩
  refine ⟨fun i hi c hc => ?_, f1.2.1, f2.2.1, f3.2.1, f4.2.1, v1, v2, v3, v4, hR.1,
    fun ho hd => ?_, fun ho hd => ?_⟩
  · have e := hE i hi
    rw [hc, Option.map_some] at e
    exact e.2 c.val e.1.symm
  · obtain ⟨he, h1, h25⟩ := hk ho hd
    exact he ▸ ⟨h1, h25⟩
  · obtain ⟨he, h1, h25⟩ := hk ho (Or.inr hd)
    rw [← he, ← (Glue.area_key hR').1, ← Glue.read_take (by omega)]
    exact hD (by rw [Glue.area_op hR', ho]) (by rw [Glue.area_dd hR']; exact hd)

/-! ## The statement -/

/-- **The equation of `call` implies the generated statement.** -/
theorem statement_of_call (h : CallSpec) : Statement := by
  intro env m hm fs k v _ _ _ _ hK hA hD oe st q1 hE hS hR
  obtain ⟨st', q', hcall, hst, hq⟩ := h oe st q1 (callHyp_of hK hD hE hS hR)
  obtain ⟨hsig, hS', hR'⟩ := Glue.call_run env m hm fs k v hK hA (absOe oe) (absSt st) (LkM03bArea.vals q1)
    (envRel_abs hE) ((stateRel_iff st _).1 hS) ((lkM03bAreaRel_iff q1 m).1 hR)
  rw [← hst] at hS'
  rw [← hq] at hR'
  have hrel : Rel (.ok (st', q')) (CardDemo.Cbstm03b.run env 50 (st0 m fs)) :=
    ⟨st', q', rfl, hsig, (stateRel_iff st' _).2 hS', (lkM03bAreaRel_iff q' _).2 hR'⟩
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbstm03b.run env 50 (st0 m fs)) := by
    unfold EquivLean.Cobol.Ok
    rw [hsig]
    rfl
  rw [hcall, EquivLean.Cobol.run]
  refine ⟨fun _ => ⟨EquivLean.Aeneas.safe_ok _, fun or hor =>
      ⟨CardDemo.Cbstm03b.run env 50 (st0 m fs), ?_, ?_⟩⟩,
    fun _ => ⟨(EquivLean.Cobol.safe_exec_iff _).2 hok, fun os hos => ⟨.ok (st', q'), ?_, ?_⟩⟩⟩
  · exact (EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩
  · rw [(EquivLean.Aeneas.runs_ok_iff _ _).1 hor]
    exact hrel
  · exact (EquivLean.Aeneas.runs_ok_iff _ _).2 rfl
  · obtain ⟨h1, -⟩ := (EquivLean.Cobol.runs_exec_iff _ _).1 hos
    rw [h1]
    exact hrel

end EquivLean.Modernize.Cbstm03b.Rust
