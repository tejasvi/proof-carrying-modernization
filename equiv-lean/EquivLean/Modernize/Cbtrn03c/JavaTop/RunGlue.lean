import EquivLean.Modernize.Cbtrn03c.JavaTop.RunW
import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib3
import EquivLean.Modernize.Cbtrn03c.JavaTop.Glue1

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `run`, the model facts behind its cuts

The record objects of the transaction and date parameter files, the record area's initial
contents, and `Model.loop` one step at a time (the loop head's remaining computation).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

/-! ## Records -/

/-- `Forall2` at an index. -/
private theorem forall2_getElemR {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → ∀ (i : Nat) (hx : i < xs.length)
      (hy : i < ys.length), R (xs[i]'hx) (ys[i]'hy)
  | [], [], .nil, _, hx, _ => absurd hx (by simp)
  | _ :: _, _ :: _, .cons h _, 0, _, _ => h
  | _ :: _, _ :: _, .cons _ hs, i + 1, hx, hy =>
    forall2_getElemR hs i (by simpa using hx) (by simpa using hy)

/-- A string field of a record object, as `SFld`. -/
private theorem sfld_of_jfield {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)}
    {f : Field} {bs : List UInt8} (h : jFieldAt σ cls fs f (.str bs)) : SFld σ cls fs f.jname bs := by
  obtain ⟨v, hget, x, rfl, hx⟩ := h
  exact ⟨x, hget, hx⟩

/-- A transaction record object holds its field values (`JRecAt` with the fields spelled out). -/
theorem tranFields_of_jrec {σ : State} {e : Addr} {t : Rec}
    (h : JRecAt TranRecord "Cbtrn03c$TranRecord" σ (.ref e) t) (ht : TranRecord.Valid t) :
    TranFields σ e t := by
  obtain ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl, -⟩ :=
    Glue.tran_shape ht
  obtain ⟨x, fs, hx, hobj, hfs⟩ := h
  cases hx
  obtain _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨h5, _ | ⟨h6, _ | ⟨h7, _ | ⟨h8, _ |
    ⟨h9, _ | ⟨h10, _ | ⟨h11, _ | ⟨h12, _ | ⟨h13, -⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ := hfs
  exact ⟨fs, hobj, sfld_of_jfield h0, sfld_of_jfield h1, h2, sfld_of_jfield h3, sfld_of_jfield h4,
    h5, h6, sfld_of_jfield h7, sfld_of_jfield h8, sfld_of_jfield h9, sfld_of_jfield h10,
    sfld_of_jfield h11, sfld_of_jfield h12, sfld_of_jfield h13⟩

/-- The transaction record object at index `i` of the file `a`. -/
theorem trans_elem {σ : State} {a : Addr} {vals : Recs} (hf : TransactFileAt σ a vals)
    (hv : ∀ v ∈ vals, TranRecord.Valid v) {i : Nat} (hi : i < vals.length) :
    ∃ et es e, σ.heap a = some (.array et es) ∧ es.length = vals.length ∧ es[i]? = some (.ref e) ∧
      TranFields σ e (vals[i]'hi) := by
  obtain ⟨et, es, ha, -, h2⟩ := hf
  have hle := h2.length_eq
  have hie : i < es.length := hle ▸ hi
  obtain ⟨e, fs, he, hobj, hfs⟩ := forall2_getElemR h2 i hie hi
  refine ⟨et, es, e, ha, hle, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem hie, he]
  · exact tranFields_of_jrec ⟨e, fs, rfl, hobj, hfs⟩ (hv _ (List.getElem_mem hi))

theorem trans_arr {σ : State} {a : Addr} {vals : Recs} (hf : TransactFileAt σ a vals) :
    ∃ et es, σ.heap a = some (.array et es) ∧ es.length = vals.length ∧ vals.length < 2147483648 := by
  obtain ⟨et, es, ha, hlen, h2⟩ := hf
  exact ⟨et, es, ha, h2.length_eq, h2.length_eq ▸ hlen⟩

/-- The date parameter record object at index 0 of a non-empty file. -/
theorem parm_elem {σ : State} {a : Addr} {d : Rec} {rest : Recs}
    (hf : DateParmsFileAt σ a (d :: rest)) (hd : WsDateparmRecord.Valid d) :
    ∃ et es e fs, σ.heap a = some (.array et es) ∧ 0 < es.length ∧ es.length < 2147483648 ∧
      es[0]? = some (.ref e) ∧ σ.heap e = some (.plain "Cbtrn03c$WsDateparmRecord" fs) ∧
      SFld σ "Cbtrn03c$WsDateparmRecord" fs "wsStartDate" (Model.dStart d) ∧
      SFld σ "Cbtrn03c$WsDateparmRecord" fs "wsEndDate" (Model.dEnd d) := by
  obtain ⟨et, es, ha, hlen, h2⟩ := hf
  obtain ⟨st, f, en, rfl, -⟩ := Glue.parm_shape hd
  cases h2 with
  | cons hj _ =>
    obtain ⟨e, fs, rfl, hobj, hfs⟩ := hj
    obtain _ | ⟨h0, _ | ⟨-, _ | ⟨h2, -⟩⟩⟩ := hfs
    exact ⟨et, _, e, fs, ha, Nat.succ_pos _, hlen, rfl, hobj, sfld_of_jfield h0, sfld_of_jfield h2⟩

theorem parm_empty {σ : State} {a : Addr} (hf : DateParmsFileAt σ a []) :
    ∃ et, σ.heap a = some (.array et []) := by
  obtain ⟨et, es, ha, -, h2⟩ := hf
  cases h2
  exact ⟨et, ha⟩

theorem tran0_valid : TranRecord.Valid Model.tran0 := by
  refine .cons ⟨⟨_, rfl⟩, rfl⟩ (.cons ⟨⟨_, rfl⟩, rfl⟩ (.cons ⟨_, rfl, by decide, by decide, by decide, rfl⟩
    (.cons ⟨⟨_, rfl⟩, rfl⟩ (.cons ⟨⟨_, rfl⟩, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, by decide, rfl⟩
    (.cons ⟨_, rfl, by decide, by decide, by decide, rfl⟩
    (.cons ⟨⟨_, rfl⟩, rfl⟩ (.cons ⟨⟨_, rfl⟩, rfl⟩ (.cons ⟨⟨_, rfl⟩, rfl⟩ (.cons ⟨⟨_, rfl⟩, rfl⟩
    (.cons ⟨⟨_, rfl⟩, rfl⟩ (.cons ⟨⟨_, rfl⟩, rfl⟩ (.cons ⟨⟨_, rfl⟩, rfl⟩ .nil)))))))))))))

theorem procTs_len {t : Rec} (ht : TranRecord.Valid t) :
    (Model.strOf (t.getD 12 default)).length = 26 := by
  obtain ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, h15, -⟩ := Glue.tran_shape ht
  exact h15

theorem tran0_procTs_len : (Model.strOf (Model.tran0.getD 12 default)).length = 26 := by
  decide

/-- The dates of the run's date record have 10 characters. -/
theorem dOf_dates {vals5 : Recs} (hv : ∀ v ∈ vals5, WsDateparmRecord.Valid v) :
    (Model.dStart (dOf vals5)).length = 10 ∧ (Model.dEnd (dOf vals5)).length = 10 := by
  cases vals5 with
  | nil => exact ⟨by decide, by decide⟩
  | cons d rest =>
    obtain ⟨st, f, en, hd, hst, -, hen⟩ := Glue.parm_shape (hv d List.mem_cons_self)
    show (Model.dStart d).length = 10 ∧ (Model.dEnd d).length = 10
    rw [hd]
    exact ⟨hst, hen⟩

/-! ## The loop, one step -/

/-- A record read before the date range: the loop stops. -/
theorem loop_read_lo {xs ys cs : Recs} {d tv : Rec} {s : Model.St} {vals1 : Recs} {i : Nat}
    (hi : i < vals1.length) (hlo : Model.cmpB (Model.tDate (vals1[i]'hi)) (Model.dStart d) = .lt) :
    fin (Model.loop xs ys cs d (vals1.drop i) tv s) = Model.out s false := by
  have hr : Model.inRange d (vals1[i]'hi) = false := by
    simp [Model.inRange, hlo]
  rw [List.drop_eq_getElem_cons hi]
  simp only [Model.loop, hr, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- A record read after the date range: the loop stops. -/
theorem loop_read_hi {xs ys cs : Recs} {d tv : Rec} {s : Model.St} {vals1 : Recs} {i : Nat}
    (hi : i < vals1.length) (hhi : Model.cmpB (Model.tDate (vals1[i]'hi)) (Model.dEnd d) = .gt) :
    fin (Model.loop xs ys cs d (vals1.drop i) tv s) = Model.out s false := by
  have hr : Model.inRange d (vals1[i]'hi) = false := by
    simp [Model.inRange, hhi]
  rw [List.drop_eq_getElem_cons hi]
  simp only [Model.loop, hr, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- A record read in the date range: the step, then the rest. -/
theorem loop_read_in {xs ys cs : Recs} {d tv : Rec} {s : Model.St} {vals1 : Recs} {i : Nat}
    (hi : i < vals1.length)
    (hlo : Model.cmpB (Model.tDate (vals1[i]'hi)) (Model.dStart d) ≠ .lt)
    (hhi : Model.cmpB (Model.tDate (vals1[i]'hi)) (Model.dEnd d) ≠ .gt) :
    fin (Model.loop xs ys cs d (vals1.drop i) tv s) = afterStep vals1 xs ys cs d (i + 1) (vals1[i]'hi) s := by
  have hr : Model.inRange d (vals1[i]'hi) = true := by
    simp [Model.inRange, hlo, hhi]
  rw [List.drop_eq_getElem_cons hi]
  simp only [Model.loop, hr, ↓reduceIte, afterStep]
  cases Model.tranStep xs ys cs d s (vals1[i]'hi) <;> rfl

/-- End of file, the record area outside the date range. -/
theorem loop_eof_out {xs ys cs : Recs} {d tv : Rec} {s : Model.St} {vals1 : Recs} {i : Nat}
    (hi : vals1.length ≤ i)
    (hout : Model.cmpB (Model.tDate tv) (Model.dStart d) = .lt ∨
      Model.cmpB (Model.tDate tv) (Model.dEnd d) = .gt) :
    fin (Model.loop xs ys cs d (vals1.drop i) tv s) = Model.out s false := by
  have hr : Model.inRange d tv = false := by
    rcases hout with h | h <;> simp [Model.inRange, h]
  rw [List.drop_eq_nil_of_le hi]
  simp only [Model.loop, hr, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- End of file, the record area in the date range: the totals. -/
theorem loop_eof_in {xs ys cs : Recs} {d tv : Rec} {s : Model.St} {vals1 : Recs} {i : Nat}
    (hi : vals1.length ≤ i)
    (hlo : Model.cmpB (Model.tDate tv) (Model.dStart d) ≠ .lt)
    (hhi : Model.cmpB (Model.tDate tv) (Model.dEnd d) ≠ .gt) :
    fin (Model.loop xs ys cs d (vals1.drop i) tv s) = Model.out (Model.eofTail s tv) false := by
  have hr : Model.inRange d tv = true := by
    simp [Model.inRange, hlo, hhi]
  rw [List.drop_eq_nil_of_le hi]
  simp only [Model.loop, hr, ↓reduceIte]
  rfl

/-- After `processDetail`: no abend, the rest of the loop. -/
theorem afterStep_ok {vals1 xs ys cs : Recs} {d t : Rec} {s : Model.St} {i : Nat}
    (h : okB (Model.tranStep xs ys cs d s t) = true) :
    afterStep vals1 xs ys cs d i t s =
      fin (Model.loop xs ys cs d (vals1.drop i) t (stOf (Model.tranStep xs ys cs d s t))) := by
  unfold afterStep
  cases hts : Model.tranStep xs ys cs d s t with
  | ok s' => rfl
  | error s' =>
    rw [hts] at h
    cases h

/-- After `processDetail`: the abend. -/
theorem afterStep_err {vals1 xs ys cs : Recs} {d t : Rec} {s : Model.St} {i : Nat}
    (h : okB (Model.tranStep xs ys cs d s t) = false) :
    afterStep vals1 xs ys cs d i t s = Model.out (stOf (Model.tranStep xs ys cs d s t)) true := by
  unfold afterStep
  cases hts : Model.tranStep xs ys cs d s t with
  | ok s' =>
    rw [hts] at h
    cases h
  | error s' => rfl

end EquivLean.Modernize.Cbtrn03c.Java.Top
