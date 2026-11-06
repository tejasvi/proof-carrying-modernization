import EquivLean.Modernize.Cbtrn02c.Glue
import EquivLean.Modernize.Cbtrn02c.ModelAny
import EquivLean.Modernize.Cbtrn02c.Any.Domain
import EquivLean.Demo.Cobol.Cbtrn02c.Dup

/-!
# CBTRN02C on any input: the translations' model and coblean's `cbtrn02c_any`

coblean's `cbtrn02c_any` covers every input: a posted transaction whose id has already been
written makes the `WRITE` fail (status 22) and the program abend (999); `modelX` is the posting
model with that stop.  `Model.runX` is the fold the translations perform on field values.

`cobol_outputs`: for the statements' inputs, the COBOL run ends with GOBACK or abend 999, and its
displayed lines, written and rewritten records, RETURN-CODE and abend flag are `Model.runX`'s.
The proof is a simulation, one transaction at a time (`stepX_corr`), on the restricted glue's
(`Cbtrn02c.Glue.step_corr`).  Its invariant is `CorrX`:
- before the stop, the restricted glue's `Corr` and the same written transaction ids;
- always, the same outputs (`OutCorr`): the stop drops the transaction record and adds the lines
  of the failed `WRITE` on both sides (`dup_out`).
Both sides post the same transactions: one more record written on one side is one more on the
other (`step_posted`, `step_wrL2`).
-/

open Cobol EquivLean.Cobol.Rec EquivLean.Modernize.Cbtrn02c.Model
open CardDemo.Cbtrn02c (Tran Xref Acct TCat)
open EquivLean.Modernize.Cbtrn02c.Glue

namespace EquivLean.Modernize.Cbtrn02c.Any.Glue

/-- coblean's theorem `cbtrn02c_any`, for the inputs as coblean's structures. -/
theorem cobol_runX (vals1 vals2 vals3 vals4 : List (List FVal)) (clk : List UInt8)
    (hv1 : ∀ v ∈ vals1, DalytranRecord.Valid v) (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, AccountRecord.Valid v) (hv4 : ∀ v ∈ vals4, TranCatBalRecord.Valid v)
    (hc : CurrentDate clk) (hlen : vals1.length < 1000000000) (n : Nat) (hn : vals1.length < n) :
    let r := CardDemo.Cbtrn02c.run { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbtrn02c.initState initMem [(1, vals1.map DalytranRecord.encode),
        (3, vals2.map CardXrefRecord.encode), (5, vals3.map AccountRecord.encode),
        (6, vals4.map TranCatBalRecord.encode)])
    let sx := CardDemo.Cbtrn02c.modelX (vals2.map xrefOf) (fun _ => clk) (sp 20)
      ⟨vals3.map acctOf, vals4.map tcatOf, sp 22, 0, 0, []⟩ (vals1.map tranOf)
    if sx.stop then
      r.1 = .fault (.abend 999) ∧ r.2.out = sx.m.out ++ [.display CardDemo.Cbtrn02c.startMsg] ∧
        r.2.mem.read 3250 2 = encodeNum {} CardDemo.Cbtrn02c.RETURN_CODE.fmt 0
    else
      r.1 = .stop .goback ∧
        r.2.out = [.display CardDemo.Cbtrn02c.endMsg,
          .display (CardDemo.Cbtrn02c.rejMsg ++
            encodeNum {} CardDemo.Cbtrn02c.WS_REJECT_COUNT.fmt sx.m.rejects),
          .display (CardDemo.Cbtrn02c.procMsg ++
            encodeNum {} CardDemo.Cbtrn02c.WS_TRANSACTION_COUNT.fmt vals1.length)] ++ sx.m.out ++
          [.display CardDemo.Cbtrn02c.startMsg] ∧
        r.2.mem.read 3250 2 =
          encodeNum {} CardDemo.Cbtrn02c.RETURN_CODE.fmt (if 0 < sx.m.rejects then 4 else 0) := by
  have hf1 : vals1.map DalytranRecord.encode = (vals1.map tranOf).map Tran.bytes := by
    rw [List.map_map]; exact List.map_congr_left (fun t ht => (tranOf_bytes (hv1 t ht)).symm)
  have hf2 : vals2.map CardXrefRecord.encode = (vals2.map xrefOf).map Xref.bytes := by
    rw [List.map_map]; exact List.map_congr_left (fun x hx => (xrefOf_bytes (hv2 x hx)).symm)
  have hf3 : vals3.map AccountRecord.encode = (vals3.map acctOf).map Acct.bytes := by
    rw [List.map_map]; exact List.map_congr_left (fun a ha => (acctOf_bytes (hv3 a ha)).symm)
  have hf4 : vals4.map TranCatBalRecord.encode = (vals4.map tcatOf).map TCat.bytes := by
    rw [List.map_map]; exact List.map_congr_left (fun c hc => (tcatOf_bytes (hv4 c hc)).symm)
  have hany := CardDemo.Cbtrn02c.cbtrn02c_any initMem initMem_size (fun _ => clk)
    (fun _ => EquivLean.Modernize.Cbact04c.Glue.clock_ok hc) (vals1.map tranOf)
    (by intro t ht; obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht; exact tranOf_valid (hv1 t0 ht0))
    (by rw [List.length_map]; exact hlen)
    (vals2.map xrefOf)
    (by intro x hx; obtain ⟨x0, hx0, rfl⟩ := List.mem_map.1 hx; exact xrefOf_valid (hv2 x0 hx0))
    (vals3.map acctOf)
    (by intro a ha; obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha; exact acctOf_valid (hv3 a0 ha0))
    (vals4.map tcatOf)
    (by intro c hc; obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc; exact tcatOf_valid (hv4 c0 hc0))
    n (by rw [List.length_map]; exact hn)
  simp only [initMem_tfill, initMem_catFill, ← hf1, ← hf2, ← hf3, ← hf4, List.length_map] at hany
  exact hany

/-! ## The stop: the failed `WRITE` -/

set_option maxRecDepth 10000 in
theorem errWrite_text : CardDemo.Cbtrn02c.errWriteMsg.map cp037Code =
    txt "ERROR WRITING TO TRANSACTION FILE" := by decide +kernel
set_option maxRecDepth 10000 in
theorem status22_text : CardDemo.Cbtrn02c.status22Msg.map cp037Code =
    txt "FILE STATUS IS: NNNN0022" := by decide +kernel
set_option maxRecDepth 10000 in
theorem abend_text : CardDemo.Cbtrn02c.abendMsg.map cp037Code = txt "ABENDING PROGRAM" := by
  decide +kernel

/-- A daily transaction is rejected or posted. -/
theorem step_cases (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8)
    (s : CardDemo.Cbtrn02c.Model) (t : Tran) :
    (∃ code desc, CardDemo.Cbtrn02c.step xrefs clk tfill s t = s.reject t code desc) ∨
      (∃ x j a, CardDemo.Cbtrn02c.step xrefs clk tfill s t = s.post clk tfill t x j a) := by
  unfold CardDemo.Cbtrn02c.step
  split
  · exact .inl ⟨_, _, rfl⟩
  · dsimp only
    split
    · exact .inl ⟨_, _, rfl⟩
    · split
      · exact .inl ⟨_, _, rfl⟩
      · split
        · exact .inl ⟨_, _, rfl⟩
        · exact .inr ⟨_, _, _, rfl⟩

/-- A posted transaction's newest event is the `WRITE` of its transaction record. -/
theorem step_out_of_posted {xrefs : List Xref} {clk : Nat → List UInt8} {tfill : List UInt8}
    {s : CardDemo.Cbtrn02c.Model} {t : Tran}
    (hp : (CardDemo.Cbtrn02c.step xrefs clk tfill s t).posted = s.posted + 1) :
    ∃ rec, (CardDemo.Cbtrn02c.step xrefs clk tfill s t).out =
      .write 2 rec :: (CardDemo.Cbtrn02c.step xrefs clk tfill s t).out.tail := by
  rcases step_cases xrefs clk tfill s t with ⟨code, desc, h⟩ | ⟨x, j, a, h⟩
  · rw [h] at hp; simp [CardDemo.Cbtrn02c.Model.reject] at hp
  · rw [h]
    simp only [CardDemo.Cbtrn02c.Model.post]
    split <;> exact ⟨_, rfl⟩

/-- A daily transaction is posted (its record joins the transaction records) or not. -/
theorem step_posted (xrefs : List (List FVal)) (clk : List UInt8) (s : St) (t : List FVal) :
    ((step xrefs clk s t).posted = s.posted + 1 ∧
        (step xrefs clk s t).tranW = s.tranW ++ [tranVals t clk]) ∨
      ((step xrefs clk s t).posted = s.posted ∧ (step xrefs clk s t).tranW = s.tranW) := by
  unfold step
  split
  · exact .inr ⟨rfl, rfl⟩
  · split
    · exact .inr ⟨rfl, rfl⟩
    · split
      · exact .inr ⟨rfl, rfl⟩
      · split
        · exact .inr ⟨rfl, rfl⟩
        · left
          unfold St.post
          split <;> exact ⟨rfl, rfl⟩

/-- coblean's daily transaction is posted (one more transaction record written) or not. -/
theorem step_wrL2 (xrefs : List Xref) (clk : Nat → List UInt8) (tfill : List UInt8)
    (s : CardDemo.Cbtrn02c.Model) (t : Tran) :
    ((CardDemo.Cbtrn02c.step xrefs clk tfill s t).posted = s.posted + 1 ∧
        (wrL 2 (CardDemo.Cbtrn02c.step xrefs clk tfill s t).out.reverse).length =
          (wrL 2 s.out.reverse).length + 1) ∨
      ((CardDemo.Cbtrn02c.step xrefs clk tfill s t).posted = s.posted ∧
        (wrL 2 (CardDemo.Cbtrn02c.step xrefs clk tfill s t).out.reverse).length =
          (wrL 2 s.out.reverse).length) := by
  rcases step_cases xrefs clk tfill s t with ⟨code, desc, h⟩ | ⟨x, j, a, h⟩
  · right
    rw [h]
    simp [CardDemo.Cbtrn02c.Model.reject, wrL_append, wrL_write, wrL_nil]
  · left
    rw [h]
    simp only [CardDemo.Cbtrn02c.Model.post]
    split <;> simp [wrL_append, wrL_write, wrL_rewrite, wrL_display, wrL_nil]

/-! ## The simulation with the stop -/

/-- The outputs of `S` are those of `M`'s events (the output fields of `Corr`). -/
structure OutCorr (S : St) (M : CardDemo.Cbtrn02c.Model) : Prop where
  disp : S.disp = txt "START OF EXECUTION OF PROGRAM CBTRN02C" ::
    (dispL M.out.reverse).map (·.map cp037Code)
  tranW : (wrL 2 M.out.reverse).map TranRecord.decode = S.tranW.map some
  rejW : (wrL 4 M.out.reverse).map RejectRecord.decode = S.rejW.map some
  catW : (wrL 6 M.out.reverse).map TranCatBalRecord.decode = S.catW.map some
  acctRW : (rwL 5 M.out.reverse).map AccountRecord.decode = S.acctRW.map some
  catRW : (rwL 6 M.out.reverse).map TranCatBalRecord.decode = S.catRW.map some

theorem out_of_corr {S : St} {M : CardDemo.Cbtrn02c.Model} (h : Corr S M) : OutCorr S M :=
  ⟨h.disp, h.tranW, h.rejW, h.catW, h.acctRW, h.catRW⟩

/-- The translations' state `x` after the same daily transactions as coblean's `y`: the same stop;
before a stop, `Corr` and the same written transaction ids; always the same outputs. -/
structure CorrX (x : StX) (y : CardDemo.Cbtrn02c.MX) : Prop where
  stop : x.stop = y.stop
  corr : y.stop = false → Corr x.s y.m
  ids : y.stop = false → ∀ i, i ∈ y.ids ↔ i ∈ x.s.tranW.map tId
  out : OutCorr x.s y.m

/-- The failed `WRITE` of a posted transaction keeps the outputs: the transaction record is not
written, the three lines are displayed. -/
theorem dup_out {S S' : St} {M' : CardDemo.Cbtrn02c.Model} {T : List FVal} {clk : List UInt8}
    (hc : Corr S' M') (htw : S'.tranW = S.tranW ++ [tranVals T clk]) {rec : List UInt8}
    (hout : M'.out = .write 2 rec :: M'.out.tail) :
    OutCorr { S' with tranW := S.tranW, disp := S'.disp ++ dupLines }
      { M' with out := CardDemo.Cbtrn02c.dupEvents ++ M'.out.tail } := by
  obtain ⟨-, -, -, -, -, -, -, -, hd, htr, hrj, hcw, harw, hcrw⟩ := hc
  rw [hout] at hd htr hrj hcw harw hcrw
  simp only [List.reverse_cons, wrL_append, rwL_append, dispL_append, wrL_write, rwL_write,
    dispL_write, wrL_nil, rwL_nil, dispL_nil, List.append_nil, ↓reduceIte] at hd htr hrj hcw harw hcrw
  simp only [show ((2 : Nat) = 4) = False by decide, show ((2 : Nat) = 6) = False by decide,
    ↓reduceIte, List.append_nil] at hrj hcw
  simp only [htw, List.map_append, List.map_cons, List.map_nil] at htr
  have htr' := (List.append_inj' htr (by simp)).1
  have hdw : ∀ f, wrL f CardDemo.Cbtrn02c.dupEvents.reverse = [] := fun f => rfl
  have hdr : ∀ f, rwL f CardDemo.Cbtrn02c.dupEvents.reverse = [] := fun f => rfl
  have hdd : (dispL CardDemo.Cbtrn02c.dupEvents.reverse).map (·.map cp037Code) = dupLines := by
    show [CardDemo.Cbtrn02c.errWriteMsg.map cp037Code, CardDemo.Cbtrn02c.status22Msg.map cp037Code,
      CardDemo.Cbtrn02c.abendMsg.map cp037Code] = dupLines
    rw [errWrite_text, status22_text, abend_text]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · rw [List.reverse_append, dispL_append, List.map_append, hdd, hd, List.cons_append]
  · rw [List.reverse_append, wrL_append, hdw, List.append_nil]; exact htr'
  · rw [List.reverse_append, wrL_append, hdw, List.append_nil]; exact hrj
  · rw [List.reverse_append, wrL_append, hdw, List.append_nil]; exact hcw
  · rw [List.reverse_append, rwL_append, hdr, List.append_nil]; exact harw
  · rw [List.reverse_append, rwL_append, hdr, List.append_nil]; exact hcrw

set_option maxHeartbeats 2000000 in
/-- **One daily transaction**: the translations' `stepX` and coblean's `stepX` keep `CorrX`. -/
theorem stepX_corr {xrefs : List (List FVal)} {clk : List UInt8} {x : StX}
    {y : CardDemo.Cbtrn02c.MX} {T : List FVal} (hC : CorrX x y) (hT : DalytranRecord.Valid T)
    (hX : ∀ x ∈ xrefs, CardXrefRecord.Valid x) (hclk : 16 ≤ clk.length) :
    CorrX (stepX xrefs clk x T)
      (CardDemo.Cbtrn02c.stepX (xrefs.map xrefOf) (fun _ => clk) (sp 20) y (tranOf T)) := by
  unfold stepX CardDemo.Cbtrn02c.stepX
  cases hy : y.stop with
  | true =>
    have hx : x.stop = true := by rw [hC.stop, hy]
    rw [ite_eq_left hx, ite_eq_left (show true = true from rfl)]
    exact hC
  | false =>
    have hx : ¬ x.stop = true := by rw [hC.stop, hy]; decide
    rw [ite_eq_right hx, ite_eq_right (show ¬ (false = true) by decide)]
    dsimp only
    have hc := hC.corr hy
    have hids := hC.ids hy
    have hc' := step_corr hc hT hX hclk
    have hl0 : (wrL 2 y.m.out.reverse).length = x.s.tranW.length := by
      simpa using congrArg List.length hc.tranW
    have hl1 : (wrL 2 (CardDemo.Cbtrn02c.step (xrefs.map xrefOf) (fun _ => clk) (sp 20) y.m
        (tranOf T)).out.reverse).length = (step xrefs clk x.s T).tranW.length := by
      simpa using congrArg List.length hc'.tranW
    have hid : (tranOf T).id = tId T := rfl
    rcases step_posted xrefs clk x.s T with ⟨hp, htw⟩ | ⟨hp, htw⟩ <;>
      rcases step_wrL2 (xrefs.map xrefOf) (fun _ => clk) (sp 20) y.m (tranOf T) with
        ⟨hq, hl⟩ | ⟨hq, hl⟩
    · -- posted on both sides
      by_cases hd : tId T ∈ x.s.tranW.map tId
      · have hd' : (tranOf T).id ∈ y.ids := by rw [hid]; exact (hids _).2 hd
        rw [ite_eq_left ⟨hp, hd⟩, ite_eq_left hq, ite_eq_left hd']
        obtain ⟨rec, hout⟩ := step_out_of_posted hq
        exact ⟨rfl, (fun h => by cases h), (fun h => by cases h), dup_out hc' htw hout⟩
      · have hd' : ¬ (tranOf T).id ∈ y.ids := by rw [hid]; exact fun h => hd ((hids _).1 h)
        rw [ite_eq_right (fun h => hd h.2), ite_eq_left hq, ite_eq_right hd']
        refine ⟨rfl, fun _ => hc', fun _ i => ?_, out_of_corr hc'⟩
        have hne : T ≠ [] := by
          rintro rfl
          exact absurd hT.length_eq (by decide)
        rw [htw, List.mem_cons, hids i]
        simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
          List.mem_singleton, tId_tranVals T clk hne, hid]
        exact or_comm
    · exfalso
      rw [htw] at hl1
      simp only [List.length_append, List.length_cons, List.length_nil] at hl1
      omega
    · exfalso
      rw [htw] at hl1
      omega
    · -- posted on neither side
      rw [ite_eq_right (fun h => by omega), ite_eq_right (by omega)]
      refine ⟨rfl, fun _ => hc', fun _ i => ?_, out_of_corr hc'⟩
      rw [htw, hids i]

/-- The daily transactions `ts`, from corresponding states. -/
theorem foldX_corr {xrefs : List (List FVal)} {clk : List UInt8}
    (hX : ∀ x ∈ xrefs, CardXrefRecord.Valid x) (hclk : 16 ≤ clk.length) :
    ∀ (ts : List (List FVal)) (x : StX) (y : CardDemo.Cbtrn02c.MX), CorrX x y →
      (∀ t ∈ ts, DalytranRecord.Valid t) →
      CorrX (ts.foldl (stepX xrefs clk) x)
        (ts.foldl (fun y t => CardDemo.Cbtrn02c.stepX (xrefs.map xrefOf) (fun _ => clk) (sp 20) y
          (tranOf t)) y)
  | [], _, _, hC, _ => hC
  | t :: ts, _, _, hC, ht =>
    foldX_corr hX hclk ts _ _ (stepX_corr hC (ht t (by simp)) hX hclk)
      (fun t' h' => ht t' (by simp [h']))

/-! ## The COBOL run -/

set_option maxHeartbeats 4000000 in
/-- **CBTRN02C's COBOL run outputs what `Model.runX` says**, for every input of the statements'
domain: valid field values, a `CURRENT-DATE` clock reading, fewer than 10^9 transactions.  The run
ends with GOBACK, or with abend 999 at a posted transaction whose id has already been written; its
displays (code points), the records it writes to TRANSACT, DALYREJS and TCATBAL and rewrites in
ACCOUNT and TCATBAL (decoded), RETURN-CODE and the abend are `Model.runX`'s. -/
theorem cobol_outputs (vals1 vals2 vals3 vals4 : List (List FVal)) (clk : List UInt8)
    (hv1 : ∀ v ∈ vals1, DalytranRecord.Valid v) (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, AccountRecord.Valid v) (hv4 : ∀ v ∈ vals4, TranCatBalRecord.Valid v)
    (hc : CurrentDate clk) (hD : Any.Domain vals1 vals2 vals3 vals4) (n : Nat)
    (hn : vals1.length < n) :
    let r := CardDemo.Cbtrn02c.run { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbtrn02c.initState initMem [(1, vals1.map DalytranRecord.encode),
        (3, vals2.map CardXrefRecord.encode), (5, vals3.map AccountRecord.encode),
        (6, vals4.map TranCatBalRecord.encode)])
    let o := Model.runX vals1 vals2 vals3 vals4 clk
    (r.1 = .stop .goback ∨ r.1 = .fault (.abend 999)) ∧
      (displays r.2).map (·.map cp037Code) = o.disp ∧
      (writes 2 r.2).map TranRecord.decode = o.tranW.map some ∧
      (writes 4 r.2).map RejectRecord.decode = o.rejW.map some ∧
      (writes 6 r.2).map TranCatBalRecord.decode = o.catW.map some ∧
      (rewrites 5 r.2).map AccountRecord.decode = o.acctRW.map some ∧
      (rewrites 6 r.2).map TranCatBalRecord.decode = o.catRW.map some ∧
      itemValue CardDemo.Cbtrn02c.RETURN_CODE CardDemo.Cbtrn02c.RETURN_CODE.fmt r.2 = o.rc ∧
      abended r.1 = o.abended := by
  dsimp only
  have hrun := cobol_runX vals1 vals2 vals3 vals4 clk hv1 hv2 hv3 hv4 hc hD n hn
  dsimp only at hrun
  simp only [CardDemo.Cbtrn02c.modelX, List.foldl_map] at hrun
  have h0 : CorrX ⟨init vals3 vals4, false⟩ ⟨⟨vals3.map acctOf, vals4.map tcatOf, sp 22, 0, 0, []⟩,
      [], false⟩ :=
    ⟨rfl, fun _ => init_corr hv3 hv4, fun _ i => by simp [init], out_of_corr (init_corr hv3 hv4)⟩
  have hC := foldX_corr hv2 (by rw [hc.1]; decide) vals1 _ _ h0 hv1
  simp only [Model.runX]
  generalize vals1.foldl (fun y t => CardDemo.Cbtrn02c.stepX (vals2.map xrefOf) (fun _ => clk)
    (sp 20) y (tranOf t)) ⟨⟨vals3.map acctOf, vals4.map tcatOf, sp 22, 0, 0, []⟩, [], false⟩ = Y
    at hC hrun
  generalize vals1.foldl (stepX vals2 clk) ⟨init vals3 vals4, false⟩ = X at hC
  have hO := hC.out
  cases hY : Y.stop with
  | true =>
    have hX : X.stop = true := by rw [hC.stop, hY]
    rw [ite_eq_left hY] at hrun
    rw [ite_eq_left hX]
    obtain ⟨hstop, hout, hrc⟩ := hrun
    refine ⟨.inr hstop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (dispL _).map _ = _
      rw [hout, hO.disp]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        dispL_display, List.map_cons, startMsg_text, List.singleton_append]
    · show (wrL 2 _).map _ = _
      rw [hout]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        wrL_append, wrL_display, wrL_nil]
      exact hO.tranW
    · show (wrL 4 _).map _ = _
      rw [hout]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        wrL_append, wrL_display, wrL_nil]
      exact hO.rejW
    · show (wrL 6 _).map _ = _
      rw [hout]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        wrL_append, wrL_display, wrL_nil]
      exact hO.catW
    · show (rwL 5 _).map _ = _
      rw [hout]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        rwL_append, rwL_display, rwL_nil]
      exact hO.acctRW
    · show (rwL 6 _).map _ = _
      rw [hout]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        rwL_append, rwL_display, rwL_nil]
      exact hO.catRW
    · show (decodeNum {} CardDemo.Cbtrn02c.RETURN_CODE.fmt (Cobol.Mem.read _ 3250 2)).getD 0 = _
      rw [hrc, decodeNum_encodeNum {} _ _ (by decide) (by decide) (by decide)]
      rfl
    · rw [hstop]; rfl
  | false =>
    have hX : ¬ X.stop = true := by rw [hC.stop, hY]; decide
    rw [ite_eq_right (show ¬ (Y.stop = true) by rw [hY]; decide)] at hrun
    rw [ite_eq_right hX]
    obtain ⟨hstop, hout, hrc⟩ := hrun
    have hc' := hC.corr hY
    refine ⟨.inl hstop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (dispL _).map _ = _
      rw [hout, hc'.disp, hc'.rejects]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.append_assoc, dispL_append, dispL_display, dispL_nil,
        List.map_append, List.map_cons, List.map_nil, startMsg_text, endMsg_text, procMsg_text,
        rejMsg_text, trCount_text]
    · show (wrL 2 _).map _ = _
      rw [hout]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.append_assoc, wrL_append, wrL_display, wrL_nil, List.append_nil]
      exact hc'.tranW
    · show (wrL 4 _).map _ = _
      rw [hout]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.append_assoc, wrL_append, wrL_display, wrL_nil, List.append_nil]
      exact hc'.rejW
    · show (wrL 6 _).map _ = _
      rw [hout]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.append_assoc, wrL_append, wrL_display, wrL_nil, List.append_nil]
      exact hc'.catW
    · show (rwL 5 _).map _ = _
      rw [hout]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.append_assoc, rwL_append, rwL_display, rwL_nil, List.append_nil]
      exact hc'.acctRW
    · show (rwL 6 _).map _ = _
      rw [hout]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.append_assoc, rwL_append, rwL_display, rwL_nil, List.append_nil]
      exact hc'.catRW
    · show (decodeNum {} CardDemo.Cbtrn02c.RETURN_CODE.fmt (Cobol.Mem.read _ 3250 2)).getD 0 = _
      rw [hrc, hc'.rejects, decodeNum_encodeNum {} _ _ (by decide) (by decide) (by split <;> decide)]
      rfl
    · rw [hstop]; rfl


end EquivLean.Modernize.Cbtrn02c.Any.Glue
