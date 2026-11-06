import EquivLean.Modernize.Cbtrn03c.JavaW.WsM4

/-!
# CBTRN03C → Java: `writeTransactionReport`, the contract and its cuts

On the model state (`WsRel`), against the model contracts of `writeHeaders`, `writePageTotals`,
`writeDetail` and the contract of `add11`.  The ghost values are parameters; cuts at the first
`writeHeaders` call (statement 7), at the joins (8, 14), at the `writePageTotals` call (12) and at
the `writeDetail` call (22).  Segments that read or write the working state's fields see `WsRel`
unfolded (`W5a`, `W5c`, `W5d`); segments that only call keep it folded (`W5b`, `W5e`).

Locals: `r0` (the `Ws` object) 0, `r2` (type description) 4, `r3` (category description) 5,
`r1` (the transaction record) 6.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

abbrev writeTransactionReportRef : MethodRef :=
  Gen.Cbtrn03c.«writeTransactionReport(Cbtrn03c$Ws,Cbtrn03c$TranRecord,java.lang.String,java.lang.String)».ref

def reportCallees : Contracts :=
  [(writeHeadersSig, writeHeadersSpecM), (Top.writePageTotalsSig, Top.writePageTotalsSpecM),
   (writeDetailSig, writeDetailSpecM), (add11Sig, add11Spec)]

theorem reportCallees_valid : Valid Gen.prog reportCallees.env := by
  apply Contracts.valid_of_ok
  simp only [reportCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨writeHeadersM_ok, writePageTotalsM_ok, writeDetailM_ok, add11_ok⟩

/-! ## The model states along the method -/

def rep0 (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St) : Model.St :=
  { s with first := false, rs := Model.cps (Model.dStart d), re := Model.cps (Model.dEnd d) }

def rep1 (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St) : Model.St :=
  if s.first then Model.headers (rep0 d s) else s

def rep2 (s : Model.St) : Model.St :=
  if s.lc % 20 = 0 then Model.headers (Model.pageTotals s) else s

def rep3 (s : Model.St) (t : List EquivLean.Cobol.Rec.FVal) : Model.St :=
  { s with
    page := Model.trunc11 (s.page + Model.tAmt t)
    acct := Model.trunc11 (s.acct + Model.tAmt t) }

theorem report_eq (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) :
    Model.report d s t y cc = Model.inc (Model.wr (rep3 (rep2 (rep1 d s)) t)
      (Model.detailLine t (rep3 (rep2 (rep1 d s)) t).xref y cc)) := rfl

@[simp] theorem headers_first (s : Model.St) : (Model.headers s).first = s.first := rfl
@[simp] theorem pageTotals_first (s : Model.St) : (Model.pageTotals s).first = s.first := rfl
@[simp] theorem headers_xref (s : Model.St) : (Model.headers s).xref = s.xref := rfl
@[simp] theorem pageTotals_xref (s : Model.St) : (Model.pageTotals s).xref = s.xref := rfl

theorem rep1_first (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St) : (rep1 d s).first = false := by
  unfold rep1; split
  · rfl
  · rename_i h; simpa using h

theorem rep1_xref (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St) : (rep1 d s).xref = s.xref := by
  unfold rep1; split <;> rfl

theorem rep2_first (s : Model.St) : (rep2 s).first = s.first := by
  unfold rep2; split <;> rfl

theorem rep2_xref (s : Model.St) : (rep2 s).xref = s.xref := by
  unfold rep2; split <;> rfl

theorem rep3_xref (s : Model.St) (t : List EquivLean.Cobol.Rec.FVal) : (rep3 s t).xref = s.xref := rfl

/-! ## The working state's object updated in place -/

theorem heap_setObj_ws_ne {σ : State} {w x : Addr} {fs : List (FieldKey × Value)} {o o' : Obj}
    (hw : σ.heap w = some (.plain "Cbtrn03c$Ws" fs)) (hx : σ.heap x = some o)
    (ho : ∀ fs', o ≠ .plain "Cbtrn03c$Ws" fs') : (σ.setObj w o').heap x = some o := by
  have hne : x ≠ w := by
    intro e; subst e; rw [hw] at hx; cases hx; exact ho fs rfl
  rw [State.heap_setObj_of_lt (State.lt_next_of_heap hw), if_neg hne, hx]

theorem top_recsAt_setObj_ws {σ : State} {w : Addr} {fs : List (FieldKey × Value)}
    {fs' : List (FieldKey × Value)} {ys : List Value} {ss : List JStr}
    (hw : σ.heap w = some (.plain "Cbtrn03c$Ws" fs)) (h : Top.RecsAt σ ys ss) :
    Top.RecsAt (σ.setObj w (.plain "Cbtrn03c$Ws" fs')) ys ss := by
  refine top_recsAt_mono ?_ h
  refine ⟨Nat.le_of_eq (State.next_setObj _ _ _).symm, ?_, ?_, ?_⟩
  · intro x s hx
    exact heap_setObj_ws_ne hw hx (by intro _ e; cases e)
  · intro x c fs0 hx hc
    exact heap_setObj_ws_ne hw hx (by intro _ e; cases e; exact hc rfl)
  · intro x et xs hx
    exact heap_setObj_ws_ne hw hx (by intro _ e; cases e)

theorem keepsNonWs_setObj_ws {σ0 σ : State} {w : Addr} {fs fs' : List (FieldKey × Value)}
    (hw : σ.heap w = some (.plain "Cbtrn03c$Ws" fs)) (hk : Top.KeepsNonWs σ0 σ) :
    Top.KeepsNonWs σ0 (σ.setObj w (.plain "Cbtrn03c$Ws" fs')) := by
  refine ⟨by rw [State.next_setObj]; exact hk.1, ?_, ?_, ?_⟩
  · intro x s hx
    exact heap_setObj_ws_ne hw (hk.2.1 x s hx) (by intro _ e; cases e)
  · intro x c fs0 hx hc
    exact heap_setObj_ws_ne hw (hk.2.2.1 x c fs0 hx hc) (by intro _ e; cases e; exact hc rfl)
  · intro x et xs hx
    exact heap_setObj_ws_ne hw (hk.2.2.2 x et xs hx) (by intro _ e; cases e)

theorem tranFields_setObj_ws {σ : State} {w c : Addr} {fs fs' : List (FieldKey × Value)}
    {t : List EquivLean.Cobol.Rec.FVal} (hw : σ.heap w = some (.plain "Cbtrn03c$Ws" fs))
    (h : Top.TranFields σ c t) : Top.TranFields (σ.setObj w (.plain "Cbtrn03c$Ws" fs')) c t := by
  have hk : Top.KeepsNonWs σ (σ.setObj w (.plain "Cbtrn03c$Ws" fs')) :=
    keepsNonWs_setObj_ws hw ⟨Nat.le_refl _, fun _ _ h => h, fun _ _ _ h _ => h, fun _ _ _ h => h⟩
  obtain ⟨fs0, hc, ⟨y0, e0, h0⟩, ⟨y1, e1, h1⟩, l2, ⟨y3, e3, h3⟩, ⟨y4, e4, h4⟩, l5, l6,
    ⟨y7, e7, h7⟩, ⟨y8, e8, h8⟩, ⟨y9, e9, h9⟩, ⟨y10, e10, h10⟩, ⟨y11, e11, h11⟩,
    ⟨y12, e12, h12⟩, ⟨y13, e13, h13⟩⟩ := h
  exact ⟨fs0, hk.2.2.1 c Top.tranC fs0 hc (by decide), ⟨y0, e0, hk.2.1 _ _ h0⟩,
    ⟨y1, e1, hk.2.1 _ _ h1⟩, l2, ⟨y3, e3, hk.2.1 _ _ h3⟩, ⟨y4, e4, hk.2.1 _ _ h4⟩, l5, l6,
    ⟨y7, e7, hk.2.1 _ _ h7⟩, ⟨y8, e8, hk.2.1 _ _ h8⟩, ⟨y9, e9, hk.2.1 _ _ h9⟩,
    ⟨y10, e10, hk.2.1 _ _ h10⟩, ⟨y11, e11, hk.2.1 _ _ h11⟩, ⟨y12, e12, hk.2.1 _ _ h12⟩,
    ⟨y13, e13, hk.2.1 _ _ h13⟩⟩

theorem keepsNonWs_setObj_ws0 {σ : State} {w : Addr} {fs fs' : List (FieldKey × Value)}
    (hw : σ.heap w = some (.plain "Cbtrn03c$Ws" fs)) :
    Top.KeepsNonWs σ (σ.setObj w (.plain "Cbtrn03c$Ws" fs')) :=
  keepsNonWs_setObj_ws hw ⟨Nat.le_refl _, fun _ _ h => h, fun _ _ _ h _ => h, fun _ _ _ h => h⟩

theorem keepsNonWs_refl (σ : State) : Top.KeepsNonWs σ σ :=
  ⟨Nat.le_refl _, fun _ _ h => h, fun _ _ _ h _ => h, fun _ _ _ h => h⟩

theorem keepsNonWs_trans {σ1 σ2 σ3 : State} (h1 : Top.KeepsNonWs σ1 σ2)
    (h2 : Top.KeepsNonWs σ2 σ3) : Top.KeepsNonWs σ1 σ3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun x s h => h2.2.1 x s (h1.2.1 x s h),
   fun x c fs h hc => h2.2.2.1 x c fs (h1.2.2.1 x c fs h hc) hc,
   fun x et xs h => h2.2.2.2 x et xs (h1.2.2.2 x et xs h)⟩

theorem tranFields_keeps {σ σ' : State} {c : Addr} {t : List EquivLean.Cobol.Rec.FVal}
    (hk : Top.KeepsNonWs σ σ') (h : Top.TranFields σ c t) : Top.TranFields σ' c t := by
  obtain ⟨fs0, hc, ⟨y0, e0, h0⟩, ⟨y1, e1, h1⟩, l2, ⟨y3, e3, h3⟩, ⟨y4, e4, h4⟩, l5, l6,
    ⟨y7, e7, h7⟩, ⟨y8, e8, h8⟩, ⟨y9, e9, h9⟩, ⟨y10, e10, h10⟩, ⟨y11, e11, h11⟩,
    ⟨y12, e12, h12⟩, ⟨y13, e13, h13⟩⟩ := h
  exact ⟨fs0, hk.2.2.1 c Top.tranC fs0 hc (by decide), ⟨y0, e0, hk.2.1 _ _ h0⟩,
    ⟨y1, e1, hk.2.1 _ _ h1⟩, l2, ⟨y3, e3, hk.2.1 _ _ h3⟩, ⟨y4, e4, hk.2.1 _ _ h4⟩, l5, l6,
    ⟨y7, e7, hk.2.1 _ _ h7⟩, ⟨y8, e8, hk.2.1 _ _ h8⟩, ⟨y9, e9, hk.2.1 _ _ h9⟩,
    ⟨y10, e10, hk.2.1 _ _ h10⟩, ⟨y11, e11, hk.2.1 _ _ h11⟩, ⟨y12, e12, hk.2.1 _ _ h12⟩,
    ⟨y13, e13, hk.2.1 _ _ h13⟩⟩

theorem heap_setObj_ws_self {σ : State} {w : Addr} {fs fs' : List (FieldKey × Value)}
    (hw : σ.heap w = some (.plain "Cbtrn03c$Ws" fs)) :
    (σ.setObj w (.plain "Cbtrn03c$Ws" fs')).heap w = some (.plain "Cbtrn03c$Ws" fs') := by
  rw [State.heap_setObj_of_lt (State.lt_next_of_heap hw), if_pos rfl]

/-- Two writes to the working state's object (the two totals updated in turn). -/
theorem top_recsAt_setObj_ws2 {σ : State} {w : Addr} {fs fs1 fs2 : List (FieldKey × Value)}
    {ys : List Value} {ss : List JStr} (hw : σ.heap w = some (.plain "Cbtrn03c$Ws" fs))
    (h : Top.RecsAt σ ys ss) :
    Top.RecsAt ((σ.setObj w (.plain "Cbtrn03c$Ws" fs1)).setObj w (.plain "Cbtrn03c$Ws" fs2))
      ys ss :=
  top_recsAt_setObj_ws (heap_setObj_ws_self hw) (top_recsAt_setObj_ws hw h)

theorem tranFields_setObj_ws2 {σ : State} {w c : Addr} {fs fs1 fs2 : List (FieldKey × Value)}
    {t : List EquivLean.Cobol.Rec.FVal} (hw : σ.heap w = some (.plain "Cbtrn03c$Ws" fs))
    (h : Top.TranFields σ c t) :
    Top.TranFields ((σ.setObj w (.plain "Cbtrn03c$Ws" fs1)).setObj w (.plain "Cbtrn03c$Ws" fs2))
      c t :=
  tranFields_setObj_ws (heap_setObj_ws_self hw) (tranFields_setObj_ws hw h)

theorem keepsNonWs_setObj_ws2 {σ0 σ : State} {w : Addr} {fs fs1 fs2 : List (FieldKey × Value)}
    (hw : σ.heap w = some (.plain "Cbtrn03c$Ws" fs)) (hk : Top.KeepsNonWs σ0 σ) :
    Top.KeepsNonWs σ0
      ((σ.setObj w (.plain "Cbtrn03c$Ws" fs1)).setObj w (.plain "Cbtrn03c$Ws" fs2)) :=
  keepsNonWs_setObj_ws (heap_setObj_ws_self hw) (keepsNonWs_setObj_ws hw hk)

/-! ## The callees' contracts, with posts that compose

Each callee's frame `KeepsNonWs σ σ'` restated as what the caller's facts need: an earlier
`KeepsNonWs σ0 σ`, a transaction record and the strings of `σ` carry over to `σ'`. -/

/-- The frame part of the callees' posts. -/
def Carries (σ σ' : State) : Prop :=
  (∀ σ0, Top.KeepsNonWs σ0 σ → Top.KeepsNonWs σ0 σ') ∧
  (∀ c t, Top.TranFields σ c t → Top.TranFields σ' c t) ∧ StrMono σ σ'

theorem carries_of {σ σ' : State} (hk : Top.KeepsNonWs σ σ') : Carries σ σ' :=
  ⟨fun _ h0 => keepsNonWs_trans h0 hk, fun _ _ h => tranFields_keeps hk h, hk.2.1⟩

def headersSpecR : Spec := Spec.of writeHeadersSpecM.pre
  (fun args σ r σ' => ∀ w ld lr d s, args = [.ref w] → Top.WsRel σ w ld lr d s →
     s.first = false → WsDateparmRecord.Valid d →
     r = none ∧ Top.WsRel σ' w ld lr d (Model.headers s) ∧ Carries σ σ' ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def pageSpecR : Spec := Spec.of Top.writePageTotalsSpecM.pre
  (fun args σ r σ' => ∀ w ld lr d s, args = [.ref w] → Top.WsRel σ w ld lr d s →
     r = none ∧ Top.WsRel σ' w ld lr d (Model.pageTotals s) ∧ Carries σ σ' ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def detailSpecR : Spec := Spec.of writeDetailSpecM.pre
  (fun args σ r σ' => ∀ w ld lr c ty ca d s t y cc, args = [.ref w, .ref c, .ref ty, .ref ca] →
     Top.WsRel σ w ld lr d s → Top.TranFields σ c t → TranRecord.Valid t →
     TranTypeRecord.Valid y → TranCatRecord.Valid cc →
     (Model.xAcct s.xref).natAbs < 100000000000 →
     σ.heap ty = some (.str (cp037Str (Model.yDesc y))) →
     σ.heap ca = some (.str (cp037Str (Model.cDesc cc))) →
     r = none ∧ Top.WsRel σ' w ld lr d (Model.inc (Model.wr s (Model.detailLine t s.xref y cc))) ∧
     Carries σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

theorem headersR_sat : Sat Gen.prog writeHeadersRef headersSpecR := by
  refine Sat.conseq writeHeadersM_sat (fun _ _ h => h) ?_
  intro args σ o _ ho
  cases o with
  | normal r σ' =>
    intro w ld lr d s h1 h2 h3 h4
    obtain ⟨e, hR, hk, hi, hs⟩ := ho w ld lr d s h1 h2 h3 h4
    exact ⟨e, hR, carries_of hk, hi, hs⟩
  | exc e σ' => exact ho
  | wrong m => exact ho

theorem pageR_sat : Sat Gen.prog writePageTotalsRef pageSpecR := by
  refine Sat.conseq writePageTotalsM_sat (fun _ _ h => h) ?_
  intro args σ o _ ho
  cases o with
  | normal r σ' =>
    intro w ld lr d s h1 h2
    obtain ⟨e, hR, hk, hi, hs⟩ := ho w ld lr d s h1 h2
    exact ⟨e, hR, carries_of hk, hi, hs⟩
  | exc e σ' => exact ho
  | wrong m => exact ho

theorem detailR_sat : Sat Gen.prog writeDetailRef detailSpecR := by
  refine Sat.conseq writeDetailM_sat (fun _ _ h => h) ?_
  intro args σ o _ ho
  cases o with
  | normal r σ' =>
    intro w ld lr c ty ca d s t y cc h1 h2 h3 h4 h5 h6 h7 h8 h9
    obtain ⟨e, hR, hk, hi, hs⟩ := ho w ld lr c ty ca d s t y cc h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨e, hR, carries_of hk, hi, hs⟩
  | exc e σ' => exact ho
  | wrong m => exact ho

set_option maxHeartbeats 0 in
theorem headersR_ok : ContractOK Gen.prog writeHeadersSig headersSpecR := by
  jcontract_ok [headersR_sat]

set_option maxHeartbeats 0 in
theorem pageR_ok : ContractOK Gen.prog Top.writePageTotalsSig pageSpecR := by
  jcontract_ok [pageR_sat]

set_option maxHeartbeats 0 in
theorem detailR_ok : ContractOK Gen.prog writeDetailSig detailSpecR := by
  jcontract_ok [detailR_sat]

def reportCalleesR : Contracts :=
  [(writeHeadersSig, headersSpecR), (Top.writePageTotalsSig, pageSpecR),
   (writeDetailSig, detailSpecR), (add11Sig, add11Spec)]

theorem reportCalleesR_valid : Valid Gen.prog reportCalleesR.env := by
  apply Contracts.valid_of_ok
  simp only [reportCalleesR, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨headersR_ok, pageR_ok, detailR_ok, add11_ok⟩

theorem add11_ofInt_lit (a b : Int) (ha : a.natAbs < 100000000000)
    (hb : b.natAbs < 100000000000) :
    (BitVec.ofInt 64 a + BitVec.ofInt 64 b).srem 100000000000#64 =
      BitVec.ofInt 64 (Model.trunc11 (a + b)) := by
  have h := add11J_ofInt a b ha hb
  unfold add11J at h
  rwa [show BitVec.ofInt 64 100000000000 = 100000000000#64 from by decide] at h

theorem srem20_ofNat (n : Nat) (h : n < 1000000000) :
    (BitVec.ofNat 64 n).srem 20#64 = BitVec.ofNat 64 (n % 20) := by
  have h2 : 0 ≤ (BitVec.ofNat 64 n).toInt := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]; split <;> omega
  have h3 : 0 ≤ (20#64 : BitVec 64).toInt := by decide
  apply BitVec.eq_of_toNat_eq
  have e := srem_toNat_of_nonneg _ _ h2 h3
  have e1 : (BitVec.ofNat 64 n).toNat = n := by simp only [BitVec.toNat_ofNat]; omega
  have e2 : (20#64 : BitVec 64).toNat = 20 := by decide
  have e3 : (BitVec.ofNat 64 (n % 20)).toNat = n % 20 := by simp only [BitVec.toNat_ofNat]; omega
  rw [e, e1, e2, e3]

theorem ofNat64_eq_zero_iff (n : Nat) (h : n < 1000000000) :
    BitVec.ofNat 64 n = 0#64 ↔ n = 0 := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  · rintro rfl; rfl

/-! ## `writeTransactionReport` for given ghost values -/

def wtrSpecG (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) : Spec := Spec.of
  (fun args σ => args = [.ref w, .ref c, .ref ty, .ref ca] ∧ Top.WsRel σ w ld lr d s ∧
     Top.TranFields σ c t ∧ σ.heap ty = some (.str (cp037Str (Model.yDesc y))) ∧
     σ.heap ca = some (.str (cp037Str (Model.cDesc cc))) ∧
     σ.initOf "Cbtrn03c" = .done ∧ σ.initOf fdC = .done)
  (fun args σ r σ' => r = none ∧ Top.WsRel σ' w ld lr d (Model.report d s t y cc) ∧
     Top.KeepsNonWs σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- The facts every cut carries besides the model state. -/
def wtrK (w c ty ca : Addr) (t y cc : List EquivLean.Cobol.Rec.FVal) (σ0 : State) (fr : Frame)
    (σ : State) : Prop :=
  fr.get 0 = some (.ref w) ∧ fr.get 6 = some (.ref c) ∧ fr.get 4 = some (.ref ty) ∧
  fr.get 5 = some (.ref ca) ∧ Top.TranFields σ c t ∧
  σ.heap ty = some (.str (cp037Str (Model.yDesc y))) ∧
  σ.heap ca = some (.str (cp037Str (Model.cDesc cc))) ∧ Top.KeepsNonWs σ0 σ ∧
  σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
  σ0.initOf "Cbtrn03c" = .done ∧ σ0.initOf fdC = .done

def wtrInv (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) : Invariants :=
  [(7, fun _ σ0 fr σ => Top.WsRel σ w ld lr d (rep0 d s) ∧ (rep0 d s).first = false ∧
      s.first = true ∧ wtrK w c ty ca t y cc σ0 fr σ),
   (8, fun _ σ0 fr σ => Top.WsRel σ w ld lr d (rep1 d s) ∧ wtrK w c ty ca t y cc σ0 fr σ),
   (12, fun _ σ0 fr σ => Top.WsRel σ w ld lr d (rep1 d s) ∧ (rep1 d s).lc % 20 = 0 ∧
      wtrK w c ty ca t y cc σ0 fr σ),
   (13, fun _ σ0 fr σ => Top.WsRel σ w ld lr d (Model.pageTotals (rep1 d s)) ∧
      (Model.pageTotals (rep1 d s)).first = false ∧ (rep1 d s).lc % 20 = 0 ∧
      wtrK w c ty ca t y cc σ0 fr σ),
   (14, fun _ σ0 fr σ => Top.WsRel σ w ld lr d (rep2 (rep1 d s)) ∧
      wtrK w c ty ca t y cc σ0 fr σ),
   (22, fun _ σ0 fr σ => Top.WsRel σ w ld lr d (rep3 (rep2 (rep1 d s)) t) ∧
      (Model.xAcct (rep3 (rep2 (rep1 d s)) t).xref).natAbs < 100000000000 ∧
      wtrK w c ty ca t y cc σ0 fr σ)]

/-- The paths of `writeTransactionReport` from statement `pc`. -/
def wtrWP (w ld lr c ty ca : Addr) (d : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (t y cc : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (pc : Nat)
    (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog reportCalleesR.env 0)
    Gen.Cbtrn03c.«writeTransactionReport(Cbtrn03c$Ws,Cbtrn03c$TranRecord,java.lang.String,java.lang.String)»
    ((wtrInv w ld lr c ty ca d s t y cc).inst args σ0)
    ((wtrSpecG w ld lr c ty ca d s t y cc).post args σ0) 100 pc fr σ

end EquivLean.Modernize.Cbtrn03c.Java
