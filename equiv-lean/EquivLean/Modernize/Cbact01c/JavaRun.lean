import EquivLean.Modernize.Cbact01c.JavaRunVC
import EquivLean.Modernize.Cbact01c.JavaProof

/-!
# CBACT01C → Java: linking the contracts

Each helper was verified against the contracts of its callees; the record methods against
contracts stated for an arbitrary list address `L`. `run` uses them for the lists of its own
`Result` (`*SpecR σ0`, the record objects of the entry state `σ0`): these follow from the first
by the frames of `Frames.lean`. Bottom-up, `run_sat`.
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

/-- A contract implies a weaker one. -/
theorem Sat.mono {P : Program} {m : MethodRef} {S S' : Spec} (h : Sat P m S)
    (hpre : ∀ args σ, S'.pre args σ → S.pre args σ)
    (hpost : ∀ args σ o, S'.pre args σ → S.post args σ o → S'.post args σ o) : Sat P m S' :=
  fun args σ o hp hm => hpost _ _ _ hp (h _ _ _ (hpre _ _ hp) hm)

/-- The frame of a callee that changes only `L` (above `σ0.next`) keeps `σ0`'s objects. -/
theorem grows_frame1 {σ0 σ σ' : Jimple.State} {L : Addr} (hg : Grows σ0 σ) (hL : σ0.next < L)
    (hnext : σ.next ≤ σ'.next) (hframe : ∀ x, x < σ.next → x ≠ L → σ'.heap x = σ.heap x) :
    Grows σ0 σ' :=
  ⟨Nat.le_trans hg.1 hnext, fun x hx => by
    rw [hframe x (Nat.lt_of_lt_of_le hx hg.1) (Nat.ne_of_lt (Nat.lt_trans hx hL)), hg.2 x hx]⟩

theorem grows_frame2 {σ0 σ σ' : Jimple.State} {L1 L4 : Addr} (hg : Grows σ0 σ)
    (hL1 : σ0.next < L1) (hL4 : σ0.next < L4) (hnext : σ.next ≤ σ'.next)
    (hframe : ∀ x, x < σ.next → x ≠ L1 → x ≠ L4 → σ'.heap x = σ.heap x) : Grows σ0 σ' :=
  ⟨Nat.le_trans hg.1 hnext, fun x hx => by
    rw [hframe x (Nat.lt_of_lt_of_le hx hg.1) (Nat.ne_of_lt (Nat.lt_trans hx hL1))
      (Nat.ne_of_lt (Nat.lt_trans hx hL4)), hg.2 x hx]⟩

theorem grows_trans' {σ0 σ σ' : Jimple.State} (h1 : Grows σ0 σ) (h2 : Grows σ σ') :
    Grows σ0 σ' :=
  ⟨Nat.le_trans h1.1 h2.1, fun x hx => by rw [h2.2 x (Nat.lt_of_lt_of_le hx h1.1), h1.2 x hx]⟩

theorem initOf_done {σ σ' : Jimple.State} (hi : σ'.inits = σ.inits)
    (h : σ.initOf "Cbact01c" = .done) : σ'.initOf "Cbact01c" = .done :=
  (State.initOf_eq_of_inits hi _).trans h

/-! ## The helpers -/

theorem spaces_satF : Sat Gen.prog spacesRef spacesSpecF := spaces_vcF.sat
theorem pad_sat : Sat Gen.prog padRef padSpec := pad_vc.sat
theorem pad_satF : Sat Gen.prog padRef padSpecF := pad_vcF.sat
theorem zoned_sat : Sat Gen.prog zonedRef zonedSpec := zoned_vc.sat
theorem cobdatft_sat : Sat Gen.prog cobdatftRef cobdatftSpec := cobdatft_vc.sat

set_option maxHeartbeats 0 in
theorem spaces_okF : ContractOK Gen.prog spacesSig spacesSpecF := by jcontract_ok [spaces_satF]
set_option maxHeartbeats 0 in
theorem pad_ok : ContractOK Gen.prog padSig padSpec := by jcontract_ok [pad_sat]
set_option maxHeartbeats 0 in
theorem pad_okF : ContractOK Gen.prog padSig padSpecF := by jcontract_ok [pad_satF]
set_option maxHeartbeats 0 in
theorem zoned_ok : ContractOK Gen.prog zonedSig zonedSpec := by jcontract_ok [zoned_sat]

theorem textCallees_valid : Valid Gen.prog textCallees.env := by
  apply Contracts.valid_of_ok
  simp only [textCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  exact ⟨zoned_ok, pad_ok⟩

theorem accountRecordText_sat : Sat Gen.prog accountRecordTextRef accountRecordTextSpec :=
  MethodVC.sat_of_valid textCallees_valid accountRecordText_vc

theorem displayAcctRecord_sat (L : Addr) :
    Sat Gen.prog displayAcctRecordRef (displayAcctRecordSpec L) :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    simp only [dispCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact zoned_ok)) (displayAcctRecord_vc L)

theorem writeOutRecord_sat (L : Addr) :
    Sat Gen.prog writeOutRecordRef (writeOutRecordSpec L) :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    simp only [outCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact pad_okF)) (writeOutRecord_vc L)

theorem writeArrayRecord_sat (L : Addr) :
    Sat Gen.prog writeArrayRecordRef (writeArrayRecordSpec L) :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    simp only [arrCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact spaces_okF)) (writeArrayRecord_vc L)

theorem writeVbrcRecords_sat (L1 L4 : Addr) :
    Sat Gen.prog writeVbrcRecordsRef (writeVbrcRecordsSpec L1 L4) :=
  MethodVC.sat_of_valid textCallees_valid (writeVbrcRecords_vc L1 L4)

/-! ## The contracts `run` uses -/

theorem padR_sat (σ0 : Jimple.State) : Sat Gen.prog padRef (padSpecR σ0) := by
  refine Sat.mono pad_sat (fun _ _ h => h.1) ?_
  rintro args σ o ⟨-, h4, hg0, hI⟩ hp
  cases o with
  | normal r σ' =>
    intro sv n hargs
    obtain ⟨x, hr, hx, hg, hi, hs⟩ := hp sv n hargs
    exact ⟨x, hr, hx, Nat.lt_of_lt_of_le h4 hg.1, grows_trans' hg0 hg, initOf_done hi hI, hg, hi,
      hs⟩
  | exc e σ' => exact hp
  | wrong m => exact hp

theorem cobdatftR_sat (σ0 : Jimple.State) : Sat Gen.prog cobdatftRef (cobdatftSpecR σ0) := by
  refine Sat.mono cobdatft_sat (fun _ _ h => h.1) ?_
  rintro args σ o ⟨⟨x1, x2, x3, x4, s2, s4, rfl, -⟩, h4, hg0, hI⟩ hp
  cases o with
  | normal r σ' =>
    obtain ⟨x, hr, hx, hfresh, hg, hi, hs⟩ := hp x1 x2 x3 x4 rfl
    show ∃ x, _
    exact ⟨x, hr, hx, hfresh, Nat.lt_of_lt_of_le h4 hg.1, grows_trans' hg0 hg, initOf_done hi hI,
      hg, hi, hs⟩
  | exc e σ' => exact hp
  | wrong m => exact hp

theorem accountRecordTextR_sat (σ0 : Jimple.State) :
    Sat Gen.prog accountRecordTextRef (accountRecordTextSpecR σ0) := by
  refine Sat.mono accountRecordText_sat ?_ ?_
  · rintro args σ ⟨c, hargs, hok, hg, -, hi⟩
    exact ⟨c, hargs, acctOk_of_grows hg (Hide.elim hok), hi⟩
  · rintro args σ o ⟨c, rfl, hok, hg, h4, hI⟩ hp
    cases o with
    | normal r σ' =>
      intro c' hargs
      simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
      subst hargs
      obtain ⟨x, hr, hx, hfresh, hg', hi, hs⟩ := hp c rfl
      rw [(texts_of_grows hg (Hide.elim hok)).2.1] at hx
      exact ⟨x, hr, hx, hfresh, Nat.lt_of_lt_of_le h4 hg'.1, grows_trans' hg hg',
        initOf_done hi hI, hg', hi, hs⟩
    | exc e σ' => exact hp
    | wrong m => exact hp

theorem displayAcctRecordR_sat (σ0 : Jimple.State) (L : Addr) (hL : σ0.next < L) :
    Sat Gen.prog displayAcctRecordRef (displayAcctRecordSpecR σ0 L) := by
  refine Sat.mono (displayAcctRecord_sat L) ?_ ?_
  · rintro args σ ⟨res, c, fs, ys, m, hargs, hres, hfs, hl, hrl, hok, hg, -, hi⟩
    exact ⟨res, c, fs, ys, m, hargs, hres, hfs, hl, hrl, State.lt_next_of_heap hl,
      acctOkB_of_grows hg (Hide.elim hok) (by jomega), hi⟩
  · rintro args σ o ⟨res, c, fs, ys, m, rfl, hres, hfs, hl, hrl, hok, hg, h4, hI⟩ hp
    cases o with
    | normal r σ' =>
      intro res' c' hargs
      simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain ⟨hr, hw, hnext, hframe, hi, hs⟩ := hp res c rfl
      have ht : ∀ i, dispLine σ c i = dispLine σ0 c i := by
        intro i; simp only [dispLine, (texts_of_grows hg (Hide.elim hok)).1]
      simp only [ht] at hw
      exact ⟨hr, hw, hnext, Nat.lt_of_lt_of_le h4 hnext, grows_frame1 hg hL hnext hframe,
        initOf_done hi hI, hframe, hi, hs⟩
    | exc e σ' => exact hp
    | wrong m => exact hp

theorem writeOutRecordR_sat (σ0 : Jimple.State) (L : Addr) (hL : σ0.next < L) :
    Sat Gen.prog writeOutRecordRef (writeOutRecordSpecR σ0 L) := by
  refine Sat.mono (writeOutRecord_sat L) ?_ ?_
  · rintro args σ ⟨res, c, d, cd, fs, ys, m, sd, hargs, hres, hfs, hl, hrl, hok, hg, -, hd, hsd,
      hdL, hi1, hi2⟩
    exact ⟨res, c, d, cd, fs, ys, m, sd, hargs, hres, hfs, hl, hrl, State.lt_next_of_heap hl,
      acctOkB_of_grows hg (Hide.elim hok) (by jomega), hd, hsd, hdL, hi1, hi2⟩
  · rintro args σ o ⟨res, c, d, cd, fs, ys, m, sd, rfl, hres, hfs, hl, hrl, hok, hg, h4, -, -, -,
      hI, -⟩ hp
    cases o with
    | normal r σ' =>
      obtain ⟨hr, ⟨ob, hob, hfresh, hrec⟩, hnext, hframe, hi, hs⟩ := hp res c d cd rfl
      show r = none ∧ _
      exact ⟨hr, ⟨ob, hob, hfresh, outRecJ_of_grows hg (Hide.elim hok) hrec⟩, hnext,
        Nat.lt_of_lt_of_le h4 hnext, grows_frame1 hg hL hnext hframe, initOf_done hi hI, hframe,
        hi, hs⟩
    | exc e σ' => exact hp
    | wrong m => exact hp

theorem writeArrayRecordR_sat (σ0 : Jimple.State) (L : Addr) (hL : σ0.next < L) :
    Sat Gen.prog writeArrayRecordRef (writeArrayRecordSpecR σ0 L) := by
  refine Sat.mono (writeArrayRecord_sat L) ?_ ?_
  · rintro args σ ⟨res, c, fs, ys, m, hargs, hres, hfs, hl, hrl, hok, hg, -, hi1, hi2⟩
    exact ⟨res, c, fs, ys, m, hargs, hres, hfs, hl, hrl, State.lt_next_of_heap hl,
      acctOkB_of_grows hg (Hide.elim hok) (by jomega), hi1, hi2⟩
  · rintro args σ o ⟨res, c, fs, ys, m, rfl, hres, hfs, hl, hrl, hok, hg, h4, hI, -⟩ hp
    cases o with
    | normal r σ' =>
      intro res' c' hargs
      simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain ⟨hr, ⟨ob, hob, hfresh, hrec⟩, hnext, hframe, hi, hs⟩ := hp res c rfl
      exact ⟨hr, ⟨ob, hob, hfresh, arrRecJ_of_grows hg (Hide.elim hok) hrec⟩, hnext,
        Nat.lt_of_lt_of_le h4 hnext, grows_frame1 hg hL hnext hframe, initOf_done hi hI, hframe,
        hi, hs⟩
    | exc e σ' => exact hp
    | wrong m => exact hp

theorem writeVbrcRecordsR_sat (σ0 : Jimple.State) (L1 L4 : Addr) (hL : σ0.next < L1)
    (h14 : L1 < L4) : Sat Gen.prog writeVbrcRecordsRef (writeVbrcRecordsSpecR σ0 L1 L4) := by
  refine Sat.mono (writeVbrcRecords_sat L1 L4) ?_ ?_
  · rintro args σ ⟨res, c, fs, ys1, m1, ys4, m4, hargs, hres, hf1, hf4, hrl, hl1, hl4, hok, hg, -,
      hi⟩
    exact ⟨res, c, fs, ys1, m1, ys4, m4, hargs, hres, hf1, hf4, h14, hrl,
      State.lt_next_of_heap hl4, hl1, hl4, acctOkB_of_grows hg (Hide.elim hok) (by jomega), hi⟩
  · rintro args σ o ⟨res, c, fs, ys1, m1, ys4, m4, rfl, hres, hf1, hf4, hrl, hl1, hl4, hok, hg, h4,
      hI⟩ hp
    cases o with
    | normal r σ' =>
      intro res' c' hargs
      simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain ⟨hr, hy, hw, hnext, hframe, hi, hs⟩ := hp res c rfl
      have ht := texts_of_grows hg (Hide.elim hok)
      rw [ht.2.2.1, ht.2.2.2.1] at hy hw
      exact ⟨hr, hy, hw, hnext, Nat.lt_of_lt_of_le h4 hnext,
        grows_frame2 hg hL (Nat.lt_trans hL h14) hnext hframe, initOf_done hi hI, hframe, hi, hs⟩
    | exc e σ' => exact hp
    | wrong m => exact hp

set_option maxHeartbeats 0 in
theorem runCallees_valid (σ0 : Jimple.State) : Valid Gen.prog (runCallees σ0).env := by
  apply Contracts.valid_of_ok
  simp only [runCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true]
  have h1 : σ0.next < σ0.next + 1 := by jomega
  have h2 : σ0.next < σ0.next + 2 := by jomega
  have h3 : σ0.next < σ0.next + 3 := by jomega
  have h14 : σ0.next + 1 < σ0.next + 4 := by jomega
  refine ⟨spaces_okF, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := padR_sat σ0; jcontract_ok [this]
  · have := cobdatftR_sat σ0; jcontract_ok [this]
  · have := displayAcctRecordR_sat σ0 _ h1; jcontract_ok [this]
  · have := writeOutRecordR_sat σ0 _ h2; jcontract_ok [this]
  · have := writeArrayRecordR_sat σ0 _ h3; jcontract_ok [this]
  · have := writeVbrcRecordsR_sat σ0 _ _ h1 h14; jcontract_ok [this]
  · have := accountRecordTextR_sat σ0; jcontract_ok [this]

/-- `run` against the contract with fixed ghost values. -/
theorem run_satG (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal)) :
    Sat Gen.prog runRefJ (runSpecG σ0 a vals) :=
  MethodVC.sat_of_valid (runEnv_valid (runCallees_valid σ0)) (run_vc σ0 a vals)

/-- **CBACT01C, Java side**: the contract `runSpec` of `Cbact01c.run` holds in the program. -/
theorem run_sat : Sat Gen.prog runRef runSpec := by
  intro args σ o hpre hm
  obtain ⟨vals, ⟨a, rfl, hfile, hvalid⟩, i1, i2, i3, i4, i5⟩ := hpre
  have hI : Inits σ := ⟨i1, i2, i3, i4, i5⟩
  have h0 := run_satG σ a vals _ σ o ⟨rfl, rfl, hfile, hvalid, hI⟩ hm
  cases o with
  | normal r σ' =>
    intro vals' ⟨a', hargs, hfile', hvalid'⟩
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    subst hargs
    exact run_satG σ a vals' _ σ _ ⟨rfl, rfl, hfile', hvalid', hI⟩ hm
  | exc e σ' => exact h0
  | wrong msg => exact h0

/-- **CBACT01C → Java, every input** (guided-v2 translation): the generated statement
(`JavaStatement.lean`). -/
theorem java : Statement := statement_of_sat run_sat

end EquivLean.Modernize.Cbact01c.Java

#print axioms EquivLean.Modernize.Cbact01c.Java.run_sat
#print axioms EquivLean.Modernize.Cbact01c.Java.java
