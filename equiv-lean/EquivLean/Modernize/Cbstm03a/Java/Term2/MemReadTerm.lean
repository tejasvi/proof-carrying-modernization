import EquivLean.Modernize.Cbstm03a.Java.Term2.RdSlot
import EquivLean.Modernize.Cbstm03a.Java.Term2.Arith
import EquivLean.Modernize.Cbstm03a.Java.Term2.Leaves

/-!
# CBSTM03A → Java, termination: `memRead`

The loop head's cases (`pos ≥ n`; `off + pos < 0`; `off + pos ≥ MEM_SZ`; a slot step through the extra cut points
28 and 37), the termination VC `memRead_tvc`, and `memRead_cterm` for `memReadSpec` (`CbAMem.Iface2`), given the
contracts of `spaces` (validity and termination) and of the slot helpers (validity).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

open EquivLean.Modernize.Cbstm03a.Java

/-- A slot step: statements 6 … 45 through the extra cut points 28 (`RdO`) and 37 (`RdTk`). -/
theorem rd_tslot (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (sb : Addr)
    (b : JStr) (vs : List Value) (n pos : I32) (v : Nat) (ha : args = [.ref a, .long off, .int n])
    (h : RdAt fr σ a off sb b vs n pos) (hv : v = (2147483648 - pos.toInt).toNat) (hx : pos.toInt < n.toInt)
    (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt) (h0 : 0 ≤ off.toInt + pos.toInt)
    (h1 : off.toInt + pos.toInt < 171156) :
    rdTWP [(6, fun fr σ => rdInv args σ0 fr σ ∧ rdVar args σ0 fr σ < v)] 60 6 fr σ := by
  have h' := h
  obtain ⟨hf0, hf1, hf5, hf10, hf12, hsb, hav, hok, hoff0, hp0, hpo, hn, hinit⟩ := h'
  have hoff1 : off.toInt < 171156 := by rcases hpo with e | e <;> omega
  have e6 := rd_tslot6 args σ0 fr σ a off sb b vs n pos v h hx ho h0 h1
  unfold rdTWP at e6 ⊢
  refine bodyWP_cutT (A := RdO a off sb b vs n pos) (m := 40) rfl ?_ 20 6 fr σ e6
  intro fr1 σ1 hO
  obtain ⟨o, g0, g1, g2, g5, g10, g12, gsb, gav, gok, goff0, goff1, gp0, gpn, gn, go0, go1, ginit⟩ := hO
  have hon : (o.toNat : Int) = o.toInt := toNat_of_toInt_nonneg64 o go0
  have hk1 : slotIdx o.toNat < 561 := slotIdx_lt _ (by omega)
  have hst := slotSt_le o.toNat
  have hen := lt_slotSt_add o.toNat
  have hin : (BitVec.ofNat 32 (slotIdx o.toNat)).toNat = slotIdx o.toNat := toNat_ofNat32 (by omega)
  have hit : (BitVec.ofNat 32 (slotIdx o.toNat)).toInt = (slotIdx o.toNat : Int) := toInt_ofNat32 (by omega)
  have hln := slotLn_cases (slotIdx o.toNat)
  have hl : (BitVec.ofNat 32 (slotLn (BitVec.ofNat 32 (slotIdx o.toNat)).toNat)).toInt =
      (slotLn (slotIdx o.toNat) : Int) := by
    rw [hin]; exact toInt_ofNat32 (by omega)
  have hs : (BitVec.ofNat 64 (slotSt (BitVec.ofNat 32 (slotIdx o.toNat)).toNat)).toInt =
      (slotSt (slotIdx o.toNat) : Int) := by
    rw [hin]; exact toInt_ofNat64 (by omega)
  have hsub : (o - BitVec.ofNat 64 (slotSt (BitVec.ofNat 32 (slotIdx o.toNat)).toNat)).toInt =
      o.toInt - (slotSt (slotIdx o.toNat) : Int) := by
    rw [toInt_sub64 _ _ (by rw [hs]; omega) (by rw [hs]; omega), hs]
  have hw : (JLong.toInt (o - BitVec.ofNat 64 (slotSt (BitVec.ofNat 32 (slotIdx o.toNat)).toNat))).toInt =
      o.toInt - (slotSt (slotIdx o.toNat) : Int) := by
    rw [l2i_toInt _ (by rw [hsub]; omega) (by rw [hsub]; omega), hsub]
  have e28 := rd_tslot28 args σ0 fr1 σ1 a off sb b vs n pos v o (slotIdx o.toNat)
    (BitVec.ofNat 32 (slotIdx o.toNat)) (BitVec.ofNat 32 (slotLn (BitVec.ofNat 32 (slotIdx o.toNat)).toNat))
    (JLong.toInt (o - BitVec.ofNat 64 (slotSt (BitVec.ofNat 32 (slotIdx o.toNat)).toNat)))
    (BitVec.ofNat 64 (slotSt (BitVec.ofNat 32 (slotIdx o.toNat)).toNat))
    g0 g1 g2 g5 g10 g12 gsb gav gok goff0 goff1 gp0 gpn gn go0 go1 ginit rfl rfl rfl rfl rfl hit hk1
    (by rw [hl]; omega) (by rw [hl]; omega) (by rw [hw]; omega) (by rw [hw, hl]; omega)
  unfold rdTWP at e28
  refine bodyWP_cutT (A := RdTk a off sb b vs n pos) (m := 20) rfl ?_ 20 28 fr1 σ1 e28
  intro fr2 σ2 hT
  obtain ⟨idx, len, within, take, k0, k1, k5, k6, k7, k9, k10, k11, k12, ksb, kav, kok, koff0, koff1, kp0, ktk1,
    ktk2, kn, kinit⟩ := hT
  by_cases hb : 0 ≤ idx.toInt ∧ idx.toInt < vs.length
  · have hb' : (BitVec.toInt idx).toNat < vs.length := by omega
    rcases kok (vs[(BitVec.toInt idx).toNat]) (List.getElem_mem hb') with hnl | ⟨y, s, hy, hys⟩
    · have e := rd_tslot37n args σ0 fr2 σ2 a off sb b vs n pos v idx len within take ha k0 k1 k5 k6 k7 k9 k10 k11
        k12 ksb kav kok koff0 koff1 kp0 ktk1 ktk2 kn kinit hv hb.1 hb.2 hb' hnl
      unfold rdTWP at e
      exact e
    · have e := rd_tslot37s args σ0 fr2 σ2 a off sb b vs n pos v idx len within take ha k0 k1 k5 k6 k7 k9 k10 k11
        k12 ksb kav kok koff0 koff1 kp0 ktk1 ktk2 kn kinit hv hb.1 hb.2 hb' y s hy hys
      unfold rdTWP at e
      exact e
  · have e := rd_tslot37o args σ0 fr2 σ2 a vs v idx k0 k9 kav hb
    unfold rdTWP at e
    exact e

/-- The paths from the loop head. -/
theorem rd_tloop (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (sb : Addr)
    (b : JStr) (vs : List Value) (n pos : I32) (ha : args = [.ref a, .long off, .int n])
    (h : RdAt fr σ a off sb b vs n pos) :
    rdTWP (rdTerm.dec args σ0 (rdVar args σ0 fr σ)) 60 6 fr σ := by
  have h' := h
  obtain ⟨hf0, hf1, hf5, hf10, hf12, hsb, hav, hok, hoff0, hp0, hpo, hn, hinit⟩ := h'
  have hv : rdVar args σ0 fr σ = (2147483648 - pos.toInt).toNat := by simp [rdVar, hf10]
  show rdTWP [(6, fun fr' σ' => rdInv args σ0 fr' σ' ∧ rdVar args σ0 fr' σ' < rdVar args σ0 fr σ)] 60 6 fr σ
  by_cases hx : n.toInt ≤ pos.toInt
  · exact rd_texit args σ0 fr σ a off sb b vs n pos h hx
  have hx : pos.toInt < n.toInt := by omega
  have hoff2 := BitVec.toInt_lt (x := off)
  have hpos2 := BitVec.toInt_lt (x := pos)
  have ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt := by
    rw [toInt_add64 _ _ (by rw [toLong_toInt]; omega) (by rw [toLong_toInt]; simp at hoff2 hpos2; omega),
      toLong_toInt]
  rcases Int.lt_or_le (off.toInt + pos.toInt) 0 with hneg | h0
  · have hn' : (-(off + JInt.toLong pos)).toInt = -(off.toInt + pos.toInt) := by
      rw [toInt_neg64 _ (by rw [ho]; omega), ho]
    have hsk : (JLong.toInt (-(off + JInt.toLong pos))).toInt = -(off.toInt + pos.toInt) := by
      rw [l2i_toInt _ (by rw [hn']; omega) (by rw [hn']; omega), hn']
    have hsk2 : (JLong.toInt (-JInt.toLong pos + -off)).toInt = -(off.toInt + pos.toInt) := by
      rw [← neg_add_rev]; exact hsk
    exact rd_tneg args σ0 fr σ a off sb b vs n pos ha hf0 hf1 hf5 hf10 hf12 hsb hav hok hoff0 hp0 hn hinit hx ho
      hneg hsk hsk2
  rcases Int.lt_or_le (off.toInt + pos.toInt) 171156 with h1 | hpast
  · exact rd_tslot args σ0 fr σ a off sb b vs n pos _ ha h hv hx ho h0 h1
  · have hz : ¬(off + JInt.toLong pos = 0#64) := by
      intro e; rw [e] at ho; simp at ho; omega
    exact rd_tpast args σ0 fr σ a off sb b vs n pos h hx ho hpast hz

theorem memRead_tvc : TermVC Gen.prog rdCallees.env (fun _ => 0) 1 0 memReadRef memReadSpec rdTerm 60 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · obtain ⟨a, off, n, m, ha, hs, hoff, hn, hinit⟩ := hpre
    have hs' := hs
    obtain ⟨vs, hav, -, -⟩ := hs'
    have e := rd_tentry args σ0 a off n vs ha hav (slotOk_of_slotsAt hs hav) hoff hn hinit
    unfold rdTWP at e
    exact e
  · intro p hp fr σ hI
    simp only [rdTerm, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    obtain ⟨a, off, sb, b, vs, n, pos, ha, h⟩ := hI
    have e := rd_tloop args σ0 fr σ a off sb b vs n pos ha h
    unfold rdTWP at e
    exact e

end EquivLean.Modernize.Cbstm03a.Java.Term2

namespace EquivLean.Modernize.Cbstm03a.Java

open Term2

/-- **`memRead` terminates** on `memReadSpec`'s inputs, given the contracts of its callees: `slotIndex`,
`slotLen`, `slotStart` hold (their termination is `slotIndex_cterm` …), `spaces` holds and terminates. -/
theorem memRead_cterm (hI : ContractOK Gen.prog slotIndexSig slotIndexSpec)
    (hL : ContractOK Gen.prog slotLenSig slotLenSpec) (hS : ContractOK Gen.prog slotStartSig slotStartSpec)
    (hsp : ContractOK Gen.prog spacesSig spacesSpecI) (hspT : ContractTerm Gen.prog spacesSig spacesSpecI) :
    ContractTerm Gen.prog memReadSig memReadSpec := by
  have hok : ∀ p ∈ rdCallees, ContractOK Gen.prog p.1 p.2 := by
    simp only [rdCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨hI, hL, hS, hsp⟩
  have htm : ∀ p ∈ rdCallees, ContractTerm Gen.prog p.1 p.2 := by
    simp only [rdCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨slotIndex_cterm, slotLen_cterm, slotStart_cterm, hspT⟩
  have ht : ∀ args σ, memReadSpec.pre args σ → MTerm Gen.prog memReadRef args σ :=
    TermVC.mterm (Contracts.valid_of_ok hok) (Contracts.term_of_ok htm _ _) memRead_tvc
  jcontract_term [ht]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.memRead_cterm
