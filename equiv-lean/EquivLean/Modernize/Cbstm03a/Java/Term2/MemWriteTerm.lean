import EquivLean.Modernize.Cbstm03a.Java.Term2.WrSlotB
import EquivLean.Modernize.Cbstm03a.Java.Term2.Arith
import EquivLean.Modernize.Cbstm03a.Java.Term2.Leaves

/-!
# CBSTM03A → Java, termination: `memWrite`

The loop head's cases (`pos ≥ n`; `off + pos < 0`; `off + pos ≥ MEM_SZ`; a slot step through the extra cut points
17 and 26), the termination VC `memWrite_tvc`, and `memWrite_cterm` for `memWriteSpec` (`CbAMem.Iface2`), given the
contracts of `spaces` (validity and termination) and of the slot helpers (validity).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

open EquivLean.Modernize.Cbstm03a.Java

/-- A slot step: statements 5 … 37 through the extra cut points 17 (`WrO`) and 26 (`WrTk`). -/
theorem wr_tslot (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (x : Addr)
    (t : JStr) (vs : List Value) (n pos : I32) (v : Nat) (ha : args = [.ref a, .long off, .ref x])
    (h : WrAt fr σ a off x t vs n pos) (hv : v = (2147483648 - pos.toInt).toNat) (hx : pos.toInt < n.toInt)
    (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt) (h0 : 0 ≤ off.toInt + pos.toInt)
    (h1 : off.toInt + pos.toInt < 171156) :
    wrTWP [(5, fun fr σ => wrInv args σ0 fr σ ∧ wrVar args σ0 fr σ < v)] 60 5 fr σ := by
  have h' := h
  obtain ⟨hf0, hf1, hf5, hf10, hf12, hxs, hav, hok, hoff0, hp0, hpo, hinit⟩ := h'
  have hoff1 : off.toInt < 171156 := by rcases hpo with e | e <;> omega
  have e5 := wr_tslot5 args σ0 fr σ a off x t vs n pos v h hx ho h0 h1
  unfold wrTWP at e5 ⊢
  refine bodyWP_cutT (A := WrO a off x t vs n pos) (m := 40) rfl ?_ 20 5 fr σ e5
  intro fr1 σ1 hO
  obtain ⟨o, g0, g1, g2, g5, g10, g12, gx, gav, gok, goff0, goff1, gp0, gpn, go0, go1, ginit⟩ := hO
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
  have e17 := wr_tslot17 args σ0 fr1 σ1 a off x t vs n pos v o (slotIdx o.toNat)
    (BitVec.ofNat 32 (slotIdx o.toNat)) (BitVec.ofNat 32 (slotLn (BitVec.ofNat 32 (slotIdx o.toNat)).toNat))
    (JLong.toInt (o - BitVec.ofNat 64 (slotSt (BitVec.ofNat 32 (slotIdx o.toNat)).toNat)))
    (BitVec.ofNat 64 (slotSt (BitVec.ofNat 32 (slotIdx o.toNat)).toNat))
    g0 g1 g2 g5 g10 g12 gx gav gok goff0 goff1 gp0 gpn go0 go1 ginit rfl rfl rfl rfl rfl hit hk1
    (by rw [hl]; omega) (by rw [hl]; omega) (by rw [hw]; omega) (by rw [hw, hl]; omega)
  unfold wrTWP at e17
  refine bodyWP_cutT (A := WrTk a off x t vs n pos) (m := 20) rfl ?_ 20 17 fr1 σ1 e17
  intro fr2 σ2 hT
  obtain ⟨idx, len, within, take, k0, k1, k5, k6, k7, k8, k10, k11, k12, kx, kav, kok, koff0, koff1, kp0, ktk1,
    ktk2, klen, kinit⟩ := hT
  by_cases hb : 0 ≤ idx.toInt ∧ idx.toInt < vs.length
  · have hb' : (BitVec.toInt idx).toNat < vs.length := by omega
    rcases kok (vs[(BitVec.toInt idx).toNat]) (List.getElem_mem hb') with hn | ⟨y, s, hy, hys⟩
    · have e := wr_tslot26n args σ0 fr2 σ2 a off x t vs n pos v idx len within take ha k0 k1 k5 k6 k7 k8 k10 k11
        k12 kx kav kok koff0 koff1 kp0 ktk1 ktk2 klen kinit hv hb.1 hb.2 hb' hn
      unfold wrTWP at e
      exact e
    · have e := wr_tslot26s args σ0 fr2 σ2 a off x t vs n pos v idx len within take ha k0 k1 k5 k6 k7 k8 k10 k11
        k12 kx kav kok koff0 koff1 kp0 ktk1 ktk2 klen kinit hv hb.1 hb.2 hb' y s hy hys
      unfold wrTWP at e
      exact e
  · have e := wr_tslot26o args σ0 fr2 σ2 a off x t vs n pos v idx len within take k0 k6 kav hb
    unfold wrTWP at e
    exact e

/-- The paths from the loop head. -/
theorem wr_tloop (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (x : Addr)
    (t : JStr) (vs : List Value) (n pos : I32) (ha : args = [.ref a, .long off, .ref x])
    (h : WrAt fr σ a off x t vs n pos) :
    wrTWP (wrTerm.dec args σ0 (wrVar args σ0 fr σ)) 60 5 fr σ := by
  have h' := h
  obtain ⟨hf0, hf1, hf5, hf10, hf12, hxs, hav, hok, hoff0, hp0, hpo, hinit⟩ := h'
  have hv : wrVar args σ0 fr σ = (2147483648 - pos.toInt).toNat := by simp [wrVar, hf10]
  show wrTWP [(5, fun fr' σ' => wrInv args σ0 fr' σ' ∧ wrVar args σ0 fr' σ' < wrVar args σ0 fr σ)] 60 5 fr σ
  by_cases hx : n.toInt ≤ pos.toInt
  · exact wr_texit args σ0 fr σ a off x t vs n pos h hx
  have hx : pos.toInt < n.toInt := by omega
  have hoff2 := BitVec.toInt_lt (x := off)
  have hpos2 := BitVec.toInt_lt (x := pos)
  have ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt := by
    rw [toInt_add64 _ _ (by rw [toLong_toInt]; omega) (by rw [toLong_toInt]; simp at hoff2 hpos2; omega),
      toLong_toInt]
  rcases Int.lt_or_le (off.toInt + pos.toInt) 0 with hneg | h0
  · have hn : (-off).toInt = -off.toInt := toInt_neg64 off (by omega)
    have hp : (JLong.toInt (-off)).toInt = -off.toInt := by
      rw [l2i_toInt _ (by rw [hn]; omega) (by rw [hn]; omega), hn]
    exact wr_tneg args σ0 fr σ a off x t vs n pos ha h hx ho hneg hp
  rcases Int.lt_or_le (off.toInt + pos.toInt) 171156 with h1 | hpast
  · exact wr_tslot args σ0 fr σ a off x t vs n pos _ ha h hv hx ho h0 h1
  · have hz : ¬(off + JInt.toLong pos = 0#64) := by
      intro e; rw [e] at ho; simp at ho; omega
    exact wr_tpast args σ0 fr σ a off x t vs n pos h hx ho hpast hz

theorem memWrite_tvc : TermVC Gen.prog memCallees.env (fun _ => 0) 1 0 memWriteRef memWriteSpec wrTerm 60 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · obtain ⟨a, off, x, m, t, ha, hs, hx, -, hoff, hinit⟩ := hpre
    have hs' := hs
    obtain ⟨vs, hav, -, -⟩ := hs'
    have e := wr_tentry args σ0 a off x t vs ha hx hav (slotOk_of_slotsAt hs hav) hoff hinit
    unfold wrTWP at e
    exact e
  · intro p hp fr σ hI
    simp only [wrTerm, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    obtain ⟨a, off, x, t, vs, n, pos, ha, h⟩ := hI
    have e := wr_tloop args σ0 fr σ a off x t vs n pos ha h
    unfold wrTWP at e
    exact e

theorem memCallees_term (hsp : ContractTerm Gen.prog spacesSig spacesSpecI) :
    ∀ p ∈ memCallees, ContractTerm Gen.prog p.1 p.2 := by
  simp only [memCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨slotIndex_cterm, slotLen_cterm, slotStart_cterm, hsp⟩

theorem memCallees_ok (hI : ContractOK Gen.prog slotIndexSig slotIndexSpec)
    (hL : ContractOK Gen.prog slotLenSig slotLenSpec) (hS : ContractOK Gen.prog slotStartSig slotStartSpec)
    (hsp : ContractOK Gen.prog spacesSig spacesSpecI) : ∀ p ∈ memCallees, ContractOK Gen.prog p.1 p.2 := by
  simp only [memCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨hI, hL, hS, hsp⟩

end EquivLean.Modernize.Cbstm03a.Java.Term2

namespace EquivLean.Modernize.Cbstm03a.Java

open Term2

/-- **`memWrite` terminates** on `memWriteSpec`'s inputs, given the contracts of its callees: `slotIndex`,
`slotLen`, `slotStart` hold (their termination is `slotIndex_cterm` …), `spaces` holds and terminates. -/
theorem memWrite_cterm (hI : ContractOK Gen.prog slotIndexSig slotIndexSpec)
    (hL : ContractOK Gen.prog slotLenSig slotLenSpec) (hS : ContractOK Gen.prog slotStartSig slotStartSpec)
    (hsp : ContractOK Gen.prog spacesSig spacesSpecI) (hspT : ContractTerm Gen.prog spacesSig spacesSpecI) :
    ContractTerm Gen.prog memWriteSig memWriteSpec := by
  have ht : ∀ args σ, memWriteSpec.pre args σ → MTerm Gen.prog memWriteRef args σ :=
    TermVC.mterm (Contracts.valid_of_ok (memCallees_ok hI hL hS hsp))
      (Contracts.term_of_ok (memCallees_term hspT) _ _) memWrite_tvc
  jcontract_term [ht]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.memWrite_cterm
