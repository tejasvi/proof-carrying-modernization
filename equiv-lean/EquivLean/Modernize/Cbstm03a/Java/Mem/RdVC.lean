import EquivLean.Modernize.Cbstm03a.Java.Mem.RdLem
import EquivLean.Modernize.Cbstm03a.Java.Mem.Rd_entry
import EquivLean.Modernize.Cbstm03a.Java.Mem.Rd_exit
import EquivLean.Modernize.Cbstm03a.Java.Mem.Rd_skip

/-!
# CBSTM03A → Java: `memRead`'s verification conditions from its segments

Two cut points: the loop head (6) and after the slot read (38). From the loop head: `pos ≥ n` (`rd_exit`), `o < 0`
(`rd_skip`), `o ≥ MEM_SZ` (`RdPastSeg`), an in-range position up to the slot read (`RdPreSeg`); from the slot read:
a `null` slot (`RdN38Seg`) or a string slot (`RdS38Seg`). The open segments are hypotheses here; their statements
are those of `Rd_past.lean`, `Rd_pre.lean`, `Rd_n38.lean`, `Rd_s38.lean`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Mem

def RdPastSeg : Prop := ∀ (args : List Value) (σ0 : State), memReadSpec.pre args σ0 → ∀ (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (n : I32) (vs : List Value) (sb : Addr) (pos : I32) (t : JStr),
    args = [.ref a, .long off, .int n] → RdAt σ0 fr σ a off n vs sb pos t → pos.toInt < n.toInt →
    (off + JInt.toLong pos).toInt = off.toInt + pos.toInt → 171156 ≤ off.toInt + pos.toInt → rdWP args σ0 6 fr σ

def RdPreSeg : Prop := ∀ (args : List Value) (σ0 : State), memReadSpec.pre args σ0 → ∀ (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (n : I32) (vs : List Value) (sb : Addr) (pos : I32) (t : JStr),
    args = [.ref a, .long off, .int n] → RdAt σ0 fr σ a off n vs sb pos t → pos.toInt < n.toInt →
    (off + JInt.toLong pos).toInt = off.toInt + pos.toInt →
    (off + JInt.toLong pos).toNat = (off.toInt + pos.toInt).toNat →
    0 ≤ off.toInt + pos.toInt → off.toInt + pos.toInt < 171156 → (off.toInt + pos.toInt).toNat < 171156 →
    slotIdx (off.toInt + pos.toInt).toNat < 561 →
    slotSt (slotIdx (off.toInt + pos.toInt).toNat) ≤ (off.toInt + pos.toInt).toNat →
    (off.toInt + pos.toInt).toNat <
      slotSt (slotIdx (off.toInt + pos.toInt).toNat) + slotLn (slotIdx (off.toInt + pos.toInt).toNat) →
    (JLong.toInt (off + JInt.toLong pos - BitVec.ofNat 64 (slotSt (slotIdx (off.toInt + pos.toInt).toNat)))).toInt =
      off.toInt + pos.toInt - (slotSt (slotIdx (off.toInt + pos.toInt).toNat) : Int) →
    rdWP args σ0 6 fr σ

def RdN38Seg : Prop := ∀ (args : List Value) (σ0 : State), memReadSpec.pre args σ0 → ∀ (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (n : I32) (vs : List Value) (sb : Addr) (pos ix wv tk : I32) (cv : Value) (t : JStr),
    args = [.ref a, .long off, .int n] → Rd38At σ0 fr σ a off n vs sb pos ix wv tk cv t → cv = .null →
    rdWP args σ0 38 fr σ

def RdS38Seg : Prop := ∀ (args : List Value) (σ0 : State), memReadSpec.pre args σ0 → ∀ (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (n : I32) (vs : List Value) (sb : Addr) (pos ix wv tk : I32) (cv : Value) (t : JStr),
    args = [.ref a, .long off, .int n] → Rd38At σ0 fr σ a off n vs sb pos ix wv tk cv t → ∀ (x : Addr) (c : JStr),
    cv = .ref x → σ.heap x = some (.str c) → σ0.heap x = some (.str c) →
    c.length = slotLn (slotIdx (off.toInt + pos.toInt).toNat) →
    slotSt (slotIdx (off.toInt + pos.toInt).toNat) ≤ (off.toInt + pos.toInt).toNat → rdWP args σ0 38 fr σ

/-- From the loop head, by cases. -/
theorem rd_loop (hP : RdPastSeg) (hR : RdPreSeg) (args : List Value) (σ0 : State)
    (hpre : memReadSpec.pre args σ0) (fr : Frame) (σ : State) (hI : rdInv6 args σ0 fr σ) :
    rdWP args σ0 6 fr σ := by
  have hpre' := hpre
  obtain ⟨a, off, n, m, ha, hs, hoff, hnb, hinit⟩ := hpre'
  obtain ⟨vs, sb, pos, t, h⟩ := hI a off n ha
  have h' := h
  obtain ⟨-, -, -, -, -, -, -, -, hva, hvl, h1, h2, h3, h4, hg, -, -⟩ := h'
  rcases Int.lt_or_le pos.toInt n.toInt with hx | hx
  · have ho := rd_o_toInt off pos n h1 h2 hx h4
    by_cases hneg : off.toInt + pos.toInt < 0
    · exact rd_skip args σ0 hpre fr σ a off n vs sb pos t ha h hx ho hneg
    by_cases hpast : 171156 ≤ off.toInt + pos.toInt
    · exact hP args σ0 hpre fr σ a off n vs sb pos t ha h hx ho hpast
    have hin0 : 0 ≤ off.toInt + pos.toInt := by omega
    have hin1 : off.toInt + pos.toInt < 171156 := by omega
    have hJm : (off.toInt + pos.toInt).toNat < 171156 := by omega
    obtain ⟨hi, hw0, hw1⟩ := slotIdx_spec _ hJm
    have hon := rd_o_toNat off pos ho hin0
    have hwi0 := rd_within (off + JInt.toLong pos) (slotSt (slotIdx (off.toInt + pos.toInt).toNat))
      (off.toInt + pos.toInt).toNat (by rw [ho]; omega) hw0 hJm
    have hwi : (JLong.toInt (off + JInt.toLong pos -
        BitVec.ofNat 64 (slotSt (slotIdx (off.toInt + pos.toInt).toNat)))).toInt =
        off.toInt + pos.toInt - (slotSt (slotIdx (off.toInt + pos.toInt).toNat) : Int) := by
      rw [hwi0]; omega
    exact hR args σ0 hpre fr σ a off n vs sb pos t ha h hx ho hon hin0 hin1 hJm hi hw0 hw1 hwi
  · exact rd_exit args σ0 hpre fr σ a off n vs sb pos t ha h hx

/-- At the slot read, by the slot's value. -/
theorem rd_at38 (hN : RdN38Seg) (hS : RdS38Seg) (args : List Value) (σ0 : State)
    (hpre : memReadSpec.pre args σ0) (fr : Frame) (σ : State) (hI : rdInv38 args σ0 fr σ) :
    rdWP args σ0 38 fr σ := by
  have hpre' := hpre
  obtain ⟨a, off, n, m, ha, hs, hoff, hnb, hinit⟩ := hpre'
  obtain ⟨vs, sb, pos, ix, wv, tk, cv, t, h⟩ := hI a off n ha
  have h' := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hva, hvl, h1, h2, h3, h4, h5, h6, hcv', h7, h8, h9, h10, hg, -, -⟩ := h'
  obtain ⟨vs0, ha0, -, hall⟩ := hs
  have hvs : vs = vs0 := by
    have e := hg.2 a (State.lt_next_of_heap ha0)
    rw [hva, ha0] at e
    simpa using e
  subst hvs
  have hJm : (off.toInt + pos.toInt).toNat < 171156 := by omega
  obtain ⟨hi, hw0, -⟩ := slotIdx_spec _ hJm
  rcases hall _ hi with ⟨hn, -⟩ | ⟨x, c, hxv, hc0, hcl, -⟩
  · have hcv : cv = .null := (Option.some.inj (hcv'.symm.trans hn))
    exact hN args σ0 hpre fr σ a off n vs sb pos ix wv tk cv t ha h hcv
  · have hcv : cv = .ref x := (Option.some.inj (hcv'.symm.trans hxv))
    have hc : σ.heap x = some (.str c) := by rw [hg.2 x (State.lt_next_of_heap hc0), hc0]
    exact hS args σ0 hpre fr σ a off n vs sb pos ix wv tk cv t ha h x c hcv hc hc0 hcl hw0

set_option maxRecDepth 8000 in
set_option maxRecDepth 8000 in
/-- `memRead`'s verification conditions, given the open segments. -/
theorem memRead_vc_of (hP : RdPastSeg) (hR : RdPreSeg) (hN : RdN38Seg) (hS : RdS38Seg) :
    MethodVC Gen.prog rdCallees.env 0 memReadRef memReadSpec memReadInv 120 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · show bodyWP Gen.prog (callWP Gen.prog rdCallees.env 0) Gen.Cbstm03a.«memRead(java.lang.String[],long,int)»
      (memReadInv.inst args σ0) (memReadSpec.post args σ0) 120 0 (Frame.init true args) σ0
    have := rd_entry args σ0 hpre
    simp only [rdWP] at this
    exact this
  · intro p hp fr σ hI
    simp only [memReadInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · have := rd_loop hP hR args σ0 hpre fr σ hI
      simp only [rdWP] at this
      exact this
    · have := rd_at38 hN hS args σ0 hpre fr σ hI
      simp only [rdWP] at this
      exact this

end EquivLean.Modernize.Cbstm03a.Java.Mem

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mem.memRead_vc_of
