import EquivLean.Modernize.Cbstm03a.Java.Mw.M5
import EquivLean.Modernize.Cbstm03a.Java.Mw.M14
import EquivLean.Modernize.Cbstm03a.Java.Mw.M22
import EquivLean.Modernize.Cbstm03a.Java.Mw.M30
import EquivLean.Modernize.Cbstm03a.Java.Mw.M36
import EquivLean.Modernize.Cbstm03a.Java.Mw.Close

/-!
# CBSTM03A → Java: `memWrite`, a slot write from the loop head, through its virtual cut points

`0 ≤ o = off + pos < MEM_SZ`: the segments `5 → 14 → 22 → 26 → 30 → 36 → 5` (fuel 100 each), the slot's text
`c` from the loop head's memory (`slot_content_null`/`_ref`), the memory after the write (`memK_store`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Mw

theorem memK_slots {σ0 σ : State} {a : Addr} {off : I64} {t : JStr} {p : Nat} (hK : MemK σ0 σ a off t p) :
    ∀ m, SlotsAt σ0 a m → SlotsAt σ a (memWr m off.toInt (t.take p)) := by
  unfold MemK at hK
  exact hK.1

/-- A `null` slot holds spaces in the loop head's memory. -/
theorem slot_content_null {σ0 σ : State} {a : Addr} {off : I64} {t : JStr} {p : Nat} {vs : List Value} {i : Nat}
    (hK : MemK σ0 σ a off t p) (ha : σ.heap a = some (.array (.cls "java.lang.String") vs)) (hi : i < 561)
    (hvn : vs[i]? = some .null) :
    ∀ m, SlotsAt σ0 a m → ∀ w, w < slotLn i →
      memWr m off.toInt (t.take p) (slotSt i + w) = (List.replicate (slotLn i) space).getD w space := by
  intro m hm w hw
  obtain ⟨vs', ha', -, hs⟩ := memK_slots hK m hm
  rw [ha] at ha'
  cases ha'
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hw]
  rcases hs i hi with ⟨-, h2⟩ | ⟨y, c, h1, -, -, -⟩
  · exact h2 w hw
  · rw [hvn] at h1
    cases h1

/-- A string slot holds its string in the loop head's memory. -/
theorem slot_content_ref {σ0 σ : State} {a : Addr} {off : I64} {t : JStr} {p : Nat} {vs : List Value} {i : Nat}
    {y : Addr} {c : JStr} (hK : MemK σ0 σ a off t p) (ha : σ.heap a = some (.array (.cls "java.lang.String") vs))
    (hi : i < 561) (hvr : vs[i]? = some (.ref y)) (hyc : σ.heap y = some (.str c)) :
    ∀ m, SlotsAt σ0 a m → ∀ w, w < slotLn i → memWr m off.toInt (t.take p) (slotSt i + w) = c.getD w space := by
  intro m hm w hw
  obtain ⟨vs', ha', -, hs⟩ := memK_slots hK m hm
  rw [ha] at ha'
  cases ha'
  rcases hs i hi with ⟨h1, -⟩ | ⟨y', c', h1, h2, -, h4⟩
  · rw [hvr] at h1
    cases h1
  · rw [hvr] at h1
    cases h1
    rw [hyc] at h2
    cases h2
    exact h4 w hw

theorem add_toInt32 (a b : I32) (h1 : -2147483648 ≤ a.toInt + b.toInt) (h2 : a.toInt + b.toInt < 2147483648) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [BitVec.toInt_add]
  exact bmod32_self h1 h2

/-- From statement 30 (the slot's text `c` in `cur#7`) back to the loop head. -/
theorem mw_from30 (σ0 : State) (a : Addr) (off : I64) (x : Addr) (t : JStr) (pos n : I32) (vs : List Value)
    (i W K P : Nat) (c : JStr) (hpos : pos.toInt = P) (hi : i < 561) (hvl : vs.length = 561) (hL : slotLn i ≤ 334)
    (hcl : c.length = slotLn i) (hWK : W + K ≤ slotLn i) (hPK : P + K ≤ t.length) (htl : t.length < 2147483648)
    (hx0 : σ0.heap x = some (.str t)) (hn : n.toInt = t.length) (hoff : -2147483648 < off.toInt)
    (hlt : off.toInt < 171156)
    (hS : StepK σ0 a off t (c.take W ++ ((t.take (P + K)).drop P ++ c.drop (W + K))) i W K P)
    (fr : Frame) (σ : State) (hA : A30 σ0 a off x t pos n vs i W K P c fr σ) :
    mwWPc [.ref a, .long off, .ref x] σ0 [] 200 30 fr σ := by
  obtain ⟨h0, h1, h5, h10, h12, ⟨idx, within, take, h6, h8, h11, hidx, hw, htk⟩, ⟨y, h15, hyc⟩, ha, hxs, hinit,
    hK⟩ := hA
  have hpt : (pos + take).toInt = ((P + K : Nat) : Int) := by
    rw [add_toInt32 pos take (by omega) (by omega)]; omega
  have hwt : (within + take).toInt = ((W + K : Nat) : Int) := by
    rw [add_toInt32 within take (by omega) (by omega)]; omega
  refine mwWPc_cut _ σ0 36 (by decide) (A36 σ0 a off x t pos n vs i W K P c) 100 (fun fr' σ' hA' => ?_) 100 30 fr σ
    ?_
  · obtain ⟨h0', h1', h5', h10', h12', ⟨idx', take', h6', h11', hidx', htk'⟩, ⟨q, h13', hq'⟩, ha', hxs', hinit',
      hK'⟩ := hA'
    have hpt' : (pos + take').toInt = ((P + K : Nat) : Int) := by
      rw [add_toInt32 pos take' (by omega) (by omega)]; omega
    unfold mwWPc
    exact mw_m36_run σ0 _ fr' σ' a off x t _ pos n idx' take' vs i K P q h0' h1' h12' h10' h5' h6' h11' h13' hidx' hi
      hvl htk' hpos hpt' ha' hq' hxs' hx0 hn htl hoff hlt hinit' (memK_store hK' hS hi ha' hq')
  · unfold mwWPc
    exact mw_m30_run σ0 _ _ fr σ a off x t pos n idx within take vs i W K P y c h0 h1 h12 h10 h5 h6 h8 h11 h15 hidx
      hw htk hpos hWK hL hcl hPK htl hpt hwt ha hyc hxs hinit hK

/-- A slot write from the loop head. -/
theorem mw_slot (σ0 : State) (a : Addr) (off : I64) (x : Addr) (m0 : Nat → JChar) (hm0 : SlotsAt σ0 a m0)
    (fr : Frame) (σ : State) (t : JStr) (pos n : I32) (h : MwAt σ0 fr σ a off x t pos n)
    (hx : pos.toInt < n.toInt) (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt)
    (hin0 : 0 ≤ off.toInt + pos.toInt) (hin1 : off.toInt + pos.toInt < 171156) :
    mwWPc [.ref a, .long off, .ref x] σ0 [] 600 5 fr σ := by
  obtain ⟨h0, h1, h12, h10, h5, hxs, hx0, hn, htl, hoff, hp0, hpo, hinit, hK⟩ := h
  obtain ⟨P, hP⟩ : ∃ P : Nat, pos.toInt = P := ⟨pos.toInt.toNat, by omega⟩
  rw [show pos.toInt.toNat = P by omega] at hK
  obtain ⟨J, hJ⟩ : ∃ J : Nat, off.toInt + pos.toInt = J := ⟨(off.toInt + pos.toInt).toNat, by omega⟩
  have hJm : J < 171156 := by omega
  obtain ⟨hi, hw0, hw1⟩ := slotIdx_spec J hJm
  have hL := slotLn_le (slotIdx J)
  have hlt : off.toInt < 171156 := by omega
  obtain ⟨K, hK1, hK2, hK3⟩ : ∃ K : Nat, (K : Int) ≤ slotLn (slotIdx J) - (J - slotSt (slotIdx J) : Nat) ∧
      (K : Int) ≤ n.toInt - pos.toInt ∧
      ((K : Int) = slotLn (slotIdx J) - (J - slotSt (slotIdx J) : Nat) ∨ (K : Int) = n.toInt - pos.toInt) :=
    ⟨min (slotLn (slotIdx J) - (J - slotSt (slotIdx J))) (n.toInt - pos.toInt).toNat, by omega, by omega, by omega⟩
  have hWK : (J - slotSt (slotIdx J)) + K ≤ slotLn (slotIdx J) := by omega
  have hPK : P + K ≤ t.length := by omega
  have hW : off.toInt + P = slotSt (slotIdx J) + (J - slotSt (slotIdx J) : Nat) := by omega
  obtain ⟨vs, ha, hvl, hslots⟩ := memK_slots hK m0 hm0
  refine mwWPc_cut _ σ0 14 (by decide) (A14 σ a off x pos n J) 500 (fun fr1 σ1 hA1 => ?_) 100 5 fr σ ?_
  · obtain ⟨hσ1, h0', h1', h5', h10', h12', o, h2', ho'⟩ := hA1
    rw [hσ1]
    have hon : o.toNat = J := by have := toInt_eq_toNat_of_nonneg o (by omega); omega
    refine mwWPc_cut _ σ0 22 (by decide) (A22 σ a off x pos n (slotIdx J) (J - slotSt (slotIdx J))) 400
      (fun fr2 σ2 hA2 => ?_) 100 14 fr1 σ ?_
    · obtain ⟨hσ2, h0'', h1'', h5'', h10'', h12'', idx, len, within, h6, h7, h8, hidx, hl, hwv⟩ := hA2
      rw [hσ2]
      have hw := valI_elim hwv
      refine mwWPc_cut _ σ0 26 (by decide) (A26 σ a off x pos n (slotIdx J) (J - slotSt (slotIdx J)) K) 300
        (fun fr3 σ3 hA3 => ?_) 100 22 fr2 σ ?_
      · obtain ⟨hσ3, g0, g1, g5, g10, g12, idx3, len3, within3, take3, g6, g7, g8, g11, hidx3, hl3, hw3, htkv⟩ := hA3
        rw [hσ3]
        have htk := valI_elim htkv
        rcases hslots (slotIdx J) hi with ⟨hvn, -⟩ | ⟨y, c, hvr, hyc, hcl, -⟩
        · refine mwWPc_cut _ σ0 30 (by decide)
            (A30 σ0 a off x t pos n vs (slotIdx J) (J - slotSt (slotIdx J)) K P
              (List.replicate (slotLn (slotIdx J)) space)) 200
            (fun fr4 σ4 hA4 => mw_from30 σ0 a off x t pos n vs (slotIdx J) (J - slotSt (slotIdx J)) K P _ hP hi hvl
              hL (List.length_replicate ..) hWK hPK htl hx0 hn hoff hlt
              (stepK_intro _ hW hWK hPK (List.length_replicate ..) (slot_content_null hK ha hi hvn)) fr4 σ4 hA4)
            100 26 fr3 σ ?_
          unfold mwWPc
          exact mw_m26n_run σ0 _ _ fr3 σ a off x t pos n idx3 len3 within3 take3 vs (slotIdx J)
            (J - slotSt (slotIdx J)) K P g0 g1 g12 g10 g5 g6 g7 g8 g11 hidx3 hl3 hw3 htk hL hi ha hvl hvn hxs hinit hK
        · refine mwWPc_cut _ σ0 30 (by decide)
            (A30 σ0 a off x t pos n vs (slotIdx J) (J - slotSt (slotIdx J)) K P c) 200
            (fun fr4 σ4 hA4 => mw_from30 σ0 a off x t pos n vs (slotIdx J) (J - slotSt (slotIdx J)) K P c hP hi hvl
              hL hcl hWK hPK htl hx0 hn hoff hlt
              (stepK_intro c hW hWK hPK hcl (slot_content_ref hK ha hi hvr hyc)) fr4 σ4 hA4)
            100 26 fr3 σ ?_
          unfold mwWPc
          exact mw_m26r_run σ0 _ _ fr3 σ a off x t pos n idx3 len3 within3 take3 vs (slotIdx J)
            (J - slotSt (slotIdx J)) K P y c g0 g1 g12 g10 g5 g6 g7 g8 g11 hidx3 hl3 hw3 htk hL hi ha hvl hvr hyc hxs
            hinit hK
      · unfold mwWPc
        exact mw_m22_run _ σ0 _ fr2 σ a off x pos n idx len within (slotIdx J) (J - slotSt (slotIdx J)) K h0'' h1''
          h12'' h10'' h5'' h6 h7 h8 hidx hl hw hL (by omega) hx hp0 (by omega) hK1 hK2 hK3
    · unfold mwWPc
      exact mw_m14_run _ σ0 _ fr1 σ a off x pos n o J (slotIdx J) h0' h1' h12' h10' h5' h2' hinit ho' hon hJm rfl hi
        hL hw0
  · unfold mwWPc
    exact mw_m5_run _ σ0 _ fr σ a off x pos n J h0 h1 h12 h10 h5 hx ho hJ

end EquivLean.Modernize.Cbstm03a.Java.Mw
