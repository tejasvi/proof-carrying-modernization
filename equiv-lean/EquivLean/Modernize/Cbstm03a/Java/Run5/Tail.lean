import EquivLean.Modernize.Cbstm03a.Java.Run5.Lem
import EquivLean.Modernize.Cbstm03a.Java.Run5.Cut

/-!
# CBSTM03A → Java, `run`'s segment 168: the statement's tail as virtual cut points

The tail (statements 196 … 213: three `stmt` and eight `html` calls) is cut right after each call of the
`Result` object's methods (`tailCuts`): the assertion `TailJ k` holds the cross-reference loop's state with the
`Result` holding the first `k` lines of `tailOf` (`tailK`). Each segment then makes exactly one such call, as its
last statement, so its precondition and postcondition are instantiated once, by hand.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg5

theorem memRd_length (m : Nat → JChar) (o : Int) (n : Nat) : (memRd m o n).length = n := by
  simp [memRd]

/-- The statement's three tail lines (`tailOf` before its HTML lines). -/
def tail3 (o : JOut) (total : I64) : JOut :=
  ((o.stmt1 (List.replicate 80 chDash)).stmt1
    (jl "Total EXP:" ++ List.replicate 56 space ++ jl "$" ++ fmtZStr total.toInt)).stmt1
    (List.replicate 32 chStar ++ jl "END OF STATEMENT" ++ List.replicate 32 chStar)

/-- The HTML lines of the statement's tail. -/
abbrev tailH : List JStr := [LTRS, L10, L75, LTDE, LTRE, L78, L79, L80]

/-- The outputs after the first `k` lines of the statement's tail. -/
def tailK (o : JOut) (total : I64) : Nat → JOut
  | 0 => o
  | 1 => o.stmt1 (List.replicate 80 chDash)
  | 2 => (o.stmt1 (List.replicate 80 chDash)).stmt1
      (jl "Total EXP:" ++ List.replicate 56 space ++ jl "$" ++ fmtZStr total.toInt)
  | k + 3 => (tailH.take k).foldl JOut.html1 (tail3 o total)

theorem tailK_11 (o : JOut) (total : I64) : tailK o total 11 = tailOf o total := rfl

/-- At the cut after the `k`-th line of the tail: the cross-reference loop's state with the `Result` holding
`tailK oc total k` (record `j` done once the tail is written); `res` in its local, `Cbstm03a` initialized; the
total in `i#79` (`k = 0`) or its text in `tRest` (`k = 1`). -/
def TailJ (g : RunG) (σ0 : State) (k : Nat) (fr : Frame) (σ : State) : Prop :=
  ∃ (res ld ls lh : Addr) (L : LdSt) (oc : JOut) (j : Nat) (total : I64),
    Kept (XCtx g σ0 fr σ res ld ls lh (tailK oc total k) L (j + 1) ∧ j < g.T2.length ∧
      xrefAll g.K3 g.T3 g.T4 L (tailOf oc total) (g.T2.drop (j + 1)) = g.F) ∧
    fr.get 7 = some (.ref res) ∧ σ.initOf "Cbstm03a" = .done ∧ TotOk total ∧
    (k = 0 → fr.get 21 = some (.long total)) ∧ (k = 1 → StrLoc σ fr 32 (fmtZStr total.toInt))

/-- The virtual cut points of the tail. -/
def tailCuts (g : RunG) (σ0 : State) : Cuts :=
  [(196, TailJ g σ0 0), (199, TailJ g σ0 1), (202, TailJ g σ0 2), (206, TailJ g σ0 3), (207, TailJ g σ0 4),
   (208, TailJ g σ0 5), (209, TailJ g σ0 6), (210, TailJ g σ0 7), (211, TailJ g σ0 8), (212, TailJ g σ0 9),
   (213, TailJ g σ0 10)]

/-- The cut list of a segment: the tail's cut points from the `k`-th on, then `run`'s. -/
abbrev CL (g : RunG) (args : List Value) (σ0 : State) (k : Nat) : Cuts :=
  (tailCuts g σ0).drop k ++ (runInv g).inst args σ0

/-- The locals the paths from 168 write: `$b12`, `$z5`, `crJmp`, `cnt`, `trJmp`, `i#78`, `tRest`, `cn`. -/
def FrT (fr fr' : Frame) : Prop :=
  ∀ k, k ≠ 0 → k ≠ 4 → k ≠ 17 → k ≠ 19 → k ≠ 22 → k ≠ 26 → k ≠ 32 → k ≠ 33 → fr'.get k = fr.get k

theorem FrT.get {fr fr' : Frame} (h : FrT fr fr') (k : Nat) (h0 : k ≠ 0 := by decide) (h4 : k ≠ 4 := by decide)
    (h17 : k ≠ 17 := by decide) (h19 : k ≠ 19 := by decide) (h22 : k ≠ 22 := by decide)
    (h26 : k ≠ 26 := by decide) (h32 : k ≠ 32 := by decide) (h33 : k ≠ 33 := by decide) :
    fr'.get k = fr.get k :=
  h k h0 h4 h17 h19 h22 h26 h32 h33

theorem FrT.trans {fr1 fr2 fr3 : Frame} (h1 : FrT fr1 fr2) (h2 : FrT fr2 fr3) : FrT fr1 fr3 :=
  fun k a b c d e f g h => (h2 k a b c d e f g h).trans (h1 k a b c d e f g h)

/-- `xctx_frame` for the locals of the paths from 168. -/
theorem xctx_frameT {g : RunG} {σ0 σ σ' : State} {fr fr' : Frame} {res ld ls lh : Addr} {o o' : JOut} {L : LdSt}
    {j' : Nat} (h : XCtx g σ0 fr σ res ld ls lh o L j') (hfr : FrT fr fr')
    (hk : KeepsRes res ld ls lh σ σ') (hR : ResAtL σ' res ld ls lh o'.disp o'.stmt o'.html o'.ab)
    (hi : σ'.inits = σ.inits) (hs : σ'.statics = σ.statics) :
    XCtx g σ0 fr' σ' res ld ls lh o' L j' := by
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, hB, hT, hL, h2, hst2, o1, o2, o3, h5, h3, h18, hLB⟩ := h
  obtain ⟨b10, b23, b9, b6, b7, hR0, r0, l0, s0, h0, hg, hi0, hs0⟩ := hB
  obtain ⟨c11, c12, c13, c14, c15, ⟨n3, c27, e3⟩, ⟨n4, c28, e4⟩, x1, x2, x3k, x3, x4, q1, q2, q3, q4, q5⟩ := hT
  obtain ⟨d16, d24, hS, htr, hl51⟩ := hL
  have hsa := saMono_of_keepsRes hR0 hk
  exact ⟨t1, t2, t3k, t3, t4, mem, trct, st2,
    ⟨(hfr.get 10).trans b10, (hfr.get 23).trans b23, (hfr.get 9).trans b9, (hfr.get 6).trans b6,
      (hfr.get 7).trans b7, hR, r0, l0, s0, h0, grows_keepsRes hg hk r0 l0 s0 h0, hi.trans hi0, hs.trans hs0⟩,
    ⟨(hfr.get 11).trans c11, (hfr.get 12).trans c12, (hfr.get 13).trans c13, (hfr.get 14).trans c14,
      (hfr.get 15).trans c15, ⟨n3, (hfr.get 27).trans c27, e3⟩, ⟨n4, (hfr.get 28).trans c28, e4⟩,
      textsAt_sa x1 hsa, textsAt_sa x2 hsa, textsAt_sa x3k hsa, textsAt_sa x3 hsa, textsAt_sa x4 hsa,
      q1, q2, q3, q4, q5⟩,
    ⟨(hfr.get 16).trans d16, (hfr.get 24).trans d24, slotsAt_sa hS hsa, heap_arr_sa hsa htr, hl51⟩,
    (hfr.get 2).trans h2, heap_arr_sa hsa hst2, o1, o2, o3, (hfr.get 5).trans h5, (hfr.get 3).trans h3,
    (hfr.get 18).trans h18, hLB⟩

end EquivLean.Modernize.Cbstm03a.Java.Seg5
