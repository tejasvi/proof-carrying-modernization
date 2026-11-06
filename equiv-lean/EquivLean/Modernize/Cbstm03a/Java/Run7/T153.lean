import EquivLean.Modernize.Cbstm03a.Java.Run7.TLem

/-!
# CBSTM03A → Java `run`'s thin VC at cut point 153 (the account search of cross-reference record `j`)

`run_thin153`: from 153, another text → back at 153 with `i#78 + 1` (the texts left decrease); the text found →
`createStatement` (its frame `KeepsRes` keeps `xrefSt`) → the cards loop's head 168 (`crCnt < 10000`, so
`(crCnt + 1 − 1) · K + 1 < C4`); the texts exhausted → `abend`, `return` (no cut point).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

attribute [-simp] List.reduceReplicate
attribute [-jsimp] List.take_succ

namespace EquivLean.Modernize.Cbstm03a.Java.Seg7

/-- The variant at 168 after `createStatement` (its `KeepsRes` frame) is below the one at 153. -/
theorem c153_var168 {σa σ' : State} {res ld ls lh st2 : Addr} {j : Nat} {cr : I64} {nA : Int} {i : I32}
    (hk : KeepsRes res ld ls lh σa σ')
    (hst : σa.heap st2 = some (.array (.prim .int) [.int (BitVec.ofNat 32 (j + 1)), .int 0]))
    (n1 : st2 ≠ res) (n2 : st2 ≠ ld) (n3 : st2 ≠ ls) (n4 : st2 ≠ lh)
    (hj1 : j + 1 < 2147483648) (hcr0 : 0 ≤ cr.toInt) (hcr1 : cr.toInt < 10000) :
    (2147483648 -
          match σ'.heap st2 with
          | some (Obj.array _ (Value.int v :: _)) => BitVec.toInt v
          | _ => 0).toNat * 4394997302 + (BitVec.toInt cr).toNat * 10002 + 1 <
      (2147483648 - ((j : Int) + 1)).toNat * 4394997302 + 100030004 + (nA - BitVec.toInt i).toNat := by
  rw [hk.2 st2 (State.lt_next_of_heap hst) n1 n2 n3 n4, hst]
  simp only [bv32_toInt_ofNat_of_lt hj1, Nat.cast_add, Nat.cast_one]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
theorem run_thin153_aux (g : RunG) : RunThinCut g 153 inv153 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨-, -, ⟨et2, xs2, -, hl2, hF2⟩, -, ⟨et4, xs4, -, hl4, hF4⟩, ⟨hci0, -⟩, -⟩ := hpre
  have hx2 : g.xrs.length < 2147483648 := by rw [← forall2_length hF2]; exact hl2
  have ha4 : g.ars.length < 2147483648 := by rw [← forall2_length hF4]; exact hl4
  clear hF2 hF4 hl2 hl4
  obtain ⟨res, ld, ls, lh, L, o, j, i, crec, hX, hjl, -, hXr, hcr, -, h38, h26, hi0, hi1, -⟩ := hI
  have hj1 : j + 1 < 2147483648 := by simp only [RunG.T2, List.length_map] at hjl; omega
  clear hjl hx2
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, hbase, htexts, -, h2, hst2, -, -, -, -, -, h18, hLB⟩ := hX
  obtain ⟨-, -, -, -, h7, hR, -, -, -, -, -, hinits, -⟩ := hbase
  have hci : σ.initOf "Cbstm03a" = .done := by unfold State.initOf at hci0 ⊢; rw [hinits]; exact hci0
  clear hinits hci0
  obtain ⟨-, -, -, -, h15, -, ⟨n4, h28, hn4e⟩, -, -, -, -, ⟨xt4, hT4, hF4t⟩, -, -, -, -, -⟩ := htexts
  obtain ⟨-, -, ⟨x33, h33, hx33⟩⟩ := hXr
  obtain ⟨x37, h37, hx37⟩ := hcr
  obtain ⟨hcr0, hcr1, -, -, -⟩ := hLB
  generalize sub (fixStr (g.T2.getD j []) 1000) 25 36 = s33 at hx33
  simp only [List.replicate_zero, List.append_nil] at hT4
  have hl4t : xt4.length = g.ars.length := by
    rw [forall2_length hF4t]; simp [RunG.T4]
  -- `xrefSt` is none of the `Result` object and its lists
  have hR' := hR
  obtain ⟨fs, hresh, -, -, -, -, -, -, -, ⟨xd, md, hldh, -⟩, ⟨xs, ms, hlsh, -⟩, ⟨xh, mh, hlhh, -⟩⟩ := hR'
  have n1 : st2 ≠ res := fun e => by rw [e, hresh] at hst2; cases hst2
  have n2 : st2 ≠ ld := fun e => by rw [e, hldh] at hst2; cases hst2
  have n3 : st2 ≠ ls := fun e => by rw [e, hlsh] at hst2; cases hst2
  have n4' : st2 ≠ lh := fun e => by rw [e, hlhh] at hst2; cases hst2
  clear hresh hldh hlsh hlhh fs xd md xs ms xh mh
  have hv : runVar 153 args σ0 fr σ =
      ((vN : Int) - ((j + 1 : Nat) : Int)).toNat * vM + vC4 + (n4.toInt - i.toInt).toNat := by
    simp only [runVar, arr0, locI, h2, hst2, h28, h26, bv32_toInt_ofNat_of_lt hj1]
  rw [hv]
  unfold runThinWP
  rcases Int.lt_or_le i.toInt n4.toInt with hin | hout
  · obtain ⟨x, s, hx, hs⟩ := texts_elem hF4t i.toInt.toNat (by omega)
    have hit : i.toInt < (xt4.length : Int) := by omega
    clear hF4t
    have hRa : ResAtL (σ.alloc (Obj.str (List.take 11 s))).2 res ld ls lh o.disp o.stmt o.html o.ab :=
      resAtL_of_agree hR (fun y o' hy _ => by rw [State.heap_alloc_of_lt (State.lt_next_of_heap hy), hy])
    have hsta : (σ.alloc (Obj.str (List.take 11 s))).2.heap st2 =
        some (.array (.prim .int) [.int (BitVec.ofNat 32 (j + 1)), .int 0]) := by
      rw [State.heap_alloc_of_lt (State.lt_next_of_heap hst2), hst2]
    have hH := hid_intro (And.intro hRa hsta)
    clear hRa hsta
    jvc [runCallees, runInv, runVar, locI, locL, arr0, vN, vM, vC3, vC4, vK]
    obtain ⟨hRa, hsta⟩ := hid_elim hH
    obtain ⟨hA0, hA1⟩ := (‹∀ (r a b c : Addr) (d e f : List JStr), _ ∧ _› :
      ∀ (r a b c : Addr) (d e f : List JStr), _ ∧ _) res ld ls lh o.disp o.stmt o.html
    cases hab : o.ab
    · rw [hab] at hRa
      exact c153_var168 (hA0 rfl hRa).2.2.1 hsta n1 n2 n3 n4' hj1 hcr0 hcr1
    · rw [hab] at hRa
      exact c153_var168 (hA1 rfl hRa).2.2.1 hsta n1 n2 n3 n4' hj1 hcr0 hcr1
  · clear hF4t
    jvc [runCallees, runInv, runVar, locI, locL, arr0, vN, vM, vC3, vC4, vK]

end EquivLean.Modernize.Cbstm03a.Java.Seg7

namespace EquivLean.Modernize.Cbstm03a.Java

theorem run_thin153 (g : RunG) : RunThinCut g 153 inv153 := Seg7.run_thin153_aux g

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_thin153
