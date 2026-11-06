import EquivLean.Modernize.Cbact04c.Every.JavaRunRes196

/-!
# CBACT04C → Java, `run`: statements 199–209 (the interest, the total, the suffix, the id)

The machine arithmetic of the interest part is the model's (`amt_eq`, `tot_eq`, `k_eq`), and
`j210_of`: the cut point 210.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-- `trunc (bal * rate / 120000, 11)` on longs: the model's interest. -/
theorem amt_eq (tb r : Int) (h1 : -100000000000 < tb) (h2 : tb < 100000000000)
    (h3 : -1000000 < r) (h4 : r < 1000000) :
    ((BitVec.ofInt 64 tb * BitVec.ofInt 64 r).sdiv 120000#64).srem 100000000000#64 =
      BitVec.ofInt 64 (Int.tmod (Int.tdiv (tb * r) 120000) (10 ^ 11)) := by
  have hA : (tb * r).natAbs < 100000000000 * 1000000 := by
    rw [Int.natAbs_mul]
    exact Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega)
  have hm1 : -100000000000000000 < tb * r := by omega
  have hm2 : tb * r < 100000000000000000 := by omega
  rw [← BitVec.ofInt_mul]
  apply BitVec.eq_of_toInt_eq
  have hd : (120000#64 : BitVec 64) ≠ -1#64 := by decide
  rw [BitVec.toInt_srem, BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr hd),
    toInt_ofInt64 (by omega) (by omega)]
  have h12 : (120000#64 : BitVec 64).toInt = 120000 := by decide
  have h11 : (100000000000#64 : BitVec 64).toInt = 100000000000 := by decide
  rw [h12, h11]
  have q1 := Int.tmod_lt_of_pos (Int.tdiv (tb * r) 120000) (b := 100000000000) (by decide)
  have q2 := Int.lt_tmod_of_pos (Int.tdiv (tb * r) 120000) (b := 100000000000) (by decide)
  have hp : ((10 : Int) ^ 11) = 100000000000 := by decide
  rw [hp, toInt_ofInt64 (by omega) (by omega)]

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

theorem toInt_ofNat64 {k : Nat} (hk : k < 4611686018427387904) :
    (BitVec.ofNat 64 k).toInt = (k : Int) := toInt_ofNat_small hk

/-- `(k + 1) % 1000000` on longs. -/
theorem k_eq {k : Nat} (hk : k < 1000000) :
    (BitVec.ofNat 64 k + 1#64).srem 1000000#64 = BitVec.ofNat 64 ((k + 1) % 1000000) := by
  apply BitVec.eq_of_toInt_eq
  have h1 : (BitVec.ofNat 64 k + 1#64) = BitVec.ofNat 64 (k + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [h1, BitVec.toInt_srem, toInt_ofNat64 (k := k + 1) (by omega),
    toInt_ofNat64 (k := 1000000) (by omega), toInt_ofNat64 (k := (k + 1) % 1000000) (by omega),
    Int.tmod_eq_emod_of_nonneg (by omega)]
  omega

/-- The suffix as `fmtU` reads it. -/
theorem kstr_eq {k : Nat} (hk : k < 1000000) :
    (((BitVec.ofNat 64 k).toInt + 1).bmod 18446744073709551616).natAbs % 1000000 =
      (k + 1) % 1000000 := by
  rw [toInt_ofNat64 (by omega)]
  have : ((k : Int) + 1).bmod 18446744073709551616 = (k : Int) + 1 := by
    rw [Int.bmod_def]
    split <;> omega
  rw [this]
  omega

/-- **The interest computed, the transaction id built** (statements 199–209): the cut point 210. -/
theorem j210_of {g : G} {σ0 σ σ1 : State} {fr' : Frame} {i : I32} {hp : Hp}
    {tcbV acctV xrefV lastV : Value} {S : JStr}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt)
    (hstop : (g.stE i.toInt.toNat).stop = false) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some tcbV)
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f11 : fr'.get 11 = some (.long (BitVec.ofInt 64 (amtOf g i.toInt.toNat))))
    (f12 : fr'.get 12 = some (.long (BitVec.ofInt 64 (totOf g i.toInt.toNat))))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (kOf g i.toInt.toNat))))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some xrefV) (f27 : fr'.get 27 = some (.ref (σ1.next + 1)))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ tcbV
      (g.trec i.toInt.toNat)))
    (hheap : Hide (LoopHeap g σ0 σ hp (sel g i.toInt.toNat) acctV xrefV lastV))
    (hrate : rateOf g i.toInt.toNat ≠ 0)
    (hS : S = cp037Str g.parm ++ zpadJ (kOf g i.toInt.toNat) 6)
    (hg : Grows σ σ1) (hi : σ1.inits = σ.inits) :
    J210 g g.args σ0 fr' ((σ1.alloc (.str [1#16, 1#16])).snd.alloc (.str S)).snd := by
  subst hS
  have hg2 : Grows σ ((σ1.alloc (.str [1#16, 1#16])).snd.alloc
      (.str (cp037Str g.parm ++ zpadJ (kOf g i.toInt.toNat) 6))).snd :=
    grows_trans (grows_trans hg (grows_alloc _ _)) (grows_alloc _ _)
  have hi2 : ((σ1.alloc (.str [1#16, 1#16])).snd.alloc
      (.str (cp037Str g.parm ++ zpadJ (kOf g i.toInt.toNat) 6))).snd.inits = σ.inits := by
    rw [← hi]; rfl
  refine ⟨i, hp, tcbV, acctV, xrefV, lastV, .ref (σ1.next + 1), ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5,
    Hide.intro (jrecAt_grows hg2 (Hide.elim htcb)), hstop⟩, f3, f11, f12, f14, f25, f16, f17,
    Hide.intro (loopHeap_grows (Hide.elim hheap) hg2 hi2), hrate⟩, f27, Hide.intro ⟨_, rfl, ?_⟩⟩
  rw [State.heap_alloc, ite_eq_left (by simp [State.next_alloc])]

end EquivLean.Modernize.Cbact04c.Java
