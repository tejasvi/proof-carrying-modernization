import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVtH2
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunAR

/-!
# CBTRN02C → Java: `validateTran`, the checks

`limit_iff`: Java's `limit cmp (credit - debit + amount) % 10^11` is the model's over-limit test
(`WS-TEMP-BAL` truncates to 11 digits); `aExp_length`: the expiration date has 10 bytes.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem aExp_length {a : List EquivLean.Cobol.Rec.FVal} (hv : AccountRecord.Valid a) :
    (Model.aExp a).length = 10 := by
  have hl : a.length = 13 := (forall2_length hv).symm
  match a, hl, hv with
  | [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12], _,
    .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons h6 _)))))) =>
    cases v6 with
    | num n =>
      obtain ⟨fmt, hk, -⟩ := h6
      cases hk
    | str bs => exact h6.2

theorem sub_ofInt64 (x y : Int) (hx : x.natAbs < 1000000000000000000)
    (hy : y.natAbs < 1000000000000000000) :
    BitVec.ofInt 64 x - BitVec.ofInt 64 y = BitVec.ofInt 64 (x - y) := by
  apply BitVec.eq_of_toInt_eq
  have hbx := natAbs_bounds hx
  have hby := natAbs_bounds hy
  rw [BitVec.toInt_sub, toInt_ofInt64 (by omega), toInt_ofInt64 (by omega),
    toInt_ofInt64 (by omega), Int.bmod_def]
  split <;> omega

/-- Java's `(a + b) % m` on `long`s, `a` below `4·10^18`. -/
theorem srem_add_ofInt' (x y : Int) (m : Nat) (hm0 : 0 < m) (hm : m < 9223372036854775808)
    (hx : x.natAbs < 4000000000000000000) (hy : y.natAbs < 1000000000000000000) :
    (BitVec.ofInt 64 x + BitVec.ofInt 64 y).srem (BitVec.ofNat 64 m) =
      BitVec.ofInt 64 ((x + y).tmod m) := by
  apply BitVec.eq_of_toInt_eq
  have hbx := natAbs_bounds hx
  have hby := natAbs_bounds hy
  have hadd : (BitVec.ofInt 64 x + BitVec.ofInt 64 y).toInt = x + y := by
    rw [BitVec.toInt_add, toInt_ofInt64 (by omega), toInt_ofInt64 (by omega), Int.bmod_def]
    split <;> omega
  have hmi : (BitVec.ofNat 64 m).toInt = m := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    split <;> omega
  rw [BitVec.toInt_srem, hadd, hmi]
  have hb : ((x + y).tmod m).natAbs < 9223372036854775808 := by
    rw [Int.natAbs_tmod]
    exact Nat.lt_trans (Nat.mod_lt _ hm0) hm
  rw [toInt_ofInt64 hb]

/-- The model's temporary balance: the sum truncated to 11 digits. -/
theorem tempBal_eq (v : Int) :
    (Cobol.Sem.fitNum {} CardDemo.Cbtrn02c.WS_TEMP_BAL.fmt v).2 = v.tmod 100000000000 := by
  rw [fitNum_signed_display (by rfl) (by rfl)]
  rfl

/-- Java's temporary balance: `(credit - debit + amount) % 10^11`. -/
theorem tempBal_java (cc cd amt : Int) (h1 : cc.natAbs < 1000000000000000000)
    (h2 : cd.natAbs < 1000000000000000000) (h3 : amt.natAbs < 1000000000000000000) :
    (BitVec.ofInt 64 cc - BitVec.ofInt 64 cd + BitVec.ofInt 64 amt).srem 100000000000#64 =
      BitVec.ofInt 64 ((cc - cd + amt).tmod 100000000000) := by
  rw [sub_ofInt64 cc cd h1 h2]
  exact srem_add_ofInt' (cc - cd) amt 100000000000 (by decide) (by decide) (by omega) h3

theorem take10_eq {α : Type} : ∀ (l : List α) (h : 10 ≤ l.length),
    [l[0], l[1], l[2], l[3], l[4], l[5], l[6], l[7], l[8], l[9]] = l.take 10
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _ => rfl
  | [], h => absurd h (by simp)
  | [_], h => absurd h (by simp)
  | [_, _], h => absurd h (by simp)
  | [_, _, _], h => absurd h (by simp)
  | [_, _, _, _], h => absurd h (by simp)
  | [_, _, _, _, _], h => absurd h (by simp)
  | [_, _, _, _, _, _], h => absurd h (by simp)
  | [_, _, _, _, _, _, _], h => absurd h (by simp)
  | [_, _, _, _, _, _, _, _], h => absurd h (by simp)
  | [_, _, _, _, _, _, _, _, _], h => absurd h (by simp)

theorem cp037Str_take (bs : List UInt8) (n : Nat) : (cp037Str bs).take n = cp037Str (bs.take n) := by
  unfold cp037Str
  rw [List.map_take]

theorem cmpJ_nonneg_iff (o : Ordering) : 0 ≤ (cmpJ o).toInt ↔ o ≠ .lt := by
  cases o <;> decide

/-- A string of the entry state, read after the updates of the work-storage records and an
allocation. -/
theorem argText_chain_old {σ0 : State} {wX wA a : Addr} {o1 o2 o3 : Obj} {s : JStr}
    (ha : σ0.heap a = some (.str s)) (h1 : a ≠ wX) (h2 : a ≠ wA) :
    argText (((σ0.setObj wX o1).setObj wA o2).alloc o3).snd (.ref a) = s := by
  apply argText_of
  have hlt : a < σ0.next := State.lt_next_of_heap ha
  rw [State.heap_alloc_of_lt (by simp only [State.next_setObj]; exact hlt), State.heap_setObj,
    if_neg h2, State.heap_setObj, if_neg h1, ha]

/-- The string allocated after the updates of the work-storage records. -/
theorem argText_chain_new {σ0 : State} {wX wA : Addr} {o1 o2 : Obj} {s : JStr} :
    argText (((σ0.setObj wX o1).setObj wA o2).alloc (.str s)).snd (.ref σ0.next) = s := by
  apply argText_of
  rw [State.heap_alloc, if_pos (by simp only [State.next_setObj])]

/-- **The limit test**: Java's comparison of the limit with `(credit - debit + amount) % 10^11` is
the model's comparison with `WS-TEMP-BAL`. -/
theorem limit_iff {cc cd amt lim : Int} (h1 : cc.natAbs < 1000000000000000000)
    (h2 : cd.natAbs < 1000000000000000000) (h3 : amt.natAbs < 1000000000000000000)
    (h4 : lim.natAbs < 1000000000000000000) :
    (BitVec.ofInt 64 lim).toInt < (((BitVec.ofInt 64 cc).toInt - (BitVec.ofInt 64 cd).toInt +
        (BitVec.ofInt 64 amt).toInt).bmod 18446744073709551616).tmod 100000000000 ↔
      lim < (Cobol.Sem.fitNum {} CardDemo.Cbtrn02c.WS_TEMP_BAL.fmt (cc - cd + amt)).2 := by
  have hb1 := natAbs_bounds h1
  have hb2 := natAbs_bounds h2
  have hb3 := natAbs_bounds h3
  have hb4 := natAbs_bounds h4
  rw [toInt_ofInt64 (by omega), toInt_ofInt64 (by omega), toInt_ofInt64 (by omega),
    toInt_ofInt64 (by omega), tempBal_eq]
  have e : (cc - cd + amt).bmod 18446744073709551616 = cc - cd + amt := by
    rw [Int.bmod_def]
    split <;> omega
  rw [e]

/-- **`validateTran`'s postcondition at its return.** -/
theorem vt_post_ret {d xA aD wX wA : Addr} {σ0 σ' : State}
    {fsX fsA fsX' fsA' : List (FieldKey × Value)} {cc cd lim amt : I64} {exs origS sub : JStr}
    {t : List EquivLean.Cobol.Rec.FVal} {B : I32}
    (hX : σ0.heap wX = some (.plain "Cbtrn02c$CardXrefRecord" fsX))
    (hA : σ0.heap wA = some (.plain "Cbtrn02c$AccountRecord" fsA))
    (hkA : AllSome xrKeys fsX' ∧ AllSome acKeys fsA' ∧ ∃ t1 vals2 accts x a, VtD σ0 d t1 ∧
      VtIn σ0 xA aD wX wA vals2 accts ∧
      Model.findXref vals2 (Model.tCard t1) = some x ∧ Model.findAcct accts (Model.xAcct x) = some a ∧
      JRecAt CardXrefRecord xrCls ((σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')).setObj wA
        (.plain "Cbtrn02c$AccountRecord" fsA')) (.ref wX) x ∧
      JRecAt AccountRecord acCls ((σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')).setObj wA
        (.plain "Cbtrn02c$AccountRecord" fsA')) (.ref wA) a ∧
      cc = BitVec.ofInt 64 (Model.aCC a) ∧ cd = BitVec.ofInt 64 (Model.aCD a) ∧
      lim = BitVec.ofInt 64 (Model.aLimit a) ∧ exs = cp037Str (Model.aExp a))
    (hO : cp037Str (Model.tOrig t) = origS ∧ BitVec.ofInt 64 (Model.tAmt t) = amt)
    (hD : VtD σ0 d t) (hsub : sub = cp037Str ((Model.tOrig t).take 10))
    (hn : σ0.next + 1 ≤ σ'.next) (hi : σ'.inits = σ0.inits) (hs : σ'.statics = σ0.statics)
    (hc : σ'.initOf "Cbtrn02c" = InitSt.done) (hc0 : σ0.initOf "Cbtrn02c" = InitSt.done)
    (hheap : ∀ x, x < σ0.next + 1 → σ'.heap x =
      if x = σ0.next then some (.str sub)
      else if x = wA then some (.plain "Cbtrn02c$AccountRecord" fsA')
      else if x = wX then some (.plain "Cbtrn02c$CardXrefRecord" fsX') else σ0.heap x)
    (hB : B = BitVec.ofInt 32 (if Cobol.Sem.cmpBytes (decJ exs) (decJ sub) = .lt then 103
      else if lim.toInt < ((cc.toInt - cd.toInt + amt.toInt).bmod 18446744073709551616).tmod
        100000000000 then 102 else 0)) :
    vtPostC [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0 (.normal (some (.int B)) σ') := by
  unfold vtPostC
  intro d0 xA0 aD0 wX0 wA0 he
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
  obtain ⟨hallX, hallA, t1, vals2, accts, x, a, hD1, hIn1, hfx, hfa, hjx, hja, rfl, rfl, rfl, rfl⟩ :=
    hkA
  obtain ⟨-, rfl⟩ := hO
  have hwX : wX < σ0.next := State.lt_next_of_heap hX
  have hwA : wA < σ0.next := State.lt_next_of_heap hA
  have hwXA : wA ≠ wX := by
    intro h
    rw [h, hX] at hA
    simp at hA
  have hg : Grows ((σ0.setObj wX (.plain "Cbtrn02c$CardXrefRecord" fsX')).setObj wA
      (.plain "Cbtrn02c$AccountRecord" fsA')) σ' := by
    refine ⟨by simp only [State.next_setObj]; jomega, fun z hz => ?_⟩
    simp only [State.next_setObj] at hz
    rw [hheap z (by jomega), if_neg (Nat.ne_of_lt hz),
      State.heap_setObj_of_lt (by rw [State.next_setObj]; exact hwA), State.heap_setObj_of_lt hwX]
  have hσX : σ'.heap wX = some (.plain "Cbtrn02c$CardXrefRecord" fsX') := by
    rw [hheap wX (by jomega), if_neg (Nat.ne_of_lt hwX), if_neg (Ne.symm hwXA), if_pos rfl]
  have hσA : σ'.heap wA = some (.plain "Cbtrn02c$AccountRecord" fsA') := by
    rw [hheap wA (by jomega), if_neg (Nat.ne_of_lt hwA), if_pos rfl]
  refine ⟨⟨by jomega, fun z hz hm => ?_⟩, hi, hs, by rw [hc, hc0], ⟨fsX', hσX, hallX⟩,
    ⟨fsA', hσA, hallA⟩, B, rfl, fun t' vals2' accts' hD' hIn' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
    rw [hheap z (by jomega), if_neg (Nat.ne_of_lt hz), if_neg hm.2, if_neg hm.1]
  obtain ⟨e1, e2, e3⟩ := vtd_det hD1 hD'
  obtain ⟨rfl, rfl⟩ := vtin_det hIn1 hIn'
  obtain ⟨f1, f2, f3⟩ := vtd_det hD hD1
  have hamt : (Model.tAmt t).natAbs < 100000000000 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := hD
    exact h
  have hIn0 := hIn1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hvA, -⟩ := hIn0
  have hva := hvA a (List.mem_of_find?_eq_some hfa)
  obtain ⟨-, n0, b1, n2, n3, n4, b5, b6, b7, n8, n9, b10, b11, b12, hae, -, -, a3, -, a8, a9⟩ :=
    acctobj_of_rec hja hva
  have hb3 : (Model.aLimit a).natAbs < 1000000000000000000 := by subst hae; exact a3
  have hb8 : (Model.aCC a).natAbs < 1000000000000000000 := by subst hae; exact a8
  have hb9 : (Model.aCD a).natAbs < 1000000000000000000 := by subst hae; exact a9
  have hvr : vreason vals2 accts t1 = if Cobol.Sem.cmpBytes (Model.aExp a)
      ((Model.tOrig t1).take 10) = .lt then 103 else if Model.aLimit a <
      (Cobol.Sem.fitNum {} CardDemo.Cbtrn02c.WS_TEMP_BAL.fmt
        (Model.aCC a - Model.aCD a + Model.tAmt t1)).2 then 102 else 0 := by
    simp only [vreason, hfx, hfa]
  rw [hsub, decJ_cp037, decJ_cp037, f3] at hB
  have hamt1 : (Model.tAmt t1).natAbs < 1000000000000000000 := by rw [← f2]; omega
  rw [f2] at hB
  have hL := limit_iff hb8 hb9 hamt1 hb3
  refine ⟨?_, fun _ => ⟨x, a, ?_, hfa, jrecAt_grows hjx hg, jrecAt_grows hja hg⟩⟩
  · rw [← vreason_congr e1 e2 e3, hvr, hB]
    by_cases h1 : Cobol.Sem.cmpBytes (Model.aExp a) (List.take 10 (Model.tOrig t1)) = .lt
    · rw [if_pos h1, if_pos h1]
    · by_cases h2 : Model.aLimit a < (Cobol.Sem.fitNum {} CardDemo.Cbtrn02c.WS_TEMP_BAL.fmt
          (Model.aCC a - Model.aCD a + Model.tAmt t1)).2
      · rw [if_neg h1, if_neg h1, if_pos h2, if_pos (hL.2 h2)]
      · rw [if_neg h1, if_neg h1, if_neg h2, if_neg (fun h => h2 (hL.1 h))]
  · rw [← e1]
    exact hfx

theorem cmpJ_neg_iff (o : Ordering) : ¬0 ≤ (cmpJ o).toInt ↔ o = .lt := by
  cases o <;> decide

/-- The first 10 characters of the origination timestamp, as `substring(0, 10)` leaves them. -/
theorem vt_sub {t : List EquivLean.Cobol.Rec.FVal} {origS : JStr} {amt : I64}
    (hO : Hide (cp037Str (Model.tOrig t) = origS ∧ BitVec.ofInt 64 (Model.tAmt t) = amt))
    (h : origS.length = 26) :
    [origS[0], origS[1], origS[2], origS[3], origS[4], origS[5], origS[6], origS[7], origS[8],
      origS[9]] = cp037Str ((Model.tOrig t).take 10) := by
  obtain ⟨hO, -⟩ := Hide.elim hO
  subst hO
  rw [take10_eq _ (by omega), cp037Str_take]

end EquivLean.Modernize.Cbtrn02c.Java
