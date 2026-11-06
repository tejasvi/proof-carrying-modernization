import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM4s
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunTac

/-!
# CBTRN02C → Java: `updateTcatbal` satisfies its contract

Cut point 21 (after the first search): the missing key displayed (`z0 = 1`), or the record found
copied into `tcatWs` (`z0 = 0`).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- Statement 21. -/
def ut21 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (r d wX wC lC : Addr), args = [.ref r, .ref d, .ref wX, .ref wC, .ref lC] → UtPre σ0 r d wX wC lC →
    fr.get 5 = some (.ref r) ∧ fr.get 2 = some (.ref d) ∧ fr.get 8 = some (.ref wX) ∧
    fr.get 0 = some (.ref wC) ∧ fr.get 6 = some (.ref lC) ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c" ∧
    (utIdx σ0 d wX lC < 0 → fr.get 14 = some (.int 1#32) ∧
      ∃ (sD : Addr) (m1 : Nat),
        σ.heap (refField σ0 r dispKey) =
          some (.list .arrayList (listOf σ0 (refField σ0 r dispKey) ++ [.ref sD]) m1) ∧
        σ.heap sD = some (.str (noCatJ (lng σ0 wX xAcctKey) (argText σ0 (fld σ0 d dTypeKey))
          (lng σ0 d dCatKey))) ∧
        σ0.next ≤ sD ∧ FrameS σ0 σ [refField σ0 r dispKey]) ∧
    (0 ≤ utIdx σ0 d wX lC → fr.get 14 = some (.int 0#32) ∧
      fr.get 9 = some (.int (BitVec.ofInt 32 (utIdx σ0 d wX lC))) ∧
      ∃ fsA, (∀ k ∈ tcKeys, Fields.get fsA k =
          Fields.get (fieldsOf σ0 (objOf ((listOf σ0 lC).getD (utIdx σ0 d wX lC).toNat .null))) k) ∧
        σ = σ0.setObj wC (.plain "Cbtrn02c$TranCatBalRecord" fsA))

/-- Statement 41 (missing key, before the second search): `tcatWs` holds the key with the amount
as balance (`FILLER` unchanged); only the display list and `tcatWs` changed. -/
def ut41 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (r d wX wC lC : Addr), args = [.ref r, .ref d, .ref wX, .ref wC, .ref lC] → UtPre σ0 r d wX wC lC →
    utIdx σ0 d wX lC < 0 ∧
    fr.get 5 = some (.ref r) ∧ fr.get 2 = some (.ref d) ∧ fr.get 8 = some (.ref wX) ∧
    fr.get 0 = some (.ref wC) ∧ fr.get 6 = some (.ref lC) ∧
    fr.get 3 = some (.long (lng σ0 wX xAcctKey)) ∧ fr.get 11 = some (fld σ0 d dTypeKey) ∧
    fr.get 4 = some (.long (lng σ0 d dCatKey)) ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c" ∧
    (∃ (sD : Addr) (m1 : Nat),
        σ.heap (refField σ0 r dispKey) =
          some (.list .arrayList (listOf σ0 (refField σ0 r dispKey) ++ [.ref sD]) m1) ∧
        σ.heap sD = some (.str (noCatJ (lng σ0 wX xAcctKey) (argText σ0 (fld σ0 d dTypeKey))
          (lng σ0 d dCatKey))) ∧ σ0.next ≤ sD) ∧
    (∃ fsC', σ.heap wC = some (.plain "Cbtrn02c$TranCatBalRecord" fsC') ∧
      Fields.get fsC' tcAcctKey = some (.long (lng σ0 wX xAcctKey)) ∧
      Fields.get fsC' tcTypeKey = some (fld σ0 d dTypeKey) ∧
      Fields.get fsC' tcCdKey = some (.long (lng σ0 d dCatKey)) ∧
      Fields.get fsC' tcBalKey = some (.long ((lng σ0 d dAmtKey).srem 100000000000#64)) ∧
      Fields.get fsC' tcFillKey = Fields.get (fieldsOf σ0 wC) tcFillKey ∧ AllSome tcKeys fsC') ∧
    FrameS σ0 σ [refField σ0 r dispKey, wC]

/-- The record found (index `utIdx`). -/
def utRec (σ0 : State) (d wX lC : Addr) : Addr :=
  objOf ((listOf σ0 lC).getD (utIdx σ0 d wX lC).toNat .null)

/-- Statement 59 (key found, before the second search): `tcatWs` holds the record found with the
amount added to its balance; only `tcatWs` changed. -/
def ut59 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (r d wX wC lC : Addr), args = [.ref r, .ref d, .ref wX, .ref wC, .ref lC] → UtPre σ0 r d wX wC lC →
    0 ≤ utIdx σ0 d wX lC ∧
    fr.get 5 = some (.ref r) ∧ fr.get 2 = some (.ref d) ∧ fr.get 8 = some (.ref wX) ∧
    fr.get 0 = some (.ref wC) ∧ fr.get 6 = some (.ref lC) ∧
    fr.get 3 = some (.long (lng σ0 (utRec σ0 d wX lC) tcAcctKey)) ∧
    fr.get 11 = some (fld σ0 (utRec σ0 d wX lC) tcTypeKey) ∧
    fr.get 4 = some (.long (lng σ0 (utRec σ0 d wX lC) tcCdKey)) ∧
    fr.get 9 = some (.int (BitVec.ofInt 32 (utIdx σ0 d wX lC))) ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c" ∧
    ∃ fsA, (∀ k ∈ tcKeys, Fields.get fsA k = Fields.get (fieldsOf σ0 (utRec σ0 d wX lC)) k) ∧
      σ.heap wC = some (.plain "Cbtrn02c$TranCatBalRecord" (Fields.set fsA tcBalKey
        (.long ((lng σ0 (utRec σ0 d wX lC) tcBalKey + lng σ0 d dAmtKey).srem 100000000000#64)))) ∧
      FrameS σ0 σ [wC]

def utInv : Invariants := [(21, ut21), (41, ut41), (59, ut59)]

/-- The key test of a category record survives updates of other objects. -/
theorem tcMatch_frame {σ σ' : State} {S : List Addr} {acct cd : I64} {tcs : JStr} {y ts : Addr}
    {fs : List (FieldKey × Value)} {tcs' : JStr} (hf : FrameS σ σ' S)
    (hy : σ.heap y = some (.plain "Cbtrn02c$TranCatBalRecord" fs))
    (ht : Fields.get fs tcTypeKey = some (.ref ts)) (hts : σ.heap ts = some (.str tcs'))
    (hyS : y ∉ S) (htsS : ts ∉ S) :
    tcMatch σ' acct tcs cd (.ref y) = tcMatch σ acct tcs cd (.ref y) := by
  have e1 := hf.heap hy hyS
  have e2 := hf.heap hts htsS
  simp only [tcMatch, longFieldOf, strFieldOf, e1, e2, hy, hts, ht]

theorem firstIdx_tcMatch_frame {σ σ' : State} {S : List Addr} {acct cd : I64} {tcs : JStr}
    {xs : List Value} (hf : FrameS σ σ' S) (hsh : TcatShapes σ xs)
    (hnot : ∀ v ∈ xs, ∀ y, v = .ref y → y ∉ S) (hstr : ∀ z ∈ S, ∀ t, σ.heap z ≠ some (.str t)) :
    firstIdx (tcMatch σ' acct tcs cd) xs = firstIdx (tcMatch σ acct tcs cd) xs := by
  apply firstIdx_congr'
  intro v hv
  obtain ⟨y, fs, a, ts, tcs', c, rfl, hy, -, ht, hts, -⟩ := hsh v hv
  refine tcMatch_frame hf hy ht hts (hnot _ hv y rfl) ?_
  intro hm
  exact hstr ts hm tcs' hts

theorem tcatShapes_frame {σ σ' : State} {S : List Addr} {xs : List Value} (hf : FrameS σ σ' S)
    (hsh : TcatShapes σ xs) (hnot : ∀ v ∈ xs, ∀ y, v = .ref y → y ∉ S)
    (hstr : ∀ z ∈ S, ∀ t, σ.heap z ≠ some (.str t)) : TcatShapes σ' xs := by
  intro v hv
  obtain ⟨y, fs, a, ts, tcs, c, rfl, hy, h1, h2, h3, h4⟩ := hsh v hv
  exact ⟨y, fs, a, ts, tcs, c, rfl, hf.heap hy (hnot _ hv y rfl), h1, h2,
    hf.heap h3 (fun hm => hstr ts hm tcs h3), h4⟩

theorem firstIdx_get {α : Type} {p : α → Bool} {l : List α} (h : 0 ≤ firstIdx p l) {x : α}
    (hx : l[(firstIdx p l).toNat]? = some x) : p x = true := by
  obtain ⟨j, hj⟩ : ∃ j, l.findIdx? p = some j := by
    unfold firstIdx at h
    cases hf : l.findIdx? p with
    | none => rw [hf] at h; simp at h
    | some j => exact ⟨j, rfl⟩
  have hfj : firstIdx p l = j := by unfold firstIdx; rw [hj]
  rw [hfj, Int.toNat_natCast] at hx
  obtain ⟨hjl, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hj
  rw [List.getElem?_eq_getElem hjl] at hx
  cases hx
  exact hp

theorem tcMatch_key {σ : State} {acct cd a c : I64} {tcs tcs' : JStr} {y ts : Addr}
    {fs : List (FieldKey × Value)} (hy : σ.heap y = some (.plain "Cbtrn02c$TranCatBalRecord" fs))
    (h1 : Fields.get fs tcAcctKey = some (.long a)) (h2 : Fields.get fs tcTypeKey = some (.ref ts))
    (hts : σ.heap ts = some (.str tcs')) (h3 : Fields.get fs tcCdKey = some (.long c))
    (hm : tcMatch σ acct tcs cd (.ref y) = true) : a = acct ∧ tcs' = tcs ∧ c = cd := by
  simp only [tcMatch, longFieldOf, strFieldOf, hy, h1, h2, hts, h3, Bool.and_eq_true, beq_iff_eq,
    Option.some.injEq] at hm
  exact ⟨hm.1.1, hm.1.2, hm.2⟩

abbrev utBody := Gen.Cbtrn02c.«updateTcatbal(Cbtrn02c$Result,Cbtrn02c$DalytranRecord,Cbtrn02c$CardXrefRecord,Cbtrn02c$TranCatBalRecord,java.util.List)»

/-- The postcondition of `updateTcatbal`, folded (the symbolic execution must not carry it
unfolded: its substitutions would rewrite the whole postcondition at every step). -/
def utPost (args : List Value) (σ0 : State) : Outcome → Prop := updateTcatbalSpec.post args σ0

attribute [irreducible] utPost

/-- Symbolic execution of `updateTcatbal`'s body from `pc` against the cut list `cuts`. -/
def UtWPc (args : List Value) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog utCallees.env 0) utBody cuts (utPost args σ0) 80 pc fr σ

attribute [irreducible] UtWPc

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ut_entry_neg (r d wX wC lC : Addr) (σ0 : State) (cuts : Cuts) (hP : UtPre σ0 r d wX wC lC)
    (hn : utIdx σ0 d wX lC < 0)
    (c1 : cuts.lookup 1 = none) (c2 : cuts.lookup 2 = none) (c3 : cuts.lookup 3 = none)
    (c4 : cuts.lookup 4 = none) (c5 : cuts.lookup 5 = none) (c6 : cuts.lookup 6 = none)
    (c7 : cuts.lookup 7 = none) (c8 : cuts.lookup 8 = none) (c9 : cuts.lookup 9 = none)
    (c10 : cuts.lookup 10 = none) (c11 : cuts.lookup 11 = none) (c12 : cuts.lookup 12 = none)
    (c13 : cuts.lookup 13 = none) (c14 : cuts.lookup 14 = none) (c15 : cuts.lookup 15 = none)
    (c16 : cuts.lookup 16 = none) (c17 : cuts.lookup 17 = none)
    (c21 : cuts.lookup 21 = some (ut21 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0)) :
    UtWPc [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 cuts 0
      (Frame.init true [.ref r, .ref d, .ref wX, .ref wC, .ref lC]) σ0 := by
  have hP' := hP
  obtain ⟨fsR, fsd, fsX, fsC, lD, lCW, lCR, sty, tyS, cd, amt, acct, xs, ds, ws, rs, m, mD, mW, mR,
    hR, hRD, hRW, hRR, hd, hdT, hsty, htyl, hdC, hdA, hX, hXA, hC, hallC, hlC, hshC, hlenC, hnC,
    hallX, hlD, hlW, hlR, hnd, hacct, hcd, i1, i2⟩ := hP
  have hn' : firstIdx (tcMatch σ0 acct (argText σ0 (.ref sty)) cd) xs < 0 := by
    have e1 : lng σ0 wX xAcctKey = acct := by simp [lng, fld, fieldsOf, hX, hXA]
    have e2 : fld σ0 d dTypeKey = .ref sty := by simp [fld, fieldsOf, hd, hdT]
    have e3 : lng σ0 d dCatKey = cd := by simp [lng, fld, fieldsOf, hd, hdC]
    have e4 : listOf σ0 lC = xs := listOf_of hlC
    unfold utIdx at hn
    rw [e1, e2, e3, e4] at hn
    exact hn
  have hlo : listOf σ0 lC = xs := listOf_of hlC
  unfold UtWPc
  jvc [utCallees, findTcatbalSig, findTcatbalSpecF, findTcatbalSpec,
    padNumSig, padNumSpec, Grows, narrow_long, narrow_cls, evalDynamic, concatRecipe,
    Native.valueOfArg, valueOfObj_eq, valueOfObjN_ref, Native.nObjStr, Native.primStr, JType.isRef,
    jstrLitT]
  · -- `findTcatbal`'s precondition
    refine ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, by jomega, ⟨_, ‹_›⟩, ‹_›⟩
  · intro r' d' wX' wC' lC' hargs' hP''
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs'
    refine ⟨by frame_simp [], by frame_simp [], by frame_simp [], by frame_simp [], by frame_simp [],
      by cls_simp; simp only [*], by cls_simp; simp only [*], by cls_simp; simp only [*],
      fun _ => ⟨by frame_simp [], _, _, by (simp only [refField, fieldsOf, listOf, *]; chain_simp),
        ?_, ?_, ?_⟩, fun h => absurd h (by omega)⟩
    · simp only [noCatJ, lng, fld, fieldsOf, argText, strOfV, Option.getD_some, *]
      chain_simp
    · simp only [State.next_alloc] at *
      jomega
    · simp only [refField, fieldsOf, *]
      refine ⟨by simp only [State.next_alloc, State.next_setObj] at *; jomega, fun z hz hzS => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzS
      chain_simp

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ut_entry_pos (r d wX wC lC : Addr) (σ0 : State) (cuts : Cuts) (hP : UtPre σ0 r d wX wC lC)
    (hp : 0 ≤ utIdx σ0 d wX lC)
    (c1 : cuts.lookup 1 = none) (c2 : cuts.lookup 2 = none) (c3 : cuts.lookup 3 = none)
    (c4 : cuts.lookup 4 = none) (c5 : cuts.lookup 5 = none) (c6 : cuts.lookup 6 = none)
    (c7 : cuts.lookup 7 = none) (c8 : cuts.lookup 8 = none) (c9 : cuts.lookup 9 = none)
    (c10 : cuts.lookup 10 = none) (c18 : cuts.lookup 18 = none) (c19 : cuts.lookup 19 = none)
    (c20 : cuts.lookup 20 = none)
    (c21 : cuts.lookup 21 = some (ut21 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0)) :
    UtWPc [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 cuts 0
      (Frame.init true [.ref r, .ref d, .ref wX, .ref wC, .ref lC]) σ0 := by
  have hP' := hP
  obtain ⟨fsR, fsd, fsX, fsC, lD, lCW, lCR, sty, tyS, cd, amt, acct, xs, ds, ws, rs, m, mD, mW, mR,
    hR, hRD, hRW, hRR, hd, hdT, hsty, htyl, hdC, hdA, hX, hXA, hC, hallC, hlC, hshC, hlenC, hnC,
    hallX, hlD, hlW, hlR, hnd, hacct, hcd, i1, i2⟩ := hP
  have e1 : lng σ0 wX xAcctKey = acct := by simp [lng, fld, fieldsOf, hX, hXA]
  have e2 : fld σ0 d dTypeKey = .ref sty := by simp [fld, fieldsOf, hd, hdT]
  have e3 : lng σ0 d dCatKey = cd := by simp [lng, fld, fieldsOf, hd, hdC]
  have hlo : listOf σ0 lC = xs := listOf_of hlC
  have hp' : 0 ≤ firstIdx (tcMatch σ0 acct (argText σ0 (.ref sty)) cd) xs := by
    unfold utIdx at hp
    rw [e1, e2, e3, hlo] at hp
    exact hp
  have hlt := firstIdx_lt (tcMatch σ0 acct (argText σ0 (.ref sty)) cd) xs
  have hidxlt : (firstIdx (tcMatch σ0 acct (argText σ0 (.ref sty)) cd) xs).toNat < xs.length := by
    omega
  obtain ⟨y, fsy, by0, hyx, hyh, hyall, hyb⟩ := hallX _ (List.getElem_mem hidxlt)
  have hget : xs[(firstIdx (tcMatch σ0 acct (argText σ0 (.ref sty)) cd) xs).toNat]? = some (.ref y) := by
    rw [List.getElem?_eq_getElem hidxlt, hyx]
  have hyC : y ≠ wC := by
    intro h; subst h
    exact hnC _ (List.getElem_mem hidxlt) hyx
  unfold UtWPc
  jvc [utCallees, findTcatbalSig, findTcatbalSpecF, findTcatbalSpec, assignTcatSig, assignTcatSpecF,
    Grows, narrow_long, narrow_cls]
  intro r' d' wX' wC' lC' hargs' hP''
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs'
  refine ⟨by frame_simp [], by frame_simp [], by frame_simp [], by frame_simp [], by frame_simp [],
    by cls_simp, by cls_simp, by cls_simp, fun h => absurd hp (by omega),
    fun _ => ⟨by frame_simp [], ?_, _, ?_, rfl⟩⟩
  · unfold utIdx
    rw [e2, ← ‹BitVec.toInt _ = firstIdx _ _›, BitVec.ofInt_toInt]
    frame_simp []
  · intro k hk
    obtain ⟨a, b⟩ := k
    rename (∀ (a : ClassName) (b : String), (a, b) ∈ tcKeys →
      Fields.get _ (a, b) = Fields.get (fieldsOf _ _) (a, b)) => hasg
    rw [hasg a b hk]
    unfold utIdx
    rw [e2, List.getD_eq_getElem?_getD, hget, Option.getD_some]
    rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ut_seg21_neg (r d wX wC lC : Addr) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : UtPre σ0 r d wX wC lC) (hn : utIdx σ0 d wX lC < 0)
    (h21 : ut21 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 fr σ)
    (hc : ∀ k, 22 ≤ k → k ≤ 40 → cuts.lookup k = none)
    (c41 : cuts.lookup 41 = some (ut41 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0)) :
    UtWPc [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 cuts 21 fr σ := by
  obtain ⟨f5, f2, f8, f0, f6, hin, hst, hio, hneg, -⟩ := h21 r d wX wC lC rfl hP
  obtain ⟨f14, sD, m1, hDl, hsD, hsD0, hfr⟩ := hneg hn
  have hP' := hP
  obtain ⟨fsR, fsd, fsX, fsC, lD, lCW, lCR, sty, tyS, cd, amt, acct, xs, ds, ws, rs, m, mD, mW, mR,
    hR, hRD, hRW, hRR, hd, hdT, hsty, htyl, hdC, hdA, hX, hXA, hC, hallC, hlC, hshC, hlenC, hnC,
    hallX, hlD, hlW, hlR, hnd, hacct, hcd, i1, i2⟩ := hP
  have hrD : refField σ0 r dispKey = lD := refField_of hR hRD
  rw [hrD] at hDl hfr
  have hlist : ∀ {z c fs}, σ0.heap z = some (.plain c fs) → z ∉ [lD] := by
    intro z c fs hz hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm; rw [hlD] at hz; cases hz
  have hd1 := hfr.heap hd (hlist hd)
  have hX1 := hfr.heap hX (hlist hX)
  have hC1 := hfr.heap hC (hlist hC)
  have hsD1 : σ.heap sD = some (.str (noCatJ (lng σ0 wX xAcctKey) (argText σ0 (fld σ0 d dTypeKey))
      (lng σ0 d dCatKey))) := hsD
  have hkeep := Hide.intro (And.intro hDl (And.intro hsD1 (And.intro hfr hsD0)))
  have e1 : lng σ0 wX xAcctKey = acct := by simp [lng, fld, fieldsOf, hX, hXA]
  have e2 : fld σ0 d dTypeKey = .ref sty := by simp [fld, fieldsOf, hd, hdT]
  have e3 : lng σ0 d dCatKey = cd := by simp [lng, fld, fieldsOf, hd, hdC]
  have e4 : lng σ0 d dAmtKey = amt := by simp [lng, fld, fieldsOf, hd, hdA]
  have e5 : fieldsOf σ0 wC = fsC := fieldsOf_of hC
  obtain ⟨q0, pq0⟩ := Option.isSome_iff_exists.1 (hallC tcAcctKey (by simp [tcKeys]))
  obtain ⟨q1, pq1⟩ := Option.isSome_iff_exists.1 (hallC tcTypeKey (by simp [tcKeys]))
  obtain ⟨q2, pq2⟩ := Option.isSome_iff_exists.1 (hallC tcCdKey (by simp [tcKeys]))
  obtain ⟨q3, pq3⟩ := Option.isSome_iff_exists.1 (hallC tcBalKey (by simp [tcKeys]))
  have hsDC : sD ≠ wC := by intro h; rw [h, hC1] at hsD1; cases hsD1
  have hDC : lD ≠ wC := by intro h; rw [h, hC] at hlD; cases hlD
  have hsDlt : sD < σ.next := State.lt_next_of_heap hsD1
  have hlDlt : lD < σ.next := State.lt_next_of_heap hDl
  clear hDl hsD hfr hsD1 h21 hP' hneg
  have c22 := hc 22 (by omega) (by omega)
  have c23 := hc 23 (by omega) (by omega)
  have c24 := hc 24 (by omega) (by omega)
  have c25 := hc 25 (by omega) (by omega)
  have c26 := hc 26 (by omega) (by omega)
  have c27 := hc 27 (by omega) (by omega)
  have c28 := hc 28 (by omega) (by omega)
  have c29 := hc 29 (by omega) (by omega)
  have c30 := hc 30 (by omega) (by omega)
  have c31 := hc 31 (by omega) (by omega)
  have c32 := hc 32 (by omega) (by omega)
  have c33 := hc 33 (by omega) (by omega)
  have c34 := hc 34 (by omega) (by omega)
  have c35 := hc 35 (by omega) (by omega)
  have c36 := hc 36 (by omega) (by omega)
  have c37 := hc 37 (by omega) (by omega)
  have c38 := hc 38 (by omega) (by omega)
  have c39 := hc 39 (by omega) (by omega)
  have c40 := hc 40 (by omega) (by omega)
  clear hc
  unfold UtWPc
  jvc [utCallees, spacesSig, spacesSpec, Grows, narrow_long, narrow_cls]
  intro r' d' wX' wC' lC' hargs' hP''
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs'
  obtain ⟨hDl, hsD1, hfr, hsD0⟩ := Hide.elim hkeep
  have hfr' : ∀ z, z < σ0.next → z ≠ refField σ0 r dispKey → σ.heap z = σ0.heap z :=
    fun z hz hne => hfr.2 z hz (by simpa using hne)
  have hnx := hfr.1
  refine ⟨hn, by frame_simp [f5], by frame_simp [f2], by frame_simp [f8], by frame_simp [f0],
    by frame_simp [f6], by frame_simp [], by frame_simp [e2], by frame_simp [],
    by cls_simp; simp only [*], by cls_simp; simp only [*], by cls_simp; simp only [*],
    ⟨sD, m1, by chain_simp, by chain_simp, hsD0⟩,
    ⟨_, by chain_simp, by fget_simp, by fget_simp; rw [e2], by fget_simp, by fget_simp, by fget_simp,
      by (repeat apply allSome_set); assumption⟩, ?_⟩
  refine ⟨by simp only [State.next_setObj] at *; jomega, fun z hz hzS => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hzS
  obtain ⟨hz1, hz2⟩ := hzS
  chain_simp

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ut_seg41 (r d wX wC lC : Addr) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : UtPre σ0 r d wX wC lC) (hn : utIdx σ0 d wX lC < 0)
    (h41 : ut41 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 fr σ)
    (hc : ∀ k, 42 ≤ k → k ≤ 50 → cuts.lookup k = none) (c68 : cuts.lookup 68 = none) :
    UtWPc [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 cuts 41 fr σ := by
  obtain ⟨-, f5, f2, f8, f0, f6, f3, f11, f4, hin, hst, hio, ⟨sD, m1, hDl, hsD, hsD0⟩,
    ⟨fsC', hC', g0, g1, g2, g3, g4, gall⟩, hfr⟩ := h41 r d wX wC lC rfl hP
  obtain ⟨fsR, fsd, fsX, fsC, lD, lCW, lCR, sty, tyS, cd, amt, acct, xs, ds, ws, rs, m, mD, mW, mR,
    hR, hRD, hRW, hRR, hd, hdT, hsty, htyl, hdC, hdA, hX, hXA, hC, hallC, hlC, hshC, hlenC, hnC,
    hallX, hlD, hlW, hlR, hnd, hacct, hcd, i1, i2⟩ := hP
  have hrD : refField σ0 r dispKey = lD := refField_of hR hRD
  rw [hrD] at hDl hfr
  have e1 : lng σ0 wX xAcctKey = acct := by simp [lng, fld, fieldsOf, hX, hXA]
  have e2 : fld σ0 d dTypeKey = .ref sty := by simp [fld, fieldsOf, hd, hdT]
  have e3 : lng σ0 d dCatKey = cd := by simp [lng, fld, fieldsOf, hd, hdC]
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd'
  obtain ⟨⟨n1, n2, n3⟩, ⟨n4, n5⟩, n6, -⟩ := hnd'
  have hDC : lD ≠ wC := by intro h; rw [h, hC] at hlD; cases hlD
  have hS : ∀ z ∈ [lD, wC], ∀ t, σ0.heap z ≠ some (.str t) := by
    intro z hz t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · rw [hlD] at ht; cases ht
    · rw [hC] at ht; cases ht
  have hrec : ∀ v ∈ xs, ∀ y, v = .ref y → y ∉ [lD, wC] := by
    intro v hv y hvy hm
    obtain ⟨y', fs, a, ts, tcs, c, hv', hy, -⟩ := hshC v hv
    rw [hvy] at hv'; cases hv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · rw [hlD] at hy; cases hy
    · exact hnC v hv hvy
  have hlC1 : σ.heap lC = some (.list .arrayList xs m) :=
    hfr.heap hlC (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                     exact ⟨fun h => n3 h.symm, fun h => by rw [h, hC] at hlC; cases hlC⟩)
  have hR1 : σ.heap r = some (.plain "Cbtrn02c$Result" fsR) :=
    hfr.heap hR (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                    exact ⟨fun h => (by rw [h, hlD] at hR; cases hR), fun h => (by rw [h, hC] at hR; simp at hR)⟩)
  have hlW1 : σ.heap lCW = some (.list .arrayList ws mW) :=
    hfr.heap hlW (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                     exact ⟨fun h => n1 h.symm, fun h => by rw [h, hC] at hlW; cases hlW⟩)
  have hsty1 : σ.heap sty = some (.str tyS) :=
    hfr.heap hsty (fun hm => hS sty hm tyS hsty)
  have hsh1 : TcatShapes σ xs := tcatShapes_frame hfr hshC hrec hS
  have hneg41 : firstIdx (tcMatch σ (lng σ0 wX xAcctKey) (argText σ (.ref sty)) (lng σ0 d dCatKey))
      (listOf σ lC) < 0 := by
    have ea : argText σ (.ref sty) = argText σ0 (.ref sty) := by
      simp only [argText, strOfV, hsty1, hsty]
    rw [ea, listOf_of hlC1, firstIdx_tcMatch_frame hfr hshC hrec hS]
    unfold utIdx at hn
    rw [e2, listOf_of hlC] at hn
    exact hn
  have hkeep := Hide.intro (And.intro hDl (And.intro hsD (And.intro hsD0 hfr)))
  clear hDl hsD hfr h41
  have c42 := hc 42 (by omega) (by omega)
  have c43 := hc 43 (by omega) (by omega)
  have c44 := hc 44 (by omega) (by omega)
  have c45 := hc 45 (by omega) (by omega)
  have c46 := hc 46 (by omega) (by omega)
  have c47 := hc 47 (by omega) (by omega)
  have c48 := hc 48 (by omega) (by omega)
  have c49 := hc 49 (by omega) (by omega)
  have c50 := hc 50 (by omega) (by omega)
  clear hc
  unfold UtWPc
  jvc [utCallees, findTcatbalSig, findTcatbalSpecF, findTcatbalSpec, copyTcatSig, copyTcatSpecF,
    abendSig, abendSpec, Grows, narrow_long, narrow_cls]
  rename_i σ1 y1 hy1n fs1 hy1h hsf1 hn1 hfr1 hi1 hs1 ho1 _ _ _ _ _ σ2 y2 hy2n hy2h hsf2 hn2 hfr2 hi2 _ _
  obtain ⟨hDl, hsD, hsD0, hfr⟩ := Hide.elim hkeep
  have hCσ1 : σ1.heap wC = some (.plain "Cbtrn02c$TranCatBalRecord" fsC') := by
    rw [hfr1 wC (State.lt_next_of_heap hC')]; exact hC'
  rw [fieldsOf_of hC'] at hsf1
  have hfw : fieldsOf (σ1.setObj lC (Obj.list ListKind.arrayList (xs ++ [Value.ref y1]) (m + 1))) wC = fsC' := by
    apply fieldsOf_of
    rw [State.heap_setObj, if_neg (fun h => by rw [h, hlC1] at hC'; cases hC')]
    exact hCσ1
  rw [hfw] at hsf2
  have hlCW : refField σ0 r cwKey = lCW := refField_of hR hRW
  have hClC : wC ≠ lC := by intro h; rw [h, hlC1] at hC'; cases hC'
  have hClW : wC ≠ lCW := by intro h; rw [h, hlW1] at hC'; cases hC'
  have hsDlC : sD ≠ lC := by intro h; rw [h, hlC1] at hsD; cases hsD
  have hsDlW : sD ≠ lCW := by intro h; rw [h, hlW1] at hsD; cases hsD
  have hsDC : sD ≠ wC := by intro h; rw [h, hC'] at hsD; cases hsD
  have hsDlt := State.lt_next_of_heap hsD
  have hlClt := State.lt_next_of_heap hlC1
  have hlWlt := State.lt_next_of_heap hlW1
  have hClt := State.lt_next_of_heap hC'
  have hDlt := State.lt_next_of_heap hDl
  have hfr' := fun (z : Addr) (hz : z < σ0.next) (h1 : z ≠ refField σ0 r dispKey) (h2 : z ≠ wC) =>
    hfr.2 z hz (by simp [h1, h2])
  have hnx0 := hfr.1
  unfold utPost
  simp only [updateTcatbalSpec, Spec.of]
  intro r' d' wX' wC' lC' hargs'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs'
  refine ⟨rfl, fun _ => ⟨sD, y1, y2, fsC', fs1, w, m1, m + 1, mW + 1, by chain_simp, by chain_simp,
    by chain_simp, g0, g1, g2, by rw [BitVec.zero_add]; exact g3, g4, by rw [listOf_of hlC]; chain_simp,
    by chain_simp, hsf1, by rw [hlCW, listOf_of hlW]; chain_simp, by chain_simp, hsf2, ?_, ?_, ?_, hsD0,
    ?_⟩, fun h => absurd h (by omega), by cls_simp; simp only [*], by cls_simp; simp only [*],
    by cls_simp; simp only [*]⟩
  · simp only at *; jomega
  · simp only at *; jomega
  · intro h; subst h; jomega
  · rw [hlCW]
    refine ⟨by simp only [State.next_setObj] at *; jomega, fun z hz hzS => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hzS
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hzS
    chain_simp

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ut_seg21_pos (r d wX wC lC : Addr) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : UtPre σ0 r d wX wC lC) (hp : 0 ≤ utIdx σ0 d wX lC)
    (h21 : ut21 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 fr σ)
    (hc : ∀ k, 51 ≤ k → k ≤ 58 → cuts.lookup k = none)
    (c59 : cuts.lookup 59 = some (ut59 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0)) :
    UtWPc [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 cuts 21 fr σ := by
  obtain ⟨f5, f2, f8, f0, f6, hin, hst, hio, -, hpos⟩ := h21 r d wX wC lC rfl hP
  obtain ⟨f14, f9, fsA, hkeys, rfl⟩ := hpos hp
  have hP' := hP
  obtain ⟨fsR, fsd, fsX, fsC, lD, lCW, lCR, sty, tyS, cd, amt, acct, xs, ds, ws, rs, m, mD, mW, mR,
    hR, hRD, hRW, hRR, hd, hdT, hsty, htyl, hdC, hdA, hX, hXA, hC, hallC, hlC, hshC, hlenC, hnC,
    hallX, hlD, hlW, hlR, hnd, hacct, hcd, i1, i2⟩ := hP
  have hlo : listOf σ0 lC = xs := listOf_of hlC
  have hlt := firstIdx_lt (tcMatch σ0 (lng σ0 wX xAcctKey) (argText σ0 (fld σ0 d dTypeKey))
    (lng σ0 d dCatKey)) xs
  have hidxlt : (utIdx σ0 d wX lC).toNat < xs.length := by
    have hp2 := hp
    unfold utIdx at hp2 ⊢; rw [hlo] at hp2 ⊢; omega
  obtain ⟨y, fsy, b, hyx, hyh, hyall, hyb⟩ := hallX _ (List.getElem_mem hidxlt)
  obtain ⟨y', fs', a, ts, tcs, c, hv, hy', ha, ht, hts, hcd'⟩ := hshC _ (List.getElem_mem hidxlt)
  have hdC : d ≠ wC := by intro h; rw [h, hC] at hd; simp at hd
  have hXC : wX ≠ wC := by intro h; rw [h, hC] at hX; simp at hX
  have hRC : r ≠ wC := by intro h; rw [h, hC] at hR; simp at hR
  rw [hyx] at hv
  have ey : y' = y := (Value.ref.inj hv).symm
  subst ey
  have efs : fs' = fsy := by
    have e := hy'.symm.trans hyh
    simp only [Option.some.injEq, Obj.plain.injEq, true_and] at e
    exact e
  subst efs
  have hrec : utRec σ0 d wX lC = y' := by
    unfold utRec
    rw [hlo, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidxlt, Option.getD_some, hyx]
    rfl
  have hkeys' : ∀ k ∈ tcKeys, Fields.get fsA k = Fields.get fs' k := by
    intro k hk
    have := hkeys k hk
    unfold utRec at hrec
    rw [hrec, fieldsOf_of hyh] at this
    exact this
  have hfa : Fields.get fsA tcAcctKey = some (.long a) := by rw [hkeys' _ (by simp [tcKeys]), ha]
  have hft : Fields.get fsA tcTypeKey = some (.ref ts) := by rw [hkeys' _ (by simp [tcKeys]), ht]
  have hfc : Fields.get fsA tcCdKey = some (.long c) := by rw [hkeys' _ (by simp [tcKeys]), hcd']
  have hfb : Fields.get fsA tcBalKey = some (.long b) := by rw [hkeys' _ (by simp [tcKeys]), hyb]
  have ea : lng σ0 y' tcAcctKey = a := by simp [lng, fld, fieldsOf, hyh, ha]
  have et : fld σ0 y' tcTypeKey = .ref ts := by simp [fld, fieldsOf, hyh, ht]
  have ec : lng σ0 y' tcCdKey = c := by simp [lng, fld, fieldsOf, hyh, hcd']
  have eb : lng σ0 y' tcBalKey = b := by simp [lng, fld, fieldsOf, hyh, hyb]
  have e4 : lng σ0 d dAmtKey = amt := by simp [lng, fld, fieldsOf, hd, hdA]
  have hkeep := Hide.intro hkeys
  clear hkeys h21 hP' hpos
  have c51 := hc 51 (by omega) (by omega)
  have c52 := hc 52 (by omega) (by omega)
  have c53 := hc 53 (by omega) (by omega)
  have c54 := hc 54 (by omega) (by omega)
  have c55 := hc 55 (by omega) (by omega)
  have c56 := hc 56 (by omega) (by omega)
  have c57 := hc 57 (by omega) (by omega)
  have c58 := hc 58 (by omega) (by omega)
  clear hc
  unfold UtWPc
  jvc [utCallees, Grows, narrow_long, narrow_cls]
  intro r' d' wX' wC' lC' hargs' hP''
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs'
  refine ⟨hp, by frame_simp [f5], by frame_simp [f2], by frame_simp [f8], by frame_simp [f0],
    by frame_simp [f6], by frame_simp [], by frame_simp [et], by frame_simp [], by frame_simp [f9],
    by cls_simp, by cls_simp, by cls_simp, fsA, Hide.elim hkeep, by chain_simp, ?_⟩
  refine ⟨by simp only [State.next_setObj]; exact Nat.le_refl _, fun z hz hzS => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hzS
  chain_simp

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ut_seg59 (r d wX wC lC : Addr) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : UtPre σ0 r d wX wC lC) (hp : 0 ≤ utIdx σ0 d wX lC)
    (h59 : ut59 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 fr σ)
    (hc : ∀ k, 60 ≤ k → k ≤ 68 → cuts.lookup k = none) :
    UtWPc [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 cuts 59 fr σ := by
  obtain ⟨-, f5, f2, f8, f0, f6, f3, f11, f4, f9, hin, hst, hio, fsA, hkeys, hwC, hfr⟩ :=
    h59 r d wX wC lC rfl hP
  obtain ⟨fsR, fsd, fsX, fsC, lD, lCW, lCR, sty, tyS, cd, amt, acct, xs, ds, ws, rs, m, mD, mW, mR,
    hR, hRD, hRW, hRR, hd, hdT, hsty, htyl, hdC, hdA, hX, hXA, hC, hallC, hlC, hshC, hlenC, hnC,
    hallX, hlD, hlW, hlR, hnd, hacct, hcd, i1, i2⟩ := hP
  have hlo : listOf σ0 lC = xs := listOf_of hlC
  have hp2 : 0 ≤ firstIdx (tcMatch σ0 (lng σ0 wX xAcctKey) (argText σ0 (fld σ0 d dTypeKey))
      (lng σ0 d dCatKey)) xs := by
    have := hp; unfold utIdx at this; rwa [hlo] at this
  have hlt := firstIdx_lt (tcMatch σ0 (lng σ0 wX xAcctKey) (argText σ0 (fld σ0 d dTypeKey))
    (lng σ0 d dCatKey)) xs
  have hidxlt : (firstIdx (tcMatch σ0 (lng σ0 wX xAcctKey) (argText σ0 (fld σ0 d dTypeKey))
      (lng σ0 d dCatKey)) xs).toNat < xs.length := by omega
  obtain ⟨y, fsy, b, hyx, hyh, hyall, hyb⟩ := hallX _ (List.getElem_mem hidxlt)
  have hm := firstIdx_get hp2 (by rw [List.getElem?_eq_getElem hidxlt, hyx])
  obtain ⟨y', fs', a, ts, tcs, c, hv, hy', ha, ht, hts, hcd'⟩ := hshC _ (List.getElem_mem hidxlt)
  rw [hyx] at hv
  have ey : y' = y := (Value.ref.inj hv).symm
  subst ey
  have efs : fs' = fsy := by
    have e := hy'.symm.trans hyh
    simp only [Option.some.injEq, Obj.plain.injEq, true_and] at e
    exact e
  subst efs
  obtain ⟨eA, eT, eC⟩ := tcMatch_key hy' ha ht hts hcd' hm
  have hrec : utRec σ0 d wX lC = y' := by
    unfold utRec utIdx
    rw [hlo, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidxlt, Option.getD_some, hyx]
    rfl
  have ea : lng σ0 y' tcAcctKey = a := by simp [lng, fld, fieldsOf, hy', ha]
  have et : fld σ0 y' tcTypeKey = .ref ts := by simp [fld, fieldsOf, hy', ht]
  have ec : lng σ0 y' tcCdKey = c := by simp [lng, fld, fieldsOf, hy', hcd']
  rw [hrec, ea, eA] at f3
  rw [hrec, et] at f11
  rw [hrec, ec, eC] at f4
  have hallA : AllSome tcKeys fsA :=
    allSome_of_same (fun k hk => by rw [hkeys k hk, hrec, fieldsOf_of hy']) hyall
  -- the objects the rest reads, in the cut state
  have hCs : ∀ z ∈ [wC], ∀ t, σ0.heap z ≠ some (.str t) := by
    intro z hz t ht'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rw [hz, hC] at ht'; cases ht'
  have hrecS : ∀ v ∈ xs, ∀ y, v = .ref y → y ∉ [wC] := by
    intro v hv y hvy hm'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
    subst hm'; exact hnC v hv hvy
  have hlC1 := hfr.heap hlC (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                                intro h; rw [h, hC] at hlC; cases hlC)
  have hR1 := hfr.heap hR (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                              intro h; rw [h, hC] at hR; simp at hR)
  have hlR1 := hfr.heap hlR (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                                intro h; rw [h, hC] at hlR; cases hlR)
  have hts1 := hfr.heap hts (fun hm' => hCs ts hm' tcs hts)
  have hsh1 : TcatShapes σ xs := tcatShapes_frame hfr hshC hrecS hCs
  have hidx59 : firstIdx (tcMatch σ (lng σ0 wX xAcctKey) (argText σ (.ref ts)) (lng σ0 d dCatKey))
      (listOf σ lC) = utIdx σ0 d wX lC := by
    have e1 : argText σ (.ref ts) = argText σ0 (.ref ts) := by
      simp only [argText, strOfV, hts1, hts]
    have e2 : argText σ0 (.ref ts) = argText σ0 (fld σ0 d dTypeKey) := by
      rw [← eT]; simp only [argText, strOfV, hts, Option.getD_some]
    rw [e1, e2, listOf_of hlC1, firstIdx_tcMatch_frame hfr hshC hrecS hCs]
    unfold utIdx
    rw [hlo]
  have hu1 : utIdx σ0 d wX lC < xs.length := by unfold utIdx; rw [hlo]; exact hlt
  clear ea ec eA eC et hrec hm
  have hkeep := Hide.intro (And.intro hkeys hfr)
  clear hkeys hfr h59
  have c60 := hc 60 (by omega) (by omega)
  have c61 := hc 61 (by omega) (by omega)
  have c62 := hc 62 (by omega) (by omega)
  have c63 := hc 63 (by omega) (by omega)
  have c64 := hc 64 (by omega) (by omega)
  have c65 := hc 65 (by omega) (by omega)
  have c66 := hc 66 (by omega) (by omega)
  have c67 := hc 67 (by omega) (by omega)
  have c68 := hc 68 (by omega) (by omega)
  clear hc
  unfold UtWPc
  jvc [utCallees, findTcatbalSig, findTcatbalSpecF, findTcatbalSpec, copyTcatSig, copyTcatSpecF,
    abendSig, abendSpec, Grows, narrow_long, narrow_cls]
  all_goals first | exact allSome_set _ _ hallA | skip
  rename_i σ1 y1 hy1n fs1 hy1h hsf1 hn1 hfr1 hi1 hs1 ho1 hy1lt _ _ _ hcr σ3 y2 hy2n _ fs2 hy2h hsf2
    hn2 hfr2 hi2 hs2 ho2 hy2lt _ _ _ _ _ _ _ _ _ _
  obtain ⟨hkeys, hfr⟩ := Hide.elim hkeep
  have hlCR : refField σ0 r crKey = lCR := refField_of hR hRR
  have hClC : wC ≠ lC := by intro h; rw [h, hlC] at hC; cases hC
  have hClR : wC ≠ lCR := by intro h; rw [h, hlR] at hC; cases hC
  have hClt := State.lt_next_of_heap hC
  have hlClt := State.lt_next_of_heap hlC
  have hlRlt := State.lt_next_of_heap hlR
  have hnx0 := hfr.1
  have hfr' := fun (z : Addr) (hz : z < σ0.next) (h2 : z ≠ wC) => hfr.2 z hz (by simp [h2])
  rw [fieldsOf_of hwC] at hsf1
  have hwC1 := (hfr1 wC (by jomega)).trans hwC
  have hfw : fieldsOf (σ1.setObj lC (Obj.list ListKind.arrayList
      ((listOf σ0 lC).set (utIdx σ0 d wX lC).toNat (Value.ref y1)) m)) wC =
      Fields.set fsA tcBalKey (Value.long (BitVec.srem (lng σ0 (utRec σ0 d wX lC) tcBalKey +
        lng σ0 d dAmtKey) 100000000000#64)) := by
    apply fieldsOf_of
    rw [State.heap_setObj, if_neg hClC]
    exact hwC1
  rw [hfw] at hsf2
  clear hfw
  unfold utPost
  simp only [updateTcatbalSpec, Spec.of]
  intro r' d' wX' wC' lC' hargs'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs'
  refine ⟨rfl, fun h => absurd h (by omega), fun _ => ⟨y1, y2, fsA, fs1, fs2, m, mR + 1, hkeys,
    by chain_simp, by chain_simp, by chain_simp, hsf1, by rw [hlCR, listOf_of hlR]; chain_simp,
    by chain_simp, hsf2, by jomega, by jomega, ?_, ?_⟩, by cls_simp; simp only [*],
    by cls_simp; simp only [*], by cls_simp; simp only [*]⟩
  · intro h; subst h; jomega
  · rw [hlCR]
    refine ⟨by simp only [State.next_setObj] at *; jomega, fun z hz hzS => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hzS
    obtain ⟨hz1, hz2, hz3⟩ := hzS
    chain_simp

end EquivLean.Modernize.Cbtrn02c.Java
