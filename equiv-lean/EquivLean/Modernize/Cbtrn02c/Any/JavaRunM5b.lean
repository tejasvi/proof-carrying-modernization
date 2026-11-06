import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5a
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM4s
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM3s
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunS3
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWS

/-!
# CBTRN02C → Java: the preconditions of `postTransaction`'s callees, from `W`

`utPre_of`: `updateTcatbal`'s precondition; `utIdx_eq`: its search finds the model's category
record (`Model.findCat`).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem forall2_ex_mem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → ∀ v ∈ xs, ∃ y, y ∈ ys ∧ R v y
  | _, _, .nil, v, hv => by simp at hv
  | _, _, .cons h hs, v, hv => by
    rcases List.mem_cons.1 hv with rfl | hv
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨y, hy, hr⟩ := forall2_ex_mem hs v hv
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

theorem tType_len {t : List EquivLean.Cobol.Rec.FVal} (hv : DalytranRecord.Valid t) :
    (Model.tType t).length = 2 := by
  have hl : t.length = 14 := (forall2_length hv).symm
  match t, hl, hv with
  | [_, v1, _, _, _, _, _, _, _, _, _, _, _, _], _, .cons _ (.cons h1 _) =>
    cases v1 with
    | num n =>
      obtain ⟨fmt, hk', -⟩ := h1
      cases hk'
    | str bs => exact h1.2

theorem nodup_four {A : Addrs} (h : [A.lD, A.lT, A.lR, A.lCW, A.lAR, A.lCR, A.lC, A.lK].Nodup) :
    [A.lD, A.lCW, A.lCR, A.lC].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h ⊢
  obtain ⟨⟨-, -, n3, -, n5, n6, -⟩, ⟨-, -, -, -, -, -⟩, ⟨-, -, -, -, -⟩, ⟨-, n20, n21, -⟩,
    ⟨-, -, -⟩, ⟨n26, -⟩, -, -⟩ := h
  refine ⟨⟨n3, n5, n6⟩, ⟨n20, n21⟩, n26, ?_⟩
  simp

theorem keysOf_tcat : keysOf TranCatBalRecord tcCls = tcKeys := by decide

theorem allSome_of_jrecT {s : Schema} {cls : ClassName} {σ : State} {a : Addr}
    {vals : List EquivLean.Cobol.Rec.FVal} {fs : List (FieldKey × Value)}
    (h : JRecAt s cls σ (.ref a) vals) (ha : σ.heap a = some (.plain cls fs)) :
    AllSome (keysOf s cls) fs := by
  intro k hk
  simp only [keysOf, List.mem_map] at hk
  obtain ⟨f, hf, rfl⟩ := hk
  exact jrecAt_isSome h ha f hf

/-- **`updateTcatbal`'s precondition** from `W` and the records of the transaction and its
cross-reference. -/
theorem utPre_of {σ : State} {A : Addrs} {s : Model.St} {d : Addr}
    {t x : List EquivLean.Cobol.Rec.FVal}
    (hW : W σ A s) (hMV : MV s) (hd : JRecAt DalytranRecord dalCls σ (.ref d) t)
    (htv : DalytranRecord.Valid t) (hx : JRecAt CardXrefRecord xrCls σ (.ref A.wX) x)
    (hxv : CardXrefRecord.Valid x) (hlen : s.cats.length < 2147483647) (hI : Inits σ) :
    UtPre σ A.r d A.wX A.wC A.lC := by
  obtain ⟨hR, hD, hT, hRj, hCW, hAR, hCR, hA, hC, hK, hwX, hwA, hwC, hwT, hfC, hfT, hnd⟩ := hW
  obtain ⟨fsR, hRo, r1, -, -, r4, -, r6, -, -⟩ := hR
  obtain ⟨ds, mD, hlD, -, -⟩ := hD
  obtain ⟨ws, mW, hlW, -, -, -⟩ := hCW
  obtain ⟨rs, mR, hlR, -, -, -⟩ := hCR
  obtain ⟨xs, m, hlC, hfC0, hwsC, -⟩ := hC
  obtain ⟨fsC, hCo, hkC⟩ := hwC
  obtain ⟨⟨a, fsd, s0, s1, s3, s4, s7, s8, s9, s10, s11, s12, s13, hae, hdo, -, -, g1, t1, g2, -,
    -, -, -, g5, -⟩, b0, b1, n2, b3, b4, n5, n6, b7, b8, b9, b10, b11, b12, b13, rfl, h2, -, -⟩ :=
    dalobj_of_rec hd htv
  cases hae
  obtain ⟨⟨a', fsX, -, -, hxe, hxo, -, -, -, gx2, -⟩, xb0, xn1, xn2, xb3, rfl, -, hx2, -⟩ :=
    xobj_of_rec hx hxv
  cases hxe
  obtain ⟨hI1, -, -, -, -, hI6, -, -⟩ := hI
  have hxsl := forall2_length hfC0
  refine ⟨fsR, fsd, fsX, fsC, A.lD, A.lCW, A.lCR, s1, _, _, _, _, xs, ds, ws, rs, m, mD, mW, mR,
    hRo, r1, r4, r6, hdo, g1, t1, ?_, g2, g5, hxo, gx2, hCo, ?_, hlC, ?_, by omega, ?_, ?_, hlD, hlW,
    hlR, nodup_four hnd, ?_, ?_, hI1, hI6⟩
  · rw [cp037Str_length]
    have := tType_len htv
    simp only [Model.tType, Model.strOf, List.getD_cons_succ, List.getD_cons_zero] at this
    simp only [bAt, Model.strOf, List.getD_cons_succ, List.getD_cons_zero]
    omega
  · rw [← keysOf_tcat]; exact hkC
  · exact tcatShapes_of (fun v hv => by
      obtain ⟨y, hy, hr⟩ := forall2_ex_mem hfC0 v hv
      exact ⟨y, hy, (tcatobj_of_rec hr (hMV.2.1 y hy)).1⟩)
  · intro v hv he
    exact hwsC v hv A.wC (by simp [Addrs.ws]) he
  · intro v hv
    obtain ⟨y, hy, hr⟩ := forall2_ex_mem hfC0 v hv
    obtain ⟨⟨z', fs', _, _, hze, hz', -, -, -, -, hb, -⟩, -⟩ := tcatobj_of_rec hr (hMV.2.1 y hy)
    obtain ⟨z, fs, rfl, hz, hf⟩ := hr
    have ez : z' = z := (Value.ref.inj hze).symm
    subst ez
    have efs : fs' = fs := by
      have e := hz'.symm.trans hz
      simp only [Option.some.injEq, Obj.plain.injEq, true_and] at e
      exact e
    subst efs
    refine ⟨z', fs', _, rfl, hz, ?_, hb⟩
    rw [← keysOf_tcat]
    exact allSome_of_jrecT ⟨z', fs', rfl, hz, hf⟩ hz
  · show -9223372036854775808 < (BitVec.ofInt 64 xn2).toInt
    rw [toInt_ofInt_of_natAbs hx2]; omega
  · show -9223372036854775808 < (BitVec.ofInt 64 n2).toInt
    rw [toInt_ofInt_of_natAbs h2]; omega

theorem keysOf_acct'' : keysOf AccountRecord acCls = acKeys := by decide

theorem firstIdx_nonneg_of_mem {α : Type} {p : α → Bool} {l : List α} {b : α} (hb : b ∈ l)
    (hp : p b = true) : 0 ≤ firstIdx p l := by
  unfold firstIdx
  cases hf : l.findIdx? p with
  | none =>
    rw [List.findIdx?_eq_none_iff] at hf
    exact absurd hp (by simp [hf b hb])
  | some j => simp

/-- **`updateAccount`'s precondition** from `W`, the transaction record and the account found. -/
theorem uaPre_of {σ : State} {A : Addrs} {s : Model.St} {d : Addr} {t a : List EquivLean.Cobol.Rec.FVal}
    (hW : W σ A s) (hMV : MV s) (hAd : ∃ xs, σ.heap A.aD = some (.array (.cls acCls) xs))
    (hd : JRecAt DalytranRecord dalCls σ (.ref d) t) (htv : DalytranRecord.Valid t)
    (ha : JRecAt AccountRecord acCls σ (.ref A.wA) a) (hav : AccountRecord.Valid a)
    (hin : ∃ b ∈ s.accts, Model.aId b = Model.aId a) (hI : Inits σ) :
    updateAccountSpec.pre [.ref A.r, .ref d, .ref A.wA, .ref A.aD] σ := by
  obtain ⟨hR, hD, hT, hRj, hCW, hAR, hCR, hA, hC, hK, hwX, hwA, hwC, hwT, hfC, hfT, hnd⟩ := hW
  obtain ⟨fsR, hRo, -, -, -, -, r5, -, -, -⟩ := hR
  obtain ⟨ys, mAR, hlAR, -, -, -⟩ := hAR
  obtain ⟨et, xsA, hlA, hfA, hwsA, hnA⟩ := hA
  obtain ⟨xs', hxs'⟩ := hAd
  have exs : xs' = xsA := by
    have e := hxs'.symm.trans hlA
    simp only [Option.some.injEq, Obj.array.injEq] at e
    exact e.2
  rw [exs] at hxs'
  obtain ⟨fsW, hwo, hkW⟩ := hwA
  obtain ⟨hdo', -⟩ := dalobj_of_rec hd htv
  obtain ⟨d', fsd, _, _, _, _, _, _, _, _, _, _, _, hde, hdo, -, -, -, -, -, -, -, -, -, g5, -⟩ := hdo'
  have ed : d' = d := (Value.ref.inj hde).symm
  subst ed
  obtain ⟨hao', n0, _, _, _, _, _, _, _, _, _, _, _, _, haeq, h0, -⟩ := acctobj_of_rec ha hav
  obtain ⟨w', fsA, _, _, _, _, _, _, _, hae, hao, a0, -, -, a2, -, -, -, -, -, -, -, -, a8, a9, -⟩ := hao'
  have ew : w' = A.wA := (Value.ref.inj hae).symm
  subst ew
  have hid0 : (Model.aId a).natAbs < 10 ^ 18 := by
    rw [show Model.aId a = n0 by rw [haeq]; rfl]; exact h0
  have efs : fsW = fsA := by
    have e := hwo.symm.trans hao
    simp only [Option.some.injEq, Obj.plain.injEq, true_and] at e
    exact e
  rw [← efs] at a0 a2 a8 a9
  obtain ⟨hI1, -, hI3, -, -, -, -, -⟩ := hI
  refine ⟨A.r, d', A.wA, A.aD, fsR, fsd, fsW, A.lAR, _, _, _, _, _, xsA, ys, mAR, rfl, hRo, r5, hdo,
    g5, hwo, by rw [← keysOf_acct'']; exact hkW, a2, a8, a9, a0, hxs', hnA, ?_, ?_, ?_, hlAR,
    ?_, ?_, ?_, ?_, ?_, hI1, hI3⟩
  · exact acctShapes_of (fun v hv => by
      obtain ⟨y, hy, hr⟩ := forall2_ex_mem hfA v hv
      exact ⟨y, hy, (acctobj_of_rec hr (hMV.1 y hy)).1⟩)
  · intro v hv he
    exact hwsA v hv A.wA (by simp [Addrs.ws]) he
  · have := acct_first hfA hMV.1 _ hid0
    rw [show nAt a 0 = Model.aId a from rfl, this]
    obtain ⟨b, hb, hbe⟩ := hin
    exact firstIdx_nonneg_of_mem hb (by simp [hbe])
  · intro he; rw [he, hwo] at hxs'; cases hxs'
  · intro he; rw [he, hwo] at hlAR; cases hlAR
  · intro he; rw [he, hwo] at hRo; simp at hRo
  · intro he; rw [he, hwo] at hdo; simp at hdo
  · intro he; rw [he, hxs'] at hlAR; cases hlAR

theorem firstIdx_none {α : Type} {p : α → Bool} {l : List α} (h : ∀ x ∈ l, p x = false) :
    firstIdx p l = -1 := by
  unfold firstIdx
  rw [List.findIdx?_eq_none_iff.2 (by intro x hx; simp [h x hx])]

/-- No written id equals the new one: `findKey` finds nothing. -/
theorem firstIdx_strs_none {σ : State} {ks : List Value} {strs : List JStr} {idcs : JStr}
    (h : Forall2 (JStrAt σ) ks strs) (hn : idcs ∉ strs) :
    firstIdx (fun v => strOfV σ v == some idcs) ks = -1 := by
  apply firstIdx_none
  intro v hv
  obtain ⟨st, hst, hr⟩ := forall2_ex_mem h v hv
  obtain ⟨x, rfl, hx⟩ := hr
  simp only [strOfV, hx]
  rw [beq_eq_false_iff_ne]
  intro he
  cases he
  exact hn hst

theorem strShapes_of {σ : State} {ks : List Value} {strs : List JStr} (h : Forall2 (JStrAt σ) ks strs) :
    StrShapes σ ks := by
  intro v hv
  obtain ⟨st, -, x, rfl, hx⟩ := forall2_ex_mem h v hv
  exact ⟨x, st, rfl, hx⟩

theorem keysOf_tran' : keysOf TranRecord trCls = trKeys := by decide

/-- **`writeTransaction`'s precondition** from `W` and `tranWs` holding a record with a new id. -/
theorem wtPre_of {σ : State} {A : Addrs} {s : Model.St} {b0 : List UInt8}
    {rest : List EquivLean.Cobol.Rec.FVal}
    (hW : W σ A s) (hwT : JRecAt TranRecord trCls σ (.ref A.wT) (.str b0 :: rest))
    (hnew : tidJ (.str b0 :: rest) ∉ s.tranW.map tidJ) (hI : Inits σ) :
    writeTransactionSpec.pre [.ref A.r, .ref A.wT, .ref A.lK] σ := by
  obtain ⟨hR, hD, hT, hRj, hCW, hAR, hCR, hA, hC, hK, hwX, hwA, hwC, hwT0, hfC, hfT, hnd⟩ := hW
  obtain ⟨fsR, hRo, -, r2, -, -, -, -, -, -⟩ := hR
  obtain ⟨ts, mT, hlT, -, -, -⟩ := hT
  obtain ⟨ks, mK, hlK, hfK, hnK⟩ := hK
  obtain ⟨fsT, hto, hkT⟩ := hwT0
  obtain ⟨w', fsT', hwe, hto', hf⟩ := hwT
  have ew : w' = A.wT := (Value.ref.inj hwe).symm
  subst ew
  have efs : fsT = fsT' := by
    have e := hto.symm.trans hto'
    simp only [Option.some.injEq, Obj.plain.injEq, true_and] at e
    exact e
  subst efs
  obtain ⟨sv, hsv, sId, rfl, hsId⟩ : ∃ sv, Fields.get fsT (trCls, "tranId") = some sv ∧
      ∃ sId, sv = .ref sId ∧ σ.heap sId = some (.str (cp037Str b0)) := by
    cases hf with
    | cons j0 _ => exact j0
  obtain ⟨hI1, -, -, -, -, -, -, hI8⟩ := hI
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd'
  refine ⟨A.r, A.wT, A.lK, fsR, A.lT, fsT, sId, _, ks, mK, ts, mT, rfl, hRo, r2, hto,
    by rw [← keysOf_tran']; exact hkT, hsv, hsId, hlK, hnK, strShapes_of hfK,
    firstIdx_strs_none hfK hnew, hlT, fun h => hnd'.2.1.2.2.2.2.2 h.symm, hI1, hI8⟩

end EquivLean.Modernize.Cbtrn02c.Java
