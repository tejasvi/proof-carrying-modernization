import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM3s
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunTac

/-!
# CBTRN02C → Java: `updateAccount` satisfies its contract
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem acctShapes_setObj {σ : State} {xs : List Value} {a : Addr} {o : Obj}
    (h : AcctShapes σ xs) (hne : ∀ v ∈ xs, v ≠ .ref a) : AcctShapes (σ.setObj a o) xs := by
  intro v hv
  obtain ⟨x, fs, l, rfl, hx, hl⟩ := h v hv
  have hxa : x ≠ a := fun h => hne _ hv (by rw [h])
  exact ⟨x, fs, l, rfl, by rw [State.heap_setObj, if_neg hxa]; exact hx, hl⟩

theorem arrOf_setObj_ne {σ : State} {a b : Addr} {o : Obj} (h : b ≠ a) :
    arrOf (σ.setObj a o) b = arrOf σ b := by
  simp only [arrOf, State.heap_setObj, if_neg h]

/-- The key search over the account table is unchanged by writes to objects outside it. -/
theorem firstIdx_acct_setObj {σ : State} {xs : List Value} {a : Addr} {o : Obj} {key : I64}
    (hne : ∀ v ∈ xs, v ≠ .ref a) :
    firstIdx (fun v => longFieldOf (σ.setObj a o) acctIdKey v == some key) xs =
      firstIdx (fun v => longFieldOf σ acctIdKey v == some key) xs := by
  apply firstIdx_congr'
  intro v hv
  cases v with
  | ref x =>
    have hxa : x ≠ a := fun h => hne _ hv (by rw [h])
    simp only [longFieldOf, State.heap_setObj, if_neg hxa]
  | _ => rfl

theorem fieldsOf_setObj_ne {σ : State} {a b : Addr} {o : Obj} (h : b ≠ a) :
    fieldsOf (σ.setObj a o) b = fieldsOf σ b := by
  simp only [fieldsOf, State.heap_setObj, if_neg h]

theorem fieldsOf_setObj_self {σ : State} {a : Addr} {c : ClassName} {fs : List (FieldKey × Value)}
    (h : a < σ.next) : fieldsOf (σ.setObj a (.plain c fs)) a = fs := by
  simp [fieldsOf, State.heap_setObj, h]

theorem fieldsOf_of_frame {σ σ' : State} {n : Nat} (hf : ∀ x, x < n → σ'.heap x = σ.heap x) {a : Addr}
    (ha : a < n) : fieldsOf σ' a = fieldsOf σ a := by
  simp only [fieldsOf, hf a ha]

theorem fieldsOf_congr {σ σ' : State} {a : Addr} (h : σ'.heap a = σ.heap a) :
    fieldsOf σ' a = fieldsOf σ a := by
  simp only [fieldsOf, h]

abbrev uaBody := Gen.Cbtrn02c.«updateAccount(Cbtrn02c$Result,Cbtrn02c$DalytranRecord,Cbtrn02c$AccountRecord,Cbtrn02c$AccountRecord[])»

/-- The postcondition of `updateAccount`, folded. -/
def uaPost (args : List Value) (σ0 : State) : Outcome → Prop := updateAccountSpec.post args σ0

attribute [irreducible] uaPost

/-- Symbolic execution of `updateAccount`'s body from `pc`. -/
def UaWP (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog uaCallees.env 0) uaBody [] (uaPost args σ0) 60 pc fr σ

attribute [irreducible] UaWP

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ua_entry (r d wA aD : Addr) (σ0 : State)
    (hpre : updateAccountSpec.pre [.ref r, .ref d, .ref wA, .ref aD] σ0) :
    UaWP [.ref r, .ref d, .ref wA, .ref aD] σ0 0 (Frame.init true [.ref r, .ref d, .ref wA, .ref aD]) σ0 := by
  obtain ⟨r', d', wA', aD', fsR, fsd, fsA, lAR, amt, bal, cc, cdb, id, xsA, ys, m, hargs, hR, hRk, hd,
    hamt, hA, hall, hbal, hcc, hcd, hid, haD, hlen, hsh, hne, hidx, hlAR, n1, n2, n3, n4, n5, i1,
    i2⟩ := hpre
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
  have hlAR' : refField σ0 r arKey = lAR := refField_of hR hRk
  have hfA : fieldsOf σ0 wA = fsA := fieldsOf_of hA
  have eb : lng' σ0 wA acBalKey = bal := by simp [lng', fld', fieldsOf, hA, hbal]
  have ec : lng' σ0 wA acCcKey = cc := by simp [lng', fld', fieldsOf, hA, hcc]
  have ed : lng' σ0 wA acCdKey = cdb := by simp [lng', fld', fieldsOf, hA, hcd]
  have ei : lng' σ0 wA acctIdKey = id := by simp [lng', fld', fieldsOf, hA, hid]
  have ea : lng' σ0 d dAmtKey' = amt := by simp [lng', fld', fieldsOf, hd, hamt]
  have earr : arrOf σ0 aD = xsA := by simp [arrOf, haD]
  have hkeep := Hide.intro (And.intro hlAR' (And.intro hfA (And.intro eb (And.intro ec
    (And.intro ed (And.intro ei ea))))))
  clear hlAR' hfA eb ec ed ei ea
  unfold UaWP
  jvc [uaCallees, findAccountSig', findAccountSpecF, findAccountSpec, copyAccountSig,
    copyAccountSpecF, Grows, narrow_long, narrow_cls]
  all_goals first
    | exact acctShapes_setObj (acctShapes_setObj hsh hne) hne
    | exact acctShapes_setObj hsh hne
    | ((repeat apply allSome_set); exact hall)
    | (exfalso
       have hlt0 := firstIdx_lt (fun v => longFieldOf σ0 acctIdKey v == some id) (arrOf σ0 aD)
       simp only [arrOf_setObj_ne n1, firstIdx_acct_setObj hne] at hcond
       omega)
    | skip
  all_goals (
    rename_i σ1 y1 hy1n fs1 hy1h hsf1 hn1 hfr1 hi1 hs1 ho1 hy1lt _ _ _ _ _ σ2 y2 hy2n hy2h hsf2 hn2
      hfr2 hi2 hy2lt _
    obtain ⟨hlAR', hfA, eb, ec, ed, ei, ea⟩ := Hide.elim hkeep
    simp only [arrOf_setObj_ne n1, firstIdx_acct_setObj hne] at hfr2
    simp (disch := ((try simp only [State.next_setObj]); jomega)) only [fieldsOf_setObj_self] at hsf1
    rw [fieldsOf_setObj_ne (fun h => n1 h.symm),
      fieldsOf_of (show σ1.heap wA = some (.plain _ _) by rw [hfr1 wA (by jomega), if_pos rfl])] at hsf2
    unfold uaPost
    simp only [updateAccountSpec, Spec.of]
    intro r' d' wA' aD' hargs'
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs'
    simp only [hlAR', ei, ea, eb, ec, ed, hfA]
    simp (disch := first | omega | simp) only [acctPostFs, balJ, BitVec.add_zero, if_pos, if_neg]
    refine ⟨y1, y2, fs1, w, m + 1, by chain_simp, by chain_simp, by chain_simp, hsf1,
      by rw [listOf_of hlAR]; chain_simp, by chain_simp, hsf2, by jomega, by jomega,
      by intro h; subst h; jomega, ?_, by cls_simp; simp only [*], by cls_simp; simp only [*],
      by cls_simp; simp only [*]⟩
    refine ⟨by simp only [State.next_setObj] at *; jomega, fun z hz hzS => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hzS
    obtain ⟨hz1, hz2, hz3⟩ := hzS
    chain_simp)

end EquivLean.Modernize.Cbtrn02c.Java
