import EquivLean.Modernize.Cbstm03a.Java.Term.TextsA

/-!
# CBSTM03A → Java, termination: the record text `custText`

Field reads, 19 calls of `fix` (`fixSpecT`) and `zu` (`zuSpecT`), one 19-argument concatenation. Only the
termination VC, in three segments (each its own theorem over the irreducible `ctTWP`): the entry to statement 24
(`$r20 = r.custPhoneNum1`: ten parts computed), statement 24 to statement 42 (the concatenation: nineteen parts
computed), and the concatenation. Variants: 2 at statement 24, 1 at statement 42 (no path returns to a cut).
The concatenation's arguments are looked up by `valueOfObj_str_alloc` (in the state before the recipe's
allocation), with `Native.valueOfObj_ref` off: expanding `valueOfObj` under the continuation's binder made every
earlier attempt run out of memory (design of cbA-text's `TextC5` and cbA-run6's `CustText`). The precondition
asks non-null string fields (as `CbAText.Iface3`'s `CustAt` gives). Locals: `r` 1, the parts 2-20.
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows GrowsK grows_split growsK_elim grows_refl grows_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Term

attribute [-simp] List.reduceReplicate
attribute [-jsimp] List.take_succ Native.valueOfObj_ref

abbrev custSs : List String := ["custFirstName", "custMiddleName", "custLastName", "custAddrLine1", "custAddrLine2",
  "custAddrLine3", "custAddrStateCd", "custAddrCountryCd", "custAddrZip", "custPhoneNum1", "custPhoneNum2",
  "custGovtIssuedId", "custDobYyyymmdd", "custEftAccountId", "custPriCardHolderInd", "filler1"]
abbrev custLs : List String := ["custId", "custSsn", "custFicoCreditScore"]
abbrev custTextRef : MethodRef := Gen.Cbstm03a.«custText(Cbstm03a$CustomerRecord)».ref
def custTextSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "custText", [.cls "Cbstm03a$CustomerRecord"]⟩

/-- A record argument with non-null string fields `ss` and `long` fields `ls`. -/
def RecArgNN (σ : State) (cls : ClassName) (ss ls : List String) (v : Value) : Prop :=
  v = .null ∨ ∃ a fs, v = .ref a ∧ σ.heap a = some (.plain cls fs) ∧
    (∀ f ∈ ss, ∃ x s, Fields.get fs (cls, f) = some (.ref x) ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648) ∧
    (∀ f ∈ ls, ∃ l : I64, Fields.get fs (cls, f) = some (.long l))

def custTextSpecT : Spec := ⟨fun args σ => ∃ rv, args = [rv] ∧
  RecArgNN σ "Cbstm03a$CustomerRecord" custSs custLs rv ∧ InitA σ, fun _ _ _ => True⟩

def custCalleesT : Contracts := [(fixSig, fixSpecT), (zuSig, zuSpecT), (spacesSig, spacesSpecT)]

theorem custCalleesT_ok : ∀ p ∈ custCalleesT, ContractOK Gen.prog p.1 p.2 := by
  simp only [custCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨fix_okT, zu_okT, spaces_okT⟩
theorem custCalleesT_term : ∀ p ∈ custCalleesT, ContractTerm Gen.prog p.1 p.2 := by
  simp only [custCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨fix_ctermT, zu_ctermT, spaces_ctermT⟩

/-- A string argument of the concatenation, looked up in the state before the recipe's allocation (applies only
to a known state: no expansion under the continuation's binder). -/
theorem valueOfObj_str_alloc {P : Program} {σ : State} {a : Addr} {s : JStr} {o : Obj}
    {k : JStr → State → NRes} (h : σ.heap a = some (.str s)) :
    Native.valueOfObj P (.ref a) (σ.alloc o).2 k = k s (σ.alloc o).2 := by
  rw [Native.valueOfObj_ref, State.heap_alloc_of_lt (State.lt_next_of_heap h), h]

theorem grows_alloc (σ : State) (o : Obj) : Grows σ (σ.alloc o).2 :=
  ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun _ hx => State.heap_alloc_of_lt hx o⟩
theorem grows_alloc' {σ0 σ : State} {o : Obj} (h : Grows σ0 σ) : Grows σ0 (σ.alloc o).2 :=
  grows_trans h (grows_alloc σ o)
theorem grows_k' {σ0 σ σ' : State} (h : Grows σ0 σ) (hk : GrowsK σ σ') : Grows σ0 σ' :=
  grows_trans h (growsK_elim hk)
theorem growsK_of {σ σ' : State} (h : Grows σ σ') : GrowsK σ σ' := by unfold GrowsK; exact h

/-- `Grows σ0 σ` for a state built from `σ0` by allocations and callees (`GrowsK`); reflexivity last. -/
macro "ctT_grows" : tactic => `(tactic| repeat (first | refine grows_alloc' ?_ | refine grows_k' ?_ (by assumption) | exact grows_refl _))

/-- Statement 24: the record in `r`, the first ten parts strings; the heap grown from the entry heap. -/
def custInvT24 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (a y0 y2 y4 y6 y8 y10 y12 y14 y16 y18 : Addr) (s0 s2 s4 s6 s8 s10 s12 s14 s16 s18 : JStr),
    args = [.ref a] ∧ fr.get 1 = some (.ref a) ∧
    fr.get 2 = some (.ref y0) ∧ fr.get 3 = some (.ref y2) ∧ fr.get 4 = some (.ref y4) ∧
    fr.get 5 = some (.ref y6) ∧ fr.get 6 = some (.ref y8) ∧ fr.get 7 = some (.ref y10) ∧
    fr.get 8 = some (.ref y12) ∧ fr.get 9 = some (.ref y14) ∧ fr.get 10 = some (.ref y16) ∧
    fr.get 11 = some (.ref y18) ∧
    σ.heap y0 = some (.str s0) ∧ σ.heap y2 = some (.str s2) ∧ σ.heap y4 = some (.str s4) ∧
    σ.heap y6 = some (.str s6) ∧ σ.heap y8 = some (.str s8) ∧ σ.heap y10 = some (.str s10) ∧
    σ.heap y12 = some (.str s12) ∧ σ.heap y14 = some (.str s14) ∧ σ.heap y16 = some (.str s16) ∧
    σ.heap y18 = some (.str s18) ∧
    GrowsK σ0 σ ∧ σ0.next ≤ σ.next ∧ (∀ z, z < σ0.next → σ.heap z = σ0.heap z) ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics

/-- Statement 42 (the concatenation): the nineteen parts strings. -/
def custInvT42 (_ : List Value) (_ : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (y0 y2 y4 y6 y8 y10 y12 y14 y16 y18 y20 y22 y24 y25 y27 y29 y31 y33 y34 : Addr)
    (s0 s2 s4 s6 s8 s10 s12 s14 s16 s18 s20 s22 s24 s25 s27 s29 s31 s33 s34 : JStr),
    fr.get 2 = some (.ref y0) ∧ fr.get 3 = some (.ref y2) ∧ fr.get 4 = some (.ref y4) ∧
    fr.get 5 = some (.ref y6) ∧ fr.get 6 = some (.ref y8) ∧ fr.get 7 = some (.ref y10) ∧
    fr.get 8 = some (.ref y12) ∧ fr.get 9 = some (.ref y14) ∧ fr.get 10 = some (.ref y16) ∧
    fr.get 11 = some (.ref y18) ∧ fr.get 12 = some (.ref y20) ∧ fr.get 13 = some (.ref y22) ∧
    fr.get 14 = some (.ref y24) ∧ fr.get 15 = some (.ref y25) ∧ fr.get 16 = some (.ref y27) ∧
    fr.get 17 = some (.ref y29) ∧ fr.get 18 = some (.ref y31) ∧ fr.get 19 = some (.ref y33) ∧
    fr.get 20 = some (.ref y34) ∧
    σ.heap y0 = some (.str s0) ∧ σ.heap y2 = some (.str s2) ∧ σ.heap y4 = some (.str s4) ∧
    σ.heap y6 = some (.str s6) ∧ σ.heap y8 = some (.str s8) ∧ σ.heap y10 = some (.str s10) ∧
    σ.heap y12 = some (.str s12) ∧ σ.heap y14 = some (.str s14) ∧ σ.heap y16 = some (.str s16) ∧
    σ.heap y18 = some (.str s18) ∧ σ.heap y20 = some (.str s20) ∧ σ.heap y22 = some (.str s22) ∧
    σ.heap y24 = some (.str s24) ∧ σ.heap y25 = some (.str s25) ∧ σ.heap y27 = some (.str s27) ∧
    σ.heap y29 = some (.str s29) ∧ σ.heap y31 = some (.str s31) ∧ σ.heap y33 = some (.str s33) ∧
    σ.heap y34 = some (.str s34)

def custCutsT : TermCuts := [(24, custInvT24, fun _ _ _ _ => 2), (42, custInvT42, fun _ _ _ _ => 1)]

abbrev custBodyT : Body := Gen.Cbstm03a.«custText(Cbstm03a$CustomerRecord)»

/-- The termination paths of `custText` from statement `pc`, with the cut assertions `I`. -/
@[irreducible] def ctTWP (I : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPT Gen.prog custCalleesT.env 0) custBodyT I (fun _ => True) 80 pc fr σ

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
/-- The entry: `null` (500 spaces), or to statement 24 (the first ten parts). -/
theorem ctT_entry (args : List Value) (σ0 : State) (hpre : custTextSpecT.pre args σ0) :
    ctTWP (custCutsT.inv args σ0) 0 (Frame.init true args) σ0 := by
  obtain ⟨rv, rfl, hrec, hi⟩ := hpre
  rcases hrec with rfl | ⟨a, fs, rfl, ha, hS, hL⟩
  · unfold ctTWP
    jvc [ite_nat_ne, findHandler, custCalleesT, fixSig, fixSpecT, StrArg, zuSig, zuSpecT, spacesSig, spacesSpecT,
      StrResL, GrowsT, grows_split, custCutsT, custInvT24, custInvT42, valueOfObj_str_alloc, InitA]
  · simp only [custSs, custLs, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      at hS hL
    obtain ⟨⟨x0, t0, g0, h0, l0⟩, ⟨x1, t1, g1, h1, l1⟩, ⟨x2, t2, g2, h2, l2⟩, ⟨x3, t3, g3, h3, l3⟩,
      ⟨x4, t4, g4, h4, l4⟩, ⟨x5, t5, g5, h5, l5⟩, ⟨x6, t6, g6, h6, l6⟩, ⟨x7, t7, g7, h7, l7⟩,
      ⟨x8, t8, g8, h8, l8⟩, -, -, -, -, -, -, -⟩ := hS
    obtain ⟨⟨c0, k0⟩, -, -⟩ := hL
    unfold ctTWP
    jvc [ite_nat_ne, findHandler, custCalleesT, fixSig, fixSpecT, StrArg, zuSig, zuSpecT, spacesSig, spacesSpecT,
      StrResL, GrowsT, grows_split, custCutsT, custInvT24, custInvT42, valueOfObj_str_alloc, InitA]
    all_goals first | exact growsK_of (by ctT_grows) | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
/-- Statement 24 to statement 42: the other nine parts. -/
theorem ctT_cut24 (args : List Value) (σ0 : State) (hpre : custTextSpecT.pre args σ0) (fr : Frame) (σ : State)
    (hinv : custInvT24 args σ0 fr σ) : ctTWP (custCutsT.dec args σ0 2) 24 fr σ := by
  obtain ⟨rv, rfl, hrec, hi⟩ := hpre
  obtain ⟨a, y0, y2, y4, y6, y8, y10, y12, y14, y16, y18, s0, s2, s4, s6, s8, s10, s12, s14, s16, s18, hargs,
    f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, k0, k2, k4, k6, k8, k10, k12, k14, k16, k18, hgk, hnx, hfr, hin,
    hst⟩ := hinv
  simp only [List.cons.injEq, and_true] at hargs
  subst hargs
  rcases hrec with h | ⟨a', fs, ha', hx, hS, hL⟩
  · cases h
  · cases ha'
    simp only [custSs, custLs, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      at hS hL
    obtain ⟨-, -, -, -, -, -, -, -, -, ⟨x9, t9, g9, h9, l9⟩, ⟨x10, t10, g10, h10, l10⟩,
      ⟨x11, t11, g11, h11, l11⟩, ⟨x12, t12, g12, h12, l12⟩, ⟨x13, t13, g13, h13, l13⟩,
      ⟨x14, t14, g14, h14, l14⟩, ⟨x15, t15, g15, h15, l15⟩⟩ := hS
    obtain ⟨-, ⟨c1, k1⟩, ⟨c2, k2'⟩⟩ := hL
    unfold ctTWP
    jvc [ite_nat_ne, findHandler, custCalleesT, fixSig, fixSpecT, StrArg, zuSig, zuSpecT, spacesSig, spacesSpecT,
      StrResL, GrowsT, grows_split, custCutsT, custInvT24, custInvT42, valueOfObj_str_alloc, InitA]
    all_goals first | exact growsK_of (by ctT_grows) | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
/-- Statement 42: the concatenation of the nineteen parts. -/
theorem ctT_cut42 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (hinv : custInvT42 args σ0 fr σ) :
    ctTWP (custCutsT.dec args σ0 1) 42 fr σ := by
  obtain ⟨y0, y2, y4, y6, y8, y10, y12, y14, y16, y18, y20, y22, y24, y25, y27, y29, y31, y33, y34,
    s0, s2, s4, s6, s8, s10, s12, s14, s16, s18, s20, s22, s24, s25, s27, s29, s31, s33, s34,
    f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20,
    k0, k2, k4, k6, k8, k10, k12, k14, k16, k18, k20, k22, k24, k25, k27, k29, k31, k33, k34⟩ := hinv
  unfold ctTWP
  jvc [ite_nat_ne, findHandler, custCalleesT, fixSig, fixSpecT, StrArg, zuSig, zuSpecT, spacesSig, spacesSpecT,
    StrResL, GrowsT, grows_split, custCutsT, custInvT24, custInvT42, valueOfObj_str_alloc, InitA]

set_option maxRecDepth 20000 in
theorem custText_tvcT : TermVC Gen.prog custCalleesT.env (fun _ => 0) 1 0 custTextRef custTextSpecT custCutsT 80 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, fun p hp fr σ hI => ?_⟩⟩
  · rw [SpecEnv.below_const _ _ (by decide)]
    have e := ctT_entry args σ0 hpre
    unfold ctTWP at e
    exact e
  · rw [SpecEnv.below_const _ _ (by decide)]
    simp only [custCutsT, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · have e := ctT_cut24 args σ0 hpre fr σ hI
      unfold ctTWP at e
      exact e
    · have e := ctT_cut42 args σ0 fr σ hI
      unfold ctTWP at e
      exact e

theorem custText_termT : ∀ args σ, custTextSpecT.pre args σ → MTerm Gen.prog custTextRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Contracts.valid_of_ok custCalleesT_ok)
    (Contracts.term_of_ok custCalleesT_term _ _) custText_tvcT

set_option maxHeartbeats 4000000 in
theorem custText_ctermT : ContractTerm Gen.prog custTextSig custTextSpecT := by jcontract_term [custText_termT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.custText_ctermT
