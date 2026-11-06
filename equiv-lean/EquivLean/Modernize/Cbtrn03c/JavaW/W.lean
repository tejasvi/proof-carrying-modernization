import EquivLean.Modernize.Cbtrn03c.JavaW.PadF

/-!
# CBTRN03C → Java: the working state, `incLine`, `writeLine`

`WsAt σ w ld lr rsJ reJ v`: the `Ws` object at `w` holds the scalar fields of `v`, its date
strings `rsJ`, `reJ`, and its lists at `ld` (displays) and `lr` (writes) hold the values `v.dsp`,
`v.wrs`.  The texts of the strings and list elements are tracked by the caller.  The
helpers' postconditions are functions of the entry state (`wsVOf`): a caller's symbolic execution
uses them without matching premises about the entry state.
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbtrn03c.Java

def wsC : ClassName := "Cbtrn03c$Ws"
def fdC : ClassName := "Cbtrn03c$FdReptfileRec"

/-! ## Report records -/

/-- The text of the report record `v` (field `fdReptfileRec` of an `FdReptfileRec` object). -/
def recText (σ : State) (v : Value) : Option JStr :=
  match v with
  | .ref x => match σ.heap x with
    | some (.plain c fs) =>
      if c = fdC then (match Fields.get fs (fdC, "fdReptfileRec") with
        | some s => strOf σ s
        | none => none)
      else none
    | _ => none
  | _ => none

/-- The values `ys` refer to report records holding the texts `ss`, in order. -/
def RecsAt (σ : State) (ys : List Value) (ss : List JStr) : Prop :=
  ys.map (recText σ) = ss.map some

/-- Every string and every report record of `σ` is still there in `σ'`. -/
def RecMono (σ σ' : State) : Prop :=
  StrMono σ σ' ∧ ∀ x fs, σ.heap x = some (.plain fdC fs) → σ'.heap x = some (.plain fdC fs)

theorem recText_mono {σ σ' : State} (hm : RecMono σ σ') {v : Value} {s : JStr}
    (h : recText σ v = some s) : recText σ' v = some s := by
  cases v with
  | ref x =>
    simp only [recText] at h ⊢
    cases hx : σ.heap x with
    | none => rw [hx] at h; simp at h
    | some o =>
      rw [hx] at h
      cases o with
      | plain c fs =>
        by_cases hc : c = fdC
        · subst hc
          rw [hm.2 x fs hx]
          simp only [ite_true] at h ⊢
          cases hf : Fields.get fs (fdC, "fdReptfileRec") with
          | none => rw [hf] at h; simp at h
          | some sv =>
            rw [hf] at h
            simp only at h ⊢
            obtain ⟨y, rfl, hy⟩ := strOf_eq_some_iff.1 h
            exact strOf_eq_some_iff.2 ⟨y, rfl, hm.1 y s hy⟩
        · simp [hc] at h
      | _ => simp at h
  | _ => simp [recText] at h

theorem RecsAt.mono {σ σ' : State} {ys : List Value} {ss : List JStr} (h : RecsAt σ ys ss)
    (hm : RecMono σ σ') : RecsAt σ' ys ss := by
  unfold RecsAt at *
  induction ys generalizing ss with
  | nil => exact h
  | cons y ys ih =>
    cases ss with
    | nil => simp at h
    | cons s ss =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      exact ⟨recText_mono hm h.1, ih h.2⟩

theorem RecsAt_snoc (σ : State) (ys : List Value) (y : Value) (ss : List JStr) (s : JStr) :
    RecsAt σ (ys ++ [y]) (ss ++ [s]) ↔ RecsAt σ ys ss ∧ recText σ y = some s := by
  unfold RecsAt
  simp only [List.map_append, List.map_cons, List.map_nil]
  constructor
  · intro h
    have hl : ys.length = ss.length := by
      have := congrArg List.length h
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at this
      omega
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp [hl])
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-! ## The working state -/

/-- The fields of the working state (the string fields as references) and the values in its two
lists. -/
structure WsV where
  dsp : List Value
  wrs : List Value
  first : I32
  cardRef : Value
  rsRef : Value
  reRef : Value
  acctId : I64
  lc : I64
  page : I64
  acct : I64
  grand : I64

/-- The `Ws` object at `w` holds `v`; its lists are at `ld`, `lr`.  The texts of the strings and
of the list elements are tracked by the callers. -/
def WsAt (σ : State) (w ld lr : Addr) (v : WsV) : Prop :=
  ∃ fs dm wm, σ.heap w = some (.plain wsC fs) ∧
    Fields.get fs (wsC, "displays") = some (.ref ld) ∧
    Fields.get fs (wsC, "writes") = some (.ref lr) ∧
    Fields.get fs (wsC, "firstTime") = some (.int v.first) ∧
    Fields.get fs (wsC, "currCardNum") = some v.cardRef ∧
    Fields.get fs (wsC, "startDate") = some v.rsRef ∧
    Fields.get fs (wsC, "endDate") = some v.reRef ∧
    Fields.get fs (wsC, "xrefAcctId") = some (.long v.acctId) ∧
    Fields.get fs (wsC, "lineCounter") = some (.long v.lc) ∧
    Fields.get fs (wsC, "pageTotal") = some (.long v.page) ∧
    Fields.get fs (wsC, "accountTotal") = some (.long v.acct) ∧
    Fields.get fs (wsC, "grandTotal") = some (.long v.grand) ∧
    σ.heap ld = some (.list .arrayList v.dsp dm) ∧ σ.heap lr = some (.list .arrayList v.wrs wm) ∧
    w ≠ ld ∧ w ≠ lr ∧ ld ≠ lr

/-- Field `f` of the working state object at `w` (`null` if absent). -/
def wsF (σ : State) (w : Addr) (f : String) : Value :=
  match σ.heap w with
  | some (.plain _ fs) => (Fields.get fs (wsC, f)).getD .null
  | _ => .null

def refOf : Value → Addr
  | .ref a => a
  | _ => 0

def longOf : Value → I64
  | .long x => x
  | _ => 0

def intOf : Value → I32
  | .int x => x
  | _ => 0

/-- The values in the list at `l`. -/
def listVals (σ : State) (l : Addr) : List Value :=
  match σ.heap l with
  | some (.list _ ys _) => ys
  | _ => []

/-- The working state at `w`, read from the heap. -/
def wsVOf (σ : State) (w : Addr) : WsV where
  dsp := listVals σ (refOf (wsF σ w "displays"))
  wrs := listVals σ (refOf (wsF σ w "writes"))
  first := intOf (wsF σ w "firstTime")
  cardRef := wsF σ w "currCardNum"
  rsRef := wsF σ w "startDate"
  reRef := wsF σ w "endDate"
  acctId := longOf (wsF σ w "xrefAcctId")
  lc := longOf (wsF σ w "lineCounter")
  page := longOf (wsF σ w "pageTotal")
  acct := longOf (wsF σ w "accountTotal")
  grand := longOf (wsF σ w "grandTotal")

def ldOf (σ : State) (w : Addr) : Addr := refOf (wsF σ w "displays")
def lrOf (σ : State) (w : Addr) : Addr := refOf (wsF σ w "writes")

/-- Objects other than the working state and its lists are unchanged; the heap grows. -/
def Frame3 (σ σ' : State) (w ld lr : Addr) : Prop :=
  σ.next ≤ σ'.next ∧ ∀ x, x < σ.next → x ≠ w → x ≠ ld → x ≠ lr → σ'.heap x = σ.heap x

theorem RecMono.of_grows {σ σ' : State} (hg : Grows σ σ') : RecMono σ σ' :=
  ⟨fun x s hx => by rw [hg.2 x (State.lt_next_of_heap hx), hx],
   fun x fs hx => by rw [hg.2 x (State.lt_next_of_heap hx), hx]⟩

theorem RecMono.refl (σ : State) : RecMono σ σ := ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem RecMono.trans {σ1 σ2 σ3 : State} (h1 : RecMono σ1 σ2) (h2 : RecMono σ2 σ3) :
    RecMono σ1 σ3 :=
  ⟨fun x s h => h2.1 x s (h1.1 x s h), fun x fs h => h2.2 x fs (h1.2 x fs h)⟩

/-- Writing an object that is neither a string nor a report record. -/
theorem RecMono.setObj_of {σ S : State} {a : Addr} {o : Obj} (h : RecMono σ S)
    (ha1 : ∀ s, S.heap a ≠ some (.str s)) (ha2 : ∀ fs, S.heap a ≠ some (.plain fdC fs)) :
    RecMono σ (S.setObj a o) := by
  refine ⟨fun x s hx => ?_, fun x fs hx => ?_⟩
  · have hS := h.1 x s hx
    have hxa : x ≠ a := by intro e; subst e; exact ha1 s hS
    rw [State.heap_setObj, ite_eq_right_iff.mpr (fun e => absurd e hxa), hS]
  · have hS := h.2 x fs hx
    have hxa : x ≠ a := by intro e; subst e; exact ha2 fs hS
    rw [State.heap_setObj, ite_eq_right_iff.mpr (fun e => absurd e hxa), hS]

theorem RecMono.alloc_of {σ S : State} {o : Obj} (h : RecMono σ S) : RecMono σ (S.alloc o).2 :=
  RecMono.trans h (RecMono.of_grows (grows_alloc S o))

theorem RecMono.setObj_plain {σ : State} {a : Addr} {c : ClassName} {fs : List (FieldKey × Value)}
    {o : Obj} (ha : σ.heap a = some (.plain c fs)) (hc : c ≠ fdC) : RecMono σ (σ.setObj a o) :=
  RecMono.setObj_of (RecMono.refl σ) (by intro s; rw [ha]; simp)
    (by intro fs'; rw [ha]; simp [hc])

/-! ### `incLine` and `writeLine`: small preconditions, the effect as a function of the entry state

Every helper of the working state calls these several times; their preconditions ask only for
what they read, so that a call costs little to justify. -/

/-- The fields of the object at `w`. -/
def wsFs (σ : State) (w : Addr) : List (FieldKey × Value) :=
  match σ.heap w with
  | some (.plain _ fs) => fs
  | _ => []

/-- The modification count of the list at `l`. -/
def listMods (σ : State) (l : Addr) : Nat :=
  match σ.heap l with
  | some (.list _ _ m) => m
  | _ => 0

/-- `incLine` on the counter. -/
def incL (l : I64) : I64 := (l + 1#64).srem 1000000000#64

abbrev incLineRef : MethodRef := Gen.Cbtrn03c.«incLine(Cbtrn03c$Ws)».ref

def incLineSpec : Spec := Spec.of
  (fun args σ => ∃ w fs l, args = [.ref w] ∧ σ.heap w = some (.plain wsC fs) ∧
     Fields.get fs (wsC, "lineCounter") = some (.long l))
  (fun args σ r σ' => ∀ w, args = [.ref w] →
     r = none ∧ σ' = σ.setObj w (.plain wsC (Fields.set (wsFs σ w) (wsC, "lineCounter")
       (.long (incL (longOf (wsF σ w "lineCounter")))))))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem incLine_vc : MethodVC Gen.prog (fun _ => none) 0 incLineRef incLineSpec [] 20 := by
  jverify [incLineSpec, wsC, wsFs, wsF, longOf, incL]

abbrev writeLineRef : MethodRef := Gen.Cbtrn03c.«writeLine(Cbtrn03c$Ws,java.lang.String)».ref

def writeLineCallees : Contracts := [(padSig, padSpecF)]

def writeLineSpec : Spec := Spec.of
  (fun args σ => ∃ w fs lr ys m y t, args = [.ref w, .ref y] ∧ σ.heap w = some (.plain wsC fs) ∧
     Fields.get fs (wsC, "writes") = some (.ref lr) ∧ σ.heap lr = some (.list .arrayList ys m) ∧
     σ.heap y = some (.str t) ∧ t.length < 2147483648 ∧ σ.initOf "Cbtrn03c" = .done ∧
     σ.initOf fdC = .done)
  (fun args σ r σ' => ∀ w y, args = [.ref w, .ref y] →
     ∃ rr fsR z, r = none ∧
     σ'.heap (lrOf σ w) = some (.list .arrayList (listVals σ (lrOf σ w) ++ [.ref rr])
       (listMods σ (lrOf σ w) + 1)) ∧
     σ'.heap rr = some (.plain fdC fsR) ∧ Fields.get fsR (fdC, "fdReptfileRec") = some (.ref z) ∧
     σ'.heap z = some (.str (fixJ (argText σ (.ref y)) 133)) ∧ σ.next ≤ rr ∧ σ.next ≤ z ∧
     σ.next ≤ σ'.next ∧ (∀ x, x < σ.next → x ≠ lrOf σ w → σ'.heap x = σ.heap x) ∧
     σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
     σ'.initOf "Cbtrn03c" = σ.initOf "Cbtrn03c")

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem writeLine_vc :
    MethodVC Gen.prog writeLineCallees.env 1 writeLineRef writeLineSpec [] 40 := by
  jverify [writeLineSpec, writeLineCallees, padSig, Grows, wsC, fdC,
    wsF, lrOf, refOf, listVals, listMods, argText, strOf, recText]

def incLineSig : MethodSig := ⟨"Cbtrn03c", .void, "incLine", [.cls "Cbtrn03c$Ws"]⟩
def writeLineSig : MethodSig :=
  ⟨"Cbtrn03c", .void, "writeLine", [.cls "Cbtrn03c$Ws", .cls "java.lang.String"]⟩

theorem incLine_sat : Sat Gen.prog incLineRef incLineSpec := incLine_vc.sat

theorem writeLine_sat : Sat Gen.prog writeLineRef writeLineSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    simp only [writeLineCallees, List.forall_mem_cons, List.not_mem_nil, false_implies,
      implies_true, and_true]
    exact padF_ok)) writeLine_vc

set_option maxHeartbeats 0 in
theorem incLine_ok : ContractOK Gen.prog incLineSig incLineSpec := by
  jcontract_ok [incLine_sat]

set_option maxHeartbeats 0 in
theorem writeLine_ok : ContractOK Gen.prog writeLineSig writeLineSpec := by
  jcontract_ok [writeLine_sat]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.incLine_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.writeLine_ok
