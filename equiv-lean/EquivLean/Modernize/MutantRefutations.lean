import EquivLean.Modernize.Cbcus01c.JavaProof
import EquivLean.Modernize.Cbact01c.JavaProof
import EquivLean.Modernize.Cbact04c.Every.JavaProof

/-!
# Machine-checked Lean refutations of the three A3 Java timeout mutants (`J4`, `M2`, `M5r`)

During the A3 certificate mutation tests, 97 of the 100 seeded semantic mutants failed with an
explicit unsolved proof goal at the mutated statement, while three Java mutants (`CBCUS01C` `J4`,
`CBACT01C` `M2`, and `CBACT04C` Every `M5r`) did not finish symbolic execution (`jverify`) within
their 30–83 minute per-module timeout.

Here we refute the generated `Statement` of each of those three mutants directly in Lean as a
kernel-checked theorem (`¬ Statement_J4`, `¬ Statement_M2`, `¬ Statement_M5r`), without running
`jverify`:
1. We import the mutant's Soot Jimple (`mut_cbcus01c_j4`, `mut_cbact01c_m2`, `mut_cbact04c_m5r`)
   via `jimple_import` and state its generated `Statement` (`Statement_J4`, `Statement_M2`,
   `Statement_M5r`), identical to the program's `Java.Statement` with `Gen.prog` and `runRef`
   bound to the mutant's `Program` and entry `MethodRef`.
2. We construct a concrete 1-record input satisfying every hypothesis of `Statement` (`Valid`,
   Table 2 `Domain`, length bounds, `<File>At`, and class initialization `.done`).
3. We evaluate the mutant on that input once via the structurally recursive interpreter `runMK`
   (`decide +kernel`), lift the evaluation to `Runs` via `runs_of_runMK` (`runStep_sound`), use the
   COBOL output theorem (`cbcus01c_lists` / `Glue.cobol_outputs`), and show that `Rel` is false.
-/

open Jimple EquivLean.Jimple
open EquivLean.Cobol.Rec

jimple_import "EquivLean/Demo/Gen/Jimple/mut_cbcus01c_j4" as EquivLean.Modernize.MutantRefutations.GenJ4
jimple_import "EquivLean/Demo/Gen/Jimple/mut_cbact01c_m2" as EquivLean.Modernize.MutantRefutations.GenM2
jimple_import "EquivLean/Demo/Gen/Jimple/mut_cbact04c_m5r" as EquivLean.Modernize.MutantRefutations.GenM5r

namespace EquivLean.Modernize.MutantRefutations

/-! ## Two-counter structurally recursive (kernel-reducible) Jimple interpreter

`runCall P stmtFuel d m args σ` uses `d` for call-stack depth (`d = 10` suffices for all CardDemo
programs) and `stmtFuel` for statements per method activation (`1500`). Both `runCall` and `runBody`
return `Option Outcome` directly (no tuple return or `mutual` block), so kernel evaluation runs in
linear time in the number of executed statements. -/

def runRK0 {α : Type} (P : Program) (rM : MethodRef → List Value → State → Option Outcome) :
    Res α → Option α
  | .ret a => some a
  | .call _ (.method m) args σ k =>
    match rM m args σ with
    | some o => runRK0 P rM (k o)
    | none => none
  | .call sig (.virtual c) args σ k =>
    match P.selectVirtual c sig.sub with
    | .jimple m =>
      match rM m args σ with
      | some o => runRK0 P rM (k o)
      | none => none
    | .none why =>
      if P.concrete c then runRK0 P rM (k (.wrong why)) else none
    | .native _ => none
  | .choose k => runRK0 P rM (k 0)

def runV0 (P : Program) (rM : MethodRef → List Value → State → Option Outcome)
    (sig : MethodSig) (c : ClassName) (args : List Value) (σ : State) : Option Outcome :=
  match P.selectVirtual c sig.sub with
  | .jimple m => rM m args σ
  | .native lc =>
    match args with
    | .ref a :: rest =>
      match σ.heap a with
      | some (.plain c' fs) =>
        if c' = c then
          match Native.plainInst P sig lc a c fs rest σ with
          | some r => (runRK0 P rM r).map EvOut.toOutcome
          | none => some (.wrong "no model for library method")
        else none
      | _ => none
    | _ => none
  | .none why => if P.concrete c then some (.wrong why) else none

def runRK {α : Type} (P : Program) (rM : MethodRef → List Value → State → Option Outcome) :
    Res α → Option α
  | .ret a => some a
  | .call _ (.method m) args σ k =>
    match rM m args σ with
    | some o => runRK P rM (k o)
    | none => none
  | .call sig (.virtual c) args σ k =>
    match runV0 P rM sig c args σ with
    | some o => runRK P rM (k o)
    | none => none
  | .choose k => runRK P rM (k 0)

def runBody (P : Program) (rM : MethodRef → List Value → State → Option Outcome) :
    Nat → Body → Nat → Frame → State → Option Outcome
  | 0 => fun _ _ _ _ => none
  | k + 1 => fun b pc fr σ =>
    match runRK P rM (step P b pc fr σ) with
    | some r =>
      match afterStep P b pc fr r with
      | .cont pc' fr' σ' => runBody P rM k b pc' fr' σ'
      | .done o => some o
    | none => none

def runCall (P : Program) (stmtFuel : Nat) :
    Nat → MethodRef → List Value → State → Option Outcome
  | 0 => fun _ _ _ => none
  | d + 1 => fun m args σ =>
    match m.decl.body with
    | some b => runBody P (runCall P stmtFuel d) stmtFuel b 0 (Frame.init m.decl.mods.isStatic args) σ
    | none => some (.wrong "abstract or native method")

def runMK (P : Program) (stmtFuel : Nat) (m : MethodRef) (args : List Value) (σ : State) :
    Option Outcome :=
  runCall P stmtFuel 10 m args σ

theorem runRK0_sound {P : Program}
    {rM : MethodRef → List Value → State → Option Outcome}
    (hM : ∀ m args σ o, rM m args σ = some o → MExec P m args σ o)
    {α : Type} : ∀ (r : Res α) (a : α), runRK0 P rM r = some a → RExec P r a
  | .ret a', a, h => by simp [runRK0] at h; subst h; exact .ret
  | .call _ (.method m) args σ k, a, h => by
    simp only [runRK0] at h
    split at h
    · next o ho => exact .callM (hM m args σ o ho) (runRK0_sound hM (k o) a h)
    · simp at h
  | .call sig (.virtual c) args σ k, a, h => by
    simp only [runRK0] at h
    split at h
    · next m hm =>
      split at h
      · next o ho => exact .callV (.jimple hm (hM m args σ o ho)) (runRK0_sound hM (k o) a h)
      · simp at h
    · next why hwhy =>
      split at h
      · next hc => exact .callV (.none hwhy hc) (runRK0_sound hM (k _) a h)
      · simp at h
    · simp at h
  | .choose k, a, h => by
    simp only [runRK0] at h
    exact .choose 0 (runRK0_sound hM (k 0) a h)

theorem runV0_sound {P : Program}
    {rM : MethodRef → List Value → State → Option Outcome}
    (hM : ∀ m args σ o, rM m args σ = some o → MExec P m args σ o) :
    ∀ sig c args σ o, runV0 P rM sig c args σ = some o → VExec P sig c args σ o := by
  intro sig c args σ o h
  unfold runV0 at h
  split at h
  · next m hm => exact .jimple hm (hM m args σ o h)
  · next lc hlc =>
    split at h
    · next a rest =>
      split at h
      · next c' fs hheap =>
        split at h
        · next hc =>
          subst hc
          split at h
          · next r hr =>
            cases hrun : runRK0 P rM r with
            | none => simp [hrun] at h
            | some ev =>
              simp [hrun] at h
              subst h
              exact .native hlc hheap hr (runRK0_sound hM r ev hrun)
          · next hr => cases h; exact .noModel hlc hheap hr
        · simp at h
      · simp at h
    · simp at h
  · next why hwhy =>
    split at h
    · next hc => cases h; exact .none hwhy hc
    · simp at h

theorem runRK_sound {P : Program}
    {rM : MethodRef → List Value → State → Option Outcome}
    (hM : ∀ m args σ o, rM m args σ = some o → MExec P m args σ o)
    {α : Type} : ∀ (r : Res α) (a : α), runRK P rM r = some a → RExec P r a
  | .ret a', a, h => by simp [runRK] at h; subst h; exact .ret
  | .call _ (.method m) args σ k, a, h => by
    simp only [runRK] at h
    split at h
    · next o ho => exact .callM (hM m args σ o ho) (runRK_sound hM (k o) a h)
    · simp at h
  | .call sig (.virtual c) args σ k, a, h => by
    simp only [runRK] at h
    split at h
    · next o ho => exact .callV (runV0_sound hM sig c args σ o ho) (runRK_sound hM (k o) a h)
    · simp at h
  | .choose k, a, h => by
    simp only [runRK] at h
    exact .choose 0 (runRK_sound hM (k 0) a h)

theorem runBody_sound {P : Program}
    {rM : MethodRef → List Value → State → Option Outcome}
    (hM : ∀ m args σ o, rM m args σ = some o → MExec P m args σ o) :
    ∀ k b pc fr σ o, runBody P rM k b pc fr σ = some o → BExec P b pc fr σ o
  | 0, _, _, _, _, _, h => by simp [runBody] at h
  | k + 1, b, pc, fr, σ, o, h => by
    unfold runBody at h
    split at h
    · next r hr =>
      split at h
      · next pc' fr' σ' hc =>
        exact .cont (runRK_sound hM _ r hr) hc (runBody_sound hM k b pc' fr' σ' o h)
      · next o' hd =>
        cases h
        exact .done (runRK_sound hM _ r hr) hd
    · simp at h

theorem runCall_sound (P : Program) (stmtFuel : Nat) :
    ∀ d m args σ o, runCall P stmtFuel d m args σ = some o → MExec P m args σ o
  | 0, _, _, _, _, h => by simp [runCall] at h
  | d + 1, m, args, σ, o, h => by
    unfold runCall at h
    split at h
    · next b hb =>
      exact .body hb (runBody_sound (runCall_sound P stmtFuel d) stmtFuel b 0 _ σ o h)
    · next hb => cases h; exact .noBody hb

theorem runs_of_runMK {P : Program} {fuel : Nat} {m : MethodRef} {args : List Value} {σ : State}
    {o : Out} (h : runMK P fuel m args σ = some o.toOutcome) : Runs (Call.mk P m args σ) o :=
  runCall_sound P fuel 10 m args σ _ h

def checkRunMK (P : Program) (fuel : Nat) (m : MethodRef) (args : List Value) (σ : State)
    (f : Option Value → State → Bool) : Bool :=
  match runMK P fuel m args σ with
  | some (.normal v s) => f v s
  | _ => false

theorem of_checkRunMK {P : Program} {fuel : Nat} {m : MethodRef} {args : List Value} {σ : State}
    {f : Option Value → State → Bool}
    (h : checkRunMK P fuel m args σ f = true) :
    ∃ v s, Runs (Call.mk P m args σ) (.normal v s) ∧ f v s = true := by
  unfold checkRunMK at h
  cases hrun : runMK P fuel m args σ with
  | none => rw [hrun] at h; cases h
  | some o =>
    rw [hrun] at h
    cases o with
    | normal v s => exact ⟨v, s, runs_of_runMK hrun, h⟩
    | exc _ _ => cases h
    | wrong _ => cases h

/-! ## Heap construction on `Array Obj` and decidable `JRecAt` / `<File>At` / `Valid` checkers -/

def allocFieldM (cls : ClassName) (mem : Array Obj) (f : Field) :
    EquivLean.Cobol.Rec.FVal → (FieldKey × Value) × Array Obj
  | .num v => (((cls, f.jname), .long (BitVec.ofInt 64 v)), mem)
  | .str bs => (((cls, f.jname), .ref mem.size), mem.push (.str (cp037Str bs)))

def allocFieldsM (cls : ClassName) : Array Obj → List Field → List EquivLean.Cobol.Rec.FVal →
    List (FieldKey × Value) × Array Obj
  | mem, [], _ => ([], mem)
  | mem, _, [] => ([], mem)
  | mem, f :: fs, v :: vs =>
    let (kv, mem1) := allocFieldM cls mem f v
    let (kvs, mem2) := allocFieldsM cls mem1 fs vs
    (kv :: kvs, mem2)

def allocRecM (s : Schema) (cls : ClassName) (mem : Array Obj)
    (vals : List EquivLean.Cobol.Rec.FVal) : Addr × Array Obj :=
  let (fs, mem1) := allocFieldsM cls mem s.fields vals
  (mem1.size, mem1.push (.plain cls fs))

def allocFile1M (s : Schema) (cls : ClassName) (mem : Array Obj)
    (vals : List EquivLean.Cobol.Rec.FVal) : Addr × Array Obj :=
  let (r, mem1) := allocRecM s cls mem vals
  (mem1.size, mem1.push (.array (.cls cls) [.ref r]))

def checkJFieldAt (σ : State) (cls : ClassName) (fs : List (FieldKey × Value)) (f : Field) :
    EquivLean.Cobol.Rec.FVal → Bool
  | .num v => Fields.get fs (cls, f.jname) == some (.long (BitVec.ofInt 64 v))
  | .str bs =>
    match Fields.get fs (cls, f.jname) with
    | some (.ref x) =>
      match σ.heap x with
      | some (.str s') => s' == cp037Str bs
      | _ => false
    | _ => false

theorem jFieldAt_of_check {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)}
    {f : Field} {v : EquivLean.Cobol.Rec.FVal} (h : checkJFieldAt σ cls fs f v = true) :
    jFieldAt σ cls fs f v := by
  cases v with
  | num n => exact LawfulBEq.eq_of_beq h
  | str bs =>
    unfold checkJFieldAt at h
    cases hg : Fields.get fs (cls, f.jname) with
    | none => rw [hg] at h; cases h
    | some val =>
      rw [hg] at h
      cases val with
      | ref x =>
        dsimp only at h
        cases hh : σ.heap x with
        | none => rw [hh] at h; cases h
        | some obj =>
          rw [hh] at h
          cases obj with
          | str s' =>
            have hs : s' = cp037Str bs := LawfulBEq.eq_of_beq h
            subst hs
            exact ⟨.ref x, hg, x, rfl, hh⟩
          | _ => cases h
      | _ => cases h

def checkJFieldsAt (σ : State) (cls : ClassName) (fs : List (FieldKey × Value)) :
    List Field → List EquivLean.Cobol.Rec.FVal → Bool
  | [], [] => true
  | f :: flds, v :: vs => checkJFieldAt σ cls fs f v && checkJFieldsAt σ cls fs flds vs
  | _, _ => false

theorem jFieldsAt_of_check {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)}
    {flds : List Field} {vals : List EquivLean.Cobol.Rec.FVal}
    (h : checkJFieldsAt σ cls fs flds vals = true) :
    Forall2 (fun f val => jFieldAt σ cls fs f val) flds vals := by
  revert vals h
  induction flds with
  | nil =>
    intro vals h
    cases vals with
    | nil => exact .nil
    | cons _ _ => cases h
  | cons f flds ih =>
    intro vals h
    cases vals with
    | nil => cases h
    | cons v vs =>
      simp only [checkJFieldsAt, Bool.and_eq_true] at h
      exact .cons (jFieldAt_of_check h.1) (ih h.2)

def checkJRecAt (s : Schema) (cls : ClassName) (σ : State) (v : Value)
    (vals : List EquivLean.Cobol.Rec.FVal) : Bool :=
  match v with
  | .ref x =>
    match σ.heap x with
    | some (.plain c fs) => (c == cls) && checkJFieldsAt σ cls fs s.fields vals
    | _ => false
  | _ => false

theorem jRecAt_of_check (s : Schema) (cls : ClassName) {σ : State} {v : Value}
    {vals : List EquivLean.Cobol.Rec.FVal} (h : checkJRecAt s cls σ v vals = true) :
    JRecAt s cls σ v vals := by
  unfold checkJRecAt at h
  cases v with
  | ref x =>
    dsimp only at h
    cases hh : σ.heap x with
    | none => rw [hh] at h; cases h
    | some obj =>
      rw [hh] at h
      cases obj with
      | plain c fs =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨rfl, h2⟩
        exact ⟨x, fs, rfl, hh, jFieldsAt_of_check h2⟩
      | _ => cases h
  | _ => cases h

def checkFileAt1 (s : Schema) (cls : ClassName) (σ : State) (a : Addr)
    (vals : List EquivLean.Cobol.Rec.FVal) : Bool :=
  match σ.heap a with
  | some (.array _ [x]) => checkJRecAt s cls σ x vals
  | _ => false

theorem fileAt1_of_check (s : Schema) (cls : ClassName) {σ : State} {a : Addr}
    {vals : List EquivLean.Cobol.Rec.FVal} (h : checkFileAt1 s cls σ a vals = true) :
    ∃ et xs, σ.heap a = some (.array et xs) ∧ xs.length < 2147483648 ∧
      Forall2 (JRecAt s cls σ) xs [vals] := by
  unfold checkFileAt1 at h
  cases hh : σ.heap a with
  | none => rw [hh] at h; cases h
  | some obj =>
    rw [hh] at h
    cases obj with
    | array et xs =>
      cases xs with
      | nil => cases h
      | cons x rest =>
        cases rest with
        | nil =>
          exact ⟨et, [x], rfl, by simp, .cons (jRecAt_of_check s cls h) .nil⟩
        | cons _ _ => cases h
    | _ => cases h

def checkJStrAt (σ : State) (a : Addr) (s : JStr) : Bool :=
  match σ.heap a with
  | some (.str s') => s' == s
  | _ => false

theorem jStrAt_of_check {σ : State} {a : Addr} {s : JStr} (h : checkJStrAt σ a s = true) :
    JStrAt σ (.ref a) s := by
  unfold checkJStrAt at h
  cases hh : σ.heap a with
  | none => rw [hh] at h; cases h
  | some obj =>
    rw [hh] at h
    cases obj with
    | str s' =>
      have hs : s' = s := LawfulBEq.eq_of_beq h
      subst hs
      exact ⟨a, rfl, hh⟩
    | _ => cases h

def checkFieldValid (f : Field) : EquivLean.Cobol.Rec.FVal → Bool
  | .num v =>
    match f.desc.kind with
    | .num fmt => decide (0 < fmt.digits ∧ fmt.digits ≤ 18 ∧ fmt.Holds {} v ∧ fmt.byteLen {} = f.desc.len)
    | _ => false
  | .str bs =>
    match f.desc.kind with
    | .alnum _ => bs.length == f.desc.len
    | _ => false

theorem fieldValid_of_check {f : Field} {v : EquivLean.Cobol.Rec.FVal}
    (h : checkFieldValid f v = true) : f.Valid v := by
  cases v with
  | num n =>
    unfold checkFieldValid at h
    cases hk : f.desc.kind <;> rw [hk] at h
    case num fmt =>
      have hd : 0 < fmt.digits ∧ fmt.digits ≤ 18 ∧ fmt.Holds {} n ∧ fmt.byteLen {} = f.desc.len :=
        of_decide_eq_true h
      exact ⟨fmt, hk, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2⟩
    all_goals cases h
  | str bs =>
    unfold checkFieldValid at h
    cases hk : f.desc.kind <;> rw [hk] at h
    case alnum j => exact ⟨⟨j, hk⟩, LawfulBEq.eq_of_beq h⟩
    all_goals cases h

def checkFieldsValid : List Field → List EquivLean.Cobol.Rec.FVal → Bool
  | [], [] => true
  | f :: fs, v :: vs => checkFieldValid f v && checkFieldsValid fs vs
  | _, _ => false

theorem schemaValid_of_check {s : Schema} {vals : List EquivLean.Cobol.Rec.FVal}
    (h : checkFieldsValid s.fields vals = true) : s.Valid vals := by
  unfold Schema.Valid
  revert vals h
  induction s.fields with
  | nil =>
    intro vals h
    cases vals with
    | nil => exact .nil
    | cons _ _ => cases h
  | cons f fs ih =>
    intro vals h
    cases vals with
    | nil => cases h
    | cons v vs =>
      simp only [checkFieldsValid, Bool.and_eq_true] at h
      exact .cons (fieldValid_of_check h.1) (ih h.2)

def defaultFVal (f : Field) : EquivLean.Cobol.Rec.FVal :=
  match f.desc.kind with
  | .num _ => .num 0
  | _ => .str (List.replicate f.desc.len 64)

/-! ## 1. `CBCUS01C` Java mutant `J4` (first and last name swapped in `fmtRecord`) -/

section J4
open EquivLean.Modernize.Cbcus01c.Java

abbrev runRef_J4 : MethodRef := GenJ4.Cbcus01c.«run(Cbcus01c$CustomerRecord[])».ref

def Statement_J4 : Prop :=
  ∀ (vals1 : List (List EquivLean.Cobol.Rec.FVal)),
    (∀ v ∈ vals1, CustomerRecord.Valid v) →
    vals1.length < 2 ^ 27 →
    ∀ n : Nat, vals1.length < n →
    ∀ (σ : State) (a1 : Addr),
    CustfileFileAt σ a1 vals1 →
    σ.initOf "Cbcus01c" = .done →
    σ.initOf "Cbcus01c$Result" = .done →
    σ.initOf "Cbcus01c$CustomerRecord" = .done →
    Sim Rel (Call.mk GenJ4.prog runRef_J4 [.ref a1] σ)
      (EquivLean.Cobol.run CardDemo.Cbcus01c {} (n + 20)
        (CardDemo.Cbcus01c.initState initMem [(1, vals1.map CustomerRecord.encode)]))

def custRec_J4 : List EquivLean.Cobol.Rec.FVal :=
  (CustomerRecord.fields.map defaultFVal).set 1 (.str (193 :: List.replicate 24 64))
    |>.set 3 (.str (194 :: List.replicate 24 64))

def addr_J4 : Addr := (allocFile1M CustomerRecord "Cbcus01c$CustomerRecord" #[] custRec_J4).1
def sigma_J4 : State :=
  { mem := (allocFile1M CustomerRecord "Cbcus01c$CustomerRecord" #[] custRec_J4).2
    statics := []
    inits := [("Cbcus01c", .done), ("Cbcus01c$Result", .done), ("Cbcus01c$CustomerRecord", .done)]
    monitors := []
    out := [] }

theorem valid_J4 : ∀ v ∈ [custRec_J4], CustomerRecord.Valid v := by
  intro v hv
  simp only [List.mem_singleton] at hv
  subst hv
  exact schemaValid_of_check (by decide +kernel)

theorem fileAt_J4 : CustfileFileAt sigma_J4 addr_J4 [custRec_J4] :=
  fileAt1_of_check CustomerRecord "Cbcus01c$CustomerRecord" (by decide +kernel)

def getDisp1Char9_J4 : Out → Option JChar
  | .normal (some (.ref res)) σ' =>
    match σ'.heap res with
    | some (.plain "Cbcus01c$Result" fs) =>
      match Fields.get fs ("Cbcus01c$Result", "displays") with
      | some (.ref l) =>
        match σ'.heap l with
        | some (.list _ (_ :: .ref s1 :: _) _) =>
          match σ'.heap s1 with
          | some (.str str1) => some (str1.getD 9 0)
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

theorem getDisp1Char9_of_rel_J4 {ot : Out} {os : Cobol.Sem.Res} (h : Rel ot os)
    {d0 d1 : List UInt8} {ds : List (List UInt8)} (hdisp : displays os.2 = d0 :: d1 :: ds) :
    getDisp1Char9_J4 ot = some ((cp037Str d1).getD 9 0) := by
  obtain ⟨σ', res, fs, l, k, xs, mods, rfl, hres, hl, hlist, hpairs, _⟩ := h
  rw [hdisp] at hpairs
  rcases hpairs with _ | ⟨_, _ | ⟨⟨s1, rfl, hstr1⟩, _⟩⟩
  simp [getDisp1Char9_J4, hres, hl, hlist, hstr1]

set_option maxRecDepth 100000 in
theorem check_J4_eq :
    checkRunMK GenJ4.prog 2000 runRef_J4 [.ref addr_J4] sigma_J4
      (fun v s => getDisp1Char9_J4 (.normal v s) !=
        some ((cp037Str (CustomerRecord.encode custRec_J4)).getD 9 0)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Refutation of `CBCUS01C` Java mutant `J4`**: `Statement_J4` is false. -/
theorem mut_J4_not_statement : ¬ Statement_J4 := by
  intro hS
  have hv := valid_J4
  have hm : initMem.size = 1023 := by rw [initMem_size, CardDemo.Cbcus01c.memSize_eq]
  have hlen : ∀ r ∈ [custRec_J4].map CustomerRecord.encode, r.length = 500 := by
    intro r hr; obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hr
    exact Schema.length_encode customerRecord_contig (hv v hv')
  obtain ⟨hstop, hdisp⟩ := CardDemo.Cbcus01c.cbcus01c_lists initMem hm
    ([custRec_J4].map CustomerRecord.encode) 2 hlen (by decide)
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbcus01c.run {} (2 + 20)
      (CardDemo.Cbcus01c.initState initMem [(1, [custRec_J4].map CustomerRecord.encode)])) := by
    rw [EquivLean.Cobol.Ok, hstop]; rfl
  have hsafe : Safe (EquivLean.Cobol.run CardDemo.Cbcus01c {} (2 + 20)
      (CardDemo.Cbcus01c.initState initMem [(1, [custRec_J4].map CustomerRecord.encode)])) :=
    (EquivLean.Cobol.safe_exec_iff _).2 hok
  have hsim := hS [custRec_J4] hv (by decide) 2 (by decide) sigma_J4 addr_J4 fileAt_J4 rfl rfl rfl
  obtain ⟨v, s, hruns, hc⟩ := of_checkRunMK check_J4_eq
  have hne : getDisp1Char9_J4 (.normal v s) ≠
      some ((cp037Str (CustomerRecord.encode custRec_J4)).getD 9 0) :=
    bne_iff_ne.1 hc
  obtain ⟨_, hmatch⟩ := hsim hsafe
  obtain ⟨os, hos, hrel⟩ := hmatch (.normal v s) hruns
  obtain ⟨rfl, _⟩ := (EquivLean.Cobol.runs_exec_iff _ os).1 hos
  have hdisp' : displays (CardDemo.Cbcus01c.run {} (2 + 20)
      (CardDemo.Cbcus01c.initState initMem [(1, [custRec_J4].map CustomerRecord.encode)])).2 =
      CardDemo.Cbcus01c.startMsg :: CustomerRecord.encode custRec_J4 ::
        [CustomerRecord.encode custRec_J4, CardDemo.Cbcus01c.endMsg] := by
    rw [← displays_eq, hdisp]; rfl
  exact hne (getDisp1Char9_of_rel_J4 hrel hdisp')

end J4

/-! ## 2. `CBACT01C` Java mutant `M2` (`cobdatft` call dropped in `run`) -/

section M2
open EquivLean.Modernize.Cbact01c.Java

abbrev runRef_M2 : MethodRef := GenM2.Cbact01c.«run(Cbact01c$AccountRecord[])».ref

def Statement_M2 : Prop :=
  ∀ (vals1 : List (List EquivLean.Cobol.Rec.FVal)),
    (∀ v ∈ vals1, AccountRecord.Valid v) →
    vals1.length < 2 ^ 27 →
    ∀ n : Nat, vals1.length < n →
    ∀ (σ : State) (a1 : Addr),
    AcctfileFileAt σ a1 vals1 →
    σ.initOf "Cbact01c" = .done →
    σ.initOf "Cbact01c$Result" = .done →
    σ.initOf "Cbact01c$AccountRecord" = .done →
    σ.initOf "Cbact01c$ArrArrayRec" = .done →
    σ.initOf "Cbact01c$OutAcctRec" = .done →
    Sim Rel (Call.mk GenM2.prog runRef_M2 [.ref a1] σ)
      (EquivLean.Cobol.run CardDemo.Cbact01c
        { call := Cobol.Ext.cardDemoCalls CardDemo.Cbact01c.cfg } (n + 40)
        (CardDemo.Cbact01c.initState initMem [(1, vals1.map AccountRecord.encode)]))

/-- Witness account record: `ACCT-REISSUE-DATE` (field 7) is `"2024-01-31"` (`[242, 240, 242, 244,
96, 240, 241, 96, 243, 241]` in EBCDIC). -/
def acctRec_M2 : List EquivLean.Cobol.Rec.FVal :=
  (AccountRecord.fields.map defaultFVal).set 7
    (.str [242, 240, 242, 244, 96, 240, 241, 96, 243, 241])

def addr_M2 : Addr := (allocFile1M AccountRecord "Cbact01c$AccountRecord" #[] acctRec_M2).1
def sigma_M2 : State :=
  { mem := (allocFile1M AccountRecord "Cbact01c$AccountRecord" #[] acctRec_M2).2
    statics := []
    inits := [("Cbact01c", .done), ("Cbact01c$Result", .done), ("Cbact01c$AccountRecord", .done),
      ("Cbact01c$ArrArrayRec", .done), ("Cbact01c$OutAcctRec", .done)]
    monitors := []
    out := [] }

theorem valid_M2 : ∀ v ∈ [acctRec_M2], AccountRecord.Valid v := by
  intro v hv
  simp only [List.mem_singleton] at hv
  subst hv
  exact schemaValid_of_check (by decide +kernel)

theorem fileAt_M2 : AcctfileFileAt sigma_M2 addr_M2 [acctRec_M2] :=
  fileAt1_of_check AccountRecord "Cbact01c$AccountRecord" (by decide +kernel)

def getOutReissue_M2 : Out → Option JStr
  | .normal (some (.ref res)) σ' =>
    match σ'.heap res with
    | some (.plain "Cbact01c$Result" fs) =>
      match Fields.get fs ("Cbact01c$Result", "outFileWrites") with
      | some (.ref lw) =>
        match σ'.heap lw with
        | some (.list _ (.ref x0 :: _) _) =>
          match σ'.heap x0 with
          | some (.plain "Cbact01c$OutAcctRec" fs0) =>
            match Fields.get fs0 ("Cbact01c$OutAcctRec", "outAcctReissueDate") with
            | some (.ref s) =>
              match σ'.heap s with
              | some (.str str) => some str
              | _ => none
            | _ => none
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

theorem getOutReissue_of_rel_M2 {ot : Out} {os : Cobol.Sem.Res} (h : Rel ot os)
    {ow0 : List EquivLean.Cobol.Rec.FVal}
    (hout : (writes 2 os.2).map OutAcctRec.decode = [some ow0])
    {v0 v1 v2 v3 v4 v5 v6 : EquivLean.Cobol.Rec.FVal} {bs7 : List UInt8}
    {vs : List EquivLean.Cobol.Rec.FVal}
    (how0 : ow0 = v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: .str bs7 :: vs) :
    getOutReissue_M2 ot = some (cp037Str bs7) := by
  obtain ⟨σ', res, fs, _, _, _, _, rfl, hres, _, _, _,
    ⟨lw, kw, ws, mw, hlw, hlistw, hws⟩, _, _, _⟩ := h
  cases hw2 : writes 2 os.2 with
  | nil => rw [hw2] at hout; cases hout
  | cons r0 rs =>
    rw [hw2] at hout hws
    simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at hout
    rcases hout with ⟨hr0, rfl⟩
    rcases hws with _ | ⟨⟨vals, ⟨x0, fs0, rfl, hx0, hflds⟩, hdec⟩, _⟩
    rw [hr0] at hdec
    cases hdec
    rw [how0] at hflds
    rcases hflds with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨hf7, _⟩⟩⟩⟩⟩⟩⟩⟩
    obtain ⟨sref, hget7, s, rfl, hstr7⟩ := hf7
    have hj7 : (OutAcctRec.fields.getD 7 default).jname = "outAcctReissueDate" := rfl
    simp [getOutReissue_M2, hres, hlw, hlistw, hx0]
    rw [hget7]
    simp [hstr7]

def ow0_M2 : List EquivLean.Cobol.Rec.FVal :=
  (EquivLean.Modernize.Cbact01c.Model.run [acctRec_M2]).outWrites.headD []

def expectedBs7_M2 : List UInt8 :=
  match ow0_M2.getD 7 default with
  | .str bs => bs
  | .num _ => []

theorem how0_M2 : (EquivLean.Modernize.Cbact01c.Model.run [acctRec_M2]).outWrites.map some =
    [some (ow0_M2.getD 0 default :: ow0_M2.getD 1 default ::
      ow0_M2.getD 2 default :: ow0_M2.getD 3 default :: ow0_M2.getD 4 default ::
      ow0_M2.getD 5 default :: ow0_M2.getD 6 default :: .str expectedBs7_M2 :: ow0_M2.drop 8)] := rfl

set_option maxRecDepth 100000 in
theorem cobol_safe_M2 (vals1 : List (List EquivLean.Cobol.Rec.FVal))
    (hv : ∀ v ∈ vals1, AccountRecord.Valid v) (n : Nat) (hn : vals1.length < n) :
    Safe (EquivLean.Cobol.run CardDemo.Cbact01c
      { call := Cobol.Ext.cardDemoCalls CardDemo.Cbact01c.cfg } (n + 40)
      (CardDemo.Cbact01c.initState initMem [(1, vals1.map AccountRecord.encode)])) ∧
    ∀ os, Runs (EquivLean.Cobol.run CardDemo.Cbact01c
      { call := Cobol.Ext.cardDemoCalls CardDemo.Cbact01c.cfg } (n + 40)
      (CardDemo.Cbact01c.initState initMem [(1, vals1.map AccountRecord.encode)])) os →
      (writes 2 os.2).map OutAcctRec.decode =
        (EquivLean.Modernize.Cbact01c.Model.run vals1).outWrites.map some := by
  obtain ⟨hstop, _, hout, _, _⟩ := EquivLean.Modernize.Cbact01c.Glue.cobol_outputs vals1 hv n hn
  rw [← initMem_eq] at hstop hout
  have hsafe : Safe (EquivLean.Cobol.run CardDemo.Cbact01c
      { call := Cobol.Ext.cardDemoCalls CardDemo.Cbact01c.cfg } (n + 40)
      (CardDemo.Cbact01c.initState initMem [(1, vals1.map AccountRecord.encode)])) := by
    rw [EquivLean.Cobol.run, EquivLean.Cobol.safe_exec_iff, EquivLean.Cobol.Ok, hstop]; rfl
  refine ⟨hsafe, fun os hos => ?_⟩
  rw [hos.1]
  exact hout

set_option maxRecDepth 100000 in
theorem check_M2_eq :
    checkRunMK GenM2.prog 2000 runRef_M2 [.ref addr_M2] sigma_M2
      (fun v s => getOutReissue_M2 (.normal v s) != some (cp037Str expectedBs7_M2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Refutation of `CBACT01C` Java mutant `M2`**: `Statement_M2` is false. -/
theorem mut_M2_not_statement : ¬ Statement_M2 := by
  intro hS
  obtain ⟨hsafe, hwrites⟩ := cobol_safe_M2 [acctRec_M2] valid_M2 2 (by decide)
  have hsim := hS [acctRec_M2] valid_M2 (by decide) 2 (by decide) sigma_M2 addr_M2 fileAt_M2
    rfl rfl rfl rfl rfl
  obtain ⟨v, s, hruns, hc⟩ := of_checkRunMK check_M2_eq
  have hne : getOutReissue_M2 (.normal v s) ≠ some (cp037Str expectedBs7_M2) :=
    bne_iff_ne.1 hc
  obtain ⟨_, hmatch⟩ := hsim hsafe
  obtain ⟨os, hos, hrel⟩ := hmatch (.normal v s) hruns
  have hout := (hwrites os hos).trans how0_M2
  exact hne (getOutReissue_of_rel_M2 hrel hout rfl)

end M2

/-! ## 3. `CBACT04C` Every Java mutant `M5r` (`"DEFAULT   "` changed to `"DEFUALT   "`) -/

section M5r
open EquivLean.Modernize.Cbact04c.Every.Java

abbrev runRef_M5r : MethodRef :=
  GenM5r.Cbact04c.«run(Cbact04c$TranCatBalRecord[],Cbact04c$CardXrefRecord[],Cbact04c$AccountRecord[],Cbact04c$DisGroupRecord[],Cbact04c$ExternalParms,java.lang.String)».ref

def Statement_M5r : Prop :=
  ∀ (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal)),
    (∀ v ∈ vals1, TranCatBalRecord.Valid v) →
    (∀ v ∈ vals2, CardXrefRecord.Valid v) →
    (∀ v ∈ vals3, AccountRecord.Valid v) →
    (∀ v ∈ vals4, DisGroupRecord.Valid v) →
    ∀ (link1 : List EquivLean.Cobol.Rec.FVal), ExternalParms.Valid link1 →
    ∀ (clk : List UInt8), CurrentDate clk →
    EquivLean.Modernize.Cbact04c.Every.Domain vals1 vals2 vals3 vals4 link1 →
    vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 27 →
    ∀ n : Nat, vals1.length + vals2.length + vals3.length + vals4.length < n →
    ∀ (σ : State) (a1 a2 a3 a4 p1 cs : Addr),
    TcatbalFileAt σ a1 vals1 →
    XrefFileAt σ a2 vals2 →
    AccountFileAt σ a3 vals3 →
    DiscgrpFileAt σ a4 vals4 →
    JRecAt ExternalParms "Cbact04c$ExternalParms" σ (.ref p1) link1 →
    JStrAt σ (.ref cs) (cp037Str clk) →
    σ.initOf "Cbact04c" = .done →
    σ.initOf "Cbact04c$Result" = .done →
    σ.initOf "Cbact04c$AccountRecord" = .done →
    σ.initOf "Cbact04c$CardXrefRecord" = .done →
    σ.initOf "Cbact04c$DisGroupRecord" = .done →
    σ.initOf "Cbact04c$TranCatBalRecord" = .done →
    σ.initOf "Cbact04c$ExternalParms" = .done →
    σ.initOf "Cbact04c$TranRecord" = .done →
    Sim Rel (Call.mk GenM5r.prog runRef_M5r [.ref a1, .ref a2, .ref a3, .ref a4, .ref p1, .ref cs] σ)
      (EquivLean.Cobol.run CardDemo.Cbact04c { clock := fun _ => clk } (n + 60)
        (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
          [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
           (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)]))

def tcat1_M5r : List EquivLean.Cobol.Rec.FVal :=
  [.num 1, .str [240, 241], .num 1, .num 100, .str (List.replicate 22 64)]

def xref1_M5r : List EquivLean.Cobol.Rec.FVal :=
  [.str (List.replicate 16 241), .num 1, .num 1, .str (List.replicate 14 64)]

def acct1_M5r : List EquivLean.Cobol.Rec.FVal :=
  (AccountRecord.fields.map defaultFVal).set 0 (.num 1)
    |>.set 11 (.str [199, 217, 215, 241, 64, 64, 64, 64, 64, 64])

def disc1_M5r : List EquivLean.Cobol.Rec.FVal :=
  [.str [196, 197, 198, 193, 228, 211, 227, 64, 64, 64], .str [240, 241], .num 1, .num 1000,
   .str (List.replicate 28 64)]

def link1_M5r : List EquivLean.Cobol.Rec.FVal :=
  [.num 10, .str (List.replicate 10 240)]

def clk_M5r : List UInt8 := List.replicate 16 240 ++ [0x4E, 240, 240, 240, 240]

def buildMem_M5r : Addr × Addr × Addr × Addr × Addr × Addr × Array Obj :=
  let (a1, m1) := allocFile1M TranCatBalRecord "Cbact04c$TranCatBalRecord" #[] tcat1_M5r
  let (a2, m2) := allocFile1M CardXrefRecord "Cbact04c$CardXrefRecord" m1 xref1_M5r
  let (a3, m3) := allocFile1M AccountRecord "Cbact04c$AccountRecord" m2 acct1_M5r
  let (a4, m4) := allocFile1M DisGroupRecord "Cbact04c$DisGroupRecord" m3 disc1_M5r
  let (p1, m5) := allocRecM ExternalParms "Cbact04c$ExternalParms" m4 link1_M5r
  let cs := m5.size
  let m6 := m5.push (.str (cp037Str clk_M5r))
  (a1, a2, a3, a4, p1, cs, m6)

def a1_M5r : Addr := buildMem_M5r.1
def a2_M5r : Addr := buildMem_M5r.2.1
def a3_M5r : Addr := buildMem_M5r.2.2.1
def a4_M5r : Addr := buildMem_M5r.2.2.2.1
def p1_M5r : Addr := buildMem_M5r.2.2.2.2.1
def cs_M5r : Addr := buildMem_M5r.2.2.2.2.2.1
def sigma_M5r : State :=
  { mem := buildMem_M5r.2.2.2.2.2.2
    statics := []
    inits := [("Cbact04c", .done), ("Cbact04c$Result", .done), ("Cbact04c$AccountRecord", .done),
      ("Cbact04c$CardXrefRecord", .done), ("Cbact04c$DisGroupRecord", .done),
      ("Cbact04c$TranCatBalRecord", .done), ("Cbact04c$ExternalParms", .done),
      ("Cbact04c$TranRecord", .done)]
    monitors := []
    out := [] }

theorem valid1_M5r : ∀ v ∈ [tcat1_M5r], TranCatBalRecord.Valid v := by
  intro v hv; simp only [List.mem_singleton] at hv; subst hv
  exact schemaValid_of_check (by decide +kernel)

theorem valid2_M5r : ∀ v ∈ [xref1_M5r], CardXrefRecord.Valid v := by
  intro v hv; simp only [List.mem_singleton] at hv; subst hv
  exact schemaValid_of_check (by decide +kernel)

theorem valid3_M5r : ∀ v ∈ [acct1_M5r], AccountRecord.Valid v := by
  intro v hv; simp only [List.mem_singleton] at hv; subst hv
  exact schemaValid_of_check (by decide +kernel)

theorem valid4_M5r : ∀ v ∈ [disc1_M5r], DisGroupRecord.Valid v := by
  intro v hv; simp only [List.mem_singleton] at hv; subst hv
  exact schemaValid_of_check (by decide +kernel)

theorem validL_M5r : ExternalParms.Valid link1_M5r :=
  schemaValid_of_check (by decide +kernel)

def checkCurrDate (c : List UInt8) : Bool :=
  (c.length == 21) &&
  (List.range 21).all (fun i => i == 16 || (0xF0 ≤ c.getD i 0 && c.getD i 0 ≤ 0xF9)) &&
  (c.getD 16 0 == 0x4E || c.getD 16 0 == 0x60)

theorem currDate_of_check {c : List UInt8} (h : checkCurrDate c = true) : CurrentDate c := by
  unfold checkCurrDate at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  refine ⟨h.1.1, fun i hi h16 => ?_, h.2⟩
  rcases h.1.2 i hi with rfl | hd
  · exact absurd rfl h16
  · exact hd

theorem currDate_M5r : CurrentDate clk_M5r :=
  currDate_of_check (by decide +kernel)

theorem domain_M5r :
    EquivLean.Modernize.Cbact04c.Every.Domain [tcat1_M5r] [xref1_M5r] [acct1_M5r] [disc1_M5r] link1_M5r := by
  refine ⟨by decide, fun i j k hij hjk hk => ?_⟩
  simp only [List.length_singleton] at hk
  omega

theorem file1_M5r : TcatbalFileAt sigma_M5r a1_M5r [tcat1_M5r] :=
  fileAt1_of_check TranCatBalRecord "Cbact04c$TranCatBalRecord" (by decide +kernel)

theorem file2_M5r : XrefFileAt sigma_M5r a2_M5r [xref1_M5r] :=
  fileAt1_of_check CardXrefRecord "Cbact04c$CardXrefRecord" (by decide +kernel)

theorem file3_M5r : AccountFileAt sigma_M5r a3_M5r [acct1_M5r] :=
  fileAt1_of_check AccountRecord "Cbact04c$AccountRecord" (by decide +kernel)

theorem file4_M5r : DiscgrpFileAt sigma_M5r a4_M5r [disc1_M5r] :=
  fileAt1_of_check DisGroupRecord "Cbact04c$DisGroupRecord" (by decide +kernel)

theorem parmAt_M5r : JRecAt ExternalParms "Cbact04c$ExternalParms" sigma_M5r (.ref p1_M5r) link1_M5r :=
  jRecAt_of_check ExternalParms "Cbact04c$ExternalParms" (by decide +kernel)

theorem clkAt_M5r : JStrAt sigma_M5r (.ref cs_M5r) (cp037Str clk_M5r) :=
  jStrAt_of_check (by decide +kernel)

def getAbended_M5r : Out → Option (BitVec 32)
  | .normal (some (.ref res)) σ' =>
    match σ'.heap res with
    | some (.plain "Cbact04c$Result" fs) =>
      match Fields.get fs ("Cbact04c$Result", "abended") with
      | some (.int b) => some b
      | _ => none
    | _ => none
  | _ => none

theorem getAbended_of_rel_M5r {ot : Out} {os : Cobol.Sem.Res} (h : Rel ot os) :
    getAbended_M5r ot = some (if abended os.1 then 1 else 0) := by
  obtain ⟨σ', res, fs, _, _, _, _, rfl, hres, _, _, _, _, _, hab⟩ := h
  simp [getAbended_M5r, hres, hab]

set_option maxRecDepth 100000 in
theorem cobol_safe_M5r (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal))
    (link1 : List EquivLean.Cobol.Rec.FVal) (clk : List UInt8)
    (hv1 : ∀ v ∈ vals1, TranCatBalRecord.Valid v)
    (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, AccountRecord.Valid v)
    (hv4 : ∀ v ∈ vals4, DisGroupRecord.Valid v)
    (hl : ExternalParms.Valid link1) (hc : CurrentDate clk)
    (hD : EquivLean.Modernize.Cbact04c.Every.Domain vals1 vals2 vals3 vals4 link1)
    (n : Nat) (hn : vals1.length + vals2.length + vals3.length + vals4.length < n) :
    Safe (EquivLean.Cobol.run CardDemo.Cbact04c { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
        [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
         (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)])) ∧
    ∀ os, Runs (EquivLean.Cobol.run CardDemo.Cbact04c { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
        [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
         (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)])) os →
      abended os.1 = (EquivLean.Modernize.Cbact04c.Model.runE
        vals1 vals2 vals3 vals4 (EquivLean.Modernize.Cbact04c.Model.parmOf link1) clk).abended := by
  obtain ⟨hsig, _, _, _, habC⟩ := EquivLean.Modernize.Cbact04c.Every.Glue.cobol_outputs
    vals1 vals2 vals3 vals4 link1 clk hv1 hv2 hv3 hv4 hl hc hD n (by omega)
  rw [← initMem_eq] at hsig habC
  have hsafe : Safe (EquivLean.Cobol.run CardDemo.Cbact04c { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
        [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
         (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)])) := by
    rw [EquivLean.Cobol.run, EquivLean.Cobol.safe_exec_iff, EquivLean.Cobol.Ok]
    rcases hsig with hs | hs <;> rw [hs] <;> rfl
  refine ⟨hsafe, fun os hos => ?_⟩
  rw [hos.1]
  exact habC

set_option maxRecDepth 100000 in
theorem check_M5r_eq :
    checkRunMK GenM5r.prog 2000 runRef_M5r
      [.ref a1_M5r, .ref a2_M5r, .ref a3_M5r, .ref a4_M5r, .ref p1_M5r, .ref cs_M5r] sigma_M5r
      (fun v s => getAbended_M5r (.normal v s) == some 1) = true := by
  decide +kernel

theorem hab0_M5r : (EquivLean.Modernize.Cbact04c.Model.runE
    [tcat1_M5r] [xref1_M5r] [acct1_M5r] [disc1_M5r]
    (EquivLean.Modernize.Cbact04c.Model.parmOf link1_M5r) clk_M5r).abended = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Refutation of `CBACT04C` Every Java mutant `M5r`**: `Statement_M5r` is false. -/
theorem mut_M5r_not_statement : ¬ Statement_M5r := by
  intro hS
  obtain ⟨hsafe, habFn⟩ := cobol_safe_M5r
    [tcat1_M5r] [xref1_M5r] [acct1_M5r] [disc1_M5r] link1_M5r clk_M5r
    valid1_M5r valid2_M5r valid3_M5r valid4_M5r validL_M5r currDate_M5r domain_M5r 5 (by decide)
  have hsim := hS [tcat1_M5r] [xref1_M5r] [acct1_M5r] [disc1_M5r]
    valid1_M5r valid2_M5r valid3_M5r valid4_M5r link1_M5r validL_M5r clk_M5r currDate_M5r
    domain_M5r (by decide) 5 (by decide) sigma_M5r
    a1_M5r a2_M5r a3_M5r a4_M5r p1_M5r cs_M5r
    file1_M5r file2_M5r file3_M5r file4_M5r parmAt_M5r clkAt_M5r
    rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨v, s, hruns, hc⟩ := of_checkRunMK check_M5r_eq
  have hab1 : getAbended_M5r (.normal v s) = some 1 := beq_iff_eq.1 hc
  obtain ⟨_, hmatch⟩ := hsim hsafe
  obtain ⟨os, hos, hrel⟩ := hmatch (.normal v s) hruns
  have hrelAb := getAbended_of_rel_M5r hrel
  have habC := (habFn os hos).trans hab0_M5r
  rw [habC, hab1] at hrelAb
  revert hrelAb; decide

end M5r

end EquivLean.Modernize.MutantRefutations

#print axioms EquivLean.Modernize.MutantRefutations.mut_J4_not_statement
#print axioms EquivLean.Modernize.MutantRefutations.mut_M2_not_statement
#print axioms EquivLean.Modernize.MutantRefutations.mut_M5r_not_statement
