import EquivLean.Modernize.Cbtrn03c.JavaTop.Pe

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `run`, definitions

`run(transactFile, xrefFile, trantypeFile, trancatgFile, dateParmsFile)` is `Model.run`.  The
loop head (statement 35) carries the model state `s` of the `Ws` object and the record area
`tv` (the object at `r22`); with `eof` clear, the remaining computation
`fin (Model.loop xs ys cs d (trans.drop i) tv s)` is the run's outcome; with `eof` set, the
outcome is `Model.out s false`.  `processDetail` (statement 52) and `processEnd` (statement 56)
are called at cuts of their own (their contracts' premises are then hypotheses of the call's
state); statement 53 is the cut after `processDetail`.

Locals: `$r5` (the `Result`) 0, `$i0` (records read) 1, `r2` 6, `$z0` 7, `z2` 8, `z3` 9, `r22`
(the record area) 10, `$r6` (the `Ws` object) 11, `r4` 12, `r1` 13, `r0` 14, `r3` 16.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

/-- The date record of the run (the record area's spaces when the file is empty: the loop does
not run then, and `ws.startDate`, `ws.endDate` hold spaces). -/
def d0 : List EquivLean.Cobol.Rec.FVal := [.str (Model.sp 10), .str (Model.sp 1), .str (Model.sp 10)]
def dOf (vals5 : List (List EquivLean.Cobol.Rec.FVal)) : List EquivLean.Cobol.Rec.FVal :=
  vals5.headD d0

/-- The outputs of a loop's result. -/
def fin : Except Model.St Model.St → Model.Out
  | .ok s => Model.out s false
  | .error s => Model.out s true

/-- The `Result` object at `res` with the lists `ld`, `lr`, `abended` clear. -/
def ResAt (σ : State) (res ld lr : Addr) : Prop :=
  ∃ fs, σ.heap res = some (.plain resC fs) ∧ Fields.get fs (resC, "displays") = some (.ref ld) ∧
    Fields.get fs (resC, "reportFileWrites") = some (.ref lr) ∧
    Fields.get fs (resC, "abended") = some (.int 0)

theorem ResAt.keeps {σ σ' : State} {res ld lr : Addr} (h : ResAt σ res ld lr)
    (hk : KeepsNonWs σ σ') : ResAt σ' res ld lr := by
  obtain ⟨fs, h1, h2, h3, h4⟩ := h
  exact ⟨fs, hk.2.2.1 res resC fs h1 (by decide), h2, h3, h4⟩

theorem ResAt.agree {σ σ' : State} {res ld lr : Addr} (h : ResAt σ res ld lr)
    (ha : Agree σ σ') : ResAt σ' res ld lr := by
  obtain ⟨fs, h1, h2, h3, h4⟩ := h
  exact ⟨fs, heap_agree ha h1, h2, h3, h4⟩

attribute [jframe] ResAt.keeps ResAt.agree

abbrev runBody : Body :=
  Gen.Cbtrn03c.«run(Cbtrn03c$TranRecord[],Cbtrn03c$CardXrefRecord[],Cbtrn03c$TranTypeRecord[],Cbtrn03c$TranCatRecord[],Cbtrn03c$WsDateparmRecord[])»

/-- The inputs of `run`, as the generated statement's `RunIn` for given addresses. -/
def RunFiles (σ : State) (a1 a2 a3 a4 a5 : Addr)
    (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal)) : Prop :=
  TransactFileAt σ a1 vals1 ∧ XrefFileAt σ a2 vals2 ∧ TrantypeFileAt σ a3 vals3 ∧
    TrancatgFileAt σ a4 vals4 ∧ DateParmsFileAt σ a5 vals5

/-- The validity of the input records (no state). -/
def RunValid (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal)) : Prop :=
  (∀ v ∈ vals1, TranRecord.Valid v) ∧ (∀ v ∈ vals2, CardXrefRecord.Valid v) ∧
    (∀ v ∈ vals3, TranTypeRecord.Valid v) ∧ (∀ v ∈ vals4, TranCatRecord.Valid v) ∧
    (∀ v ∈ vals5, WsDateparmRecord.Valid v)

/-- The classes initialized (the statement's `ClinitRan` and the record classes). -/
def RunInits (σ : State) : Prop :=
  σ.initOf "Cbtrn03c" = .done ∧ σ.initOf resC = .done ∧ σ.initOf wsC = .done ∧
    σ.initOf tranC = .done ∧ σ.initOf "Cbtrn03c$CardXrefRecord" = .done ∧
    σ.initOf "Cbtrn03c$TranTypeRecord" = .done ∧ σ.initOf "Cbtrn03c$TranCatRecord" = .done ∧
    σ.initOf "Cbtrn03c$WsDateparmRecord" = .done ∧ σ.initOf fdC = .done

/-- `Model.run`'s outputs are those of the final state `sf` (`ab`: abended).  Folded, so that the
symbolic execution takes the witnesses `sf`, `ab` of `runSpecG`'s postcondition from a hypothesis
instead of splitting the equation of outputs. -/
@[irreducible] def RunIs (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (sf : Model.St) (ab : Bool) : Prop :=
  Model.run vals1 vals2 vals3 vals4 vals5 = Model.out sf ab

theorem RunIs.eq {vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal)}
    {sf : Model.St} {ab : Bool} (h : RunIs vals1 vals2 vals3 vals4 vals5 sf ab) :
    Model.run vals1 vals2 vals3 vals4 vals5 = Model.out sf ab := by
  unfold RunIs at h; exact h

theorem RunIs.intro {vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal)}
    {sf : Model.St} {ab : Bool} (h : Model.run vals1 vals2 vals3 vals4 vals5 = Model.out sf ab) :
    RunIs vals1 vals2 vals3 vals4 vals5 sf ab := by
  unfold RunIs; exact h

/-- `run` for given inputs: the outputs of `Model.run` (displays and report lines as the strings
and records of the result's lists). -/
def runSpecG (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal)) :
    Spec := Spec.of
  (fun args σ => args = [.ref a1, .ref a2, .ref a3, .ref a4, .ref a5] ∧
     RunFiles σ a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 ∧
     RunValid vals1 vals2 vals3 vals4 vals5 ∧ RunInits σ)
  (fun _ _ r σ' => ∃ sf ab, RunIs vals1 vals2 vals3 vals4 vals5 sf ab ∧
     ∃ res fs l k xs mods lw kw ws mw, r = some (.ref res) ∧
       σ'.heap res = some (.plain resC fs) ∧ Fields.get fs (resC, "displays") = some (.ref l) ∧
       σ'.heap l = some (.list k xs mods) ∧ StrsAt σ' xs ((Model.out sf ab).disp.map jline) ∧
       Fields.get fs (resC, "reportFileWrites") = some (.ref lw) ∧
       σ'.heap lw = some (.list kw ws mw) ∧ RecsAt σ' ws (sf.writes.map recLine) ∧
       Fields.get fs (resC, "abended") = some (.int (if ab then 1 else 0)))

/-- The facts at the loop head (statement 35) for given values of its variables. -/
def RunAt (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State) (res ld lr w tr : Addr) (i z : I32) (s : Model.St)
    (tv : List EquivLean.Cobol.Rec.FVal) : Prop :=
  fr.get 0 = some (.ref res) ∧ fr.get 1 = some (.int i) ∧ fr.get 8 = some (.int z) ∧
  fr.get 9 = some (.int z) ∧ fr.get 10 = some (.ref tr) ∧ fr.get 11 = some (.ref w) ∧
  fr.get 14 = some (.ref a1) ∧ fr.get 13 = some (.ref a2) ∧ fr.get 6 = some (.ref a3) ∧
  fr.get 16 = some (.ref a4) ∧ fr.get 12 = some (.ref a5) ∧
  ResAt σ res ld lr ∧ WsRel σ w ld lr (dOf vals5) s ∧ TranFields σ tr tv ∧ TranRecord.Valid tv ∧
  RunFiles σ a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 ∧
  KeepsNonWs σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
  0 ≤ i.toInt ∧ i.toInt ≤ vals1.length ∧
  (z = 0 → vals5 ≠ [] ∧
    fin (Model.loop vals2 vals3 vals4 (dOf vals5) (vals1.drop i.toInt.toNat) tv s) =
      Model.run vals1 vals2 vals3 vals4 vals5) ∧
  (z ≠ 0 → RunIs vals1 vals2 vals3 vals4 vals5 s false)

/-- `RunAt` without the record area's object (the read segments replace it: the new record may be
the same object, and its facts would only be split on). -/
def RunAtR (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State) (res ld lr w : Addr) (i z : I32) (s : Model.St)
    (tv : List EquivLean.Cobol.Rec.FVal) : Prop :=
  fr.get 0 = some (.ref res) ∧ fr.get 1 = some (.int i) ∧ fr.get 8 = some (.int z) ∧
  fr.get 9 = some (.int z) ∧ fr.get 11 = some (.ref w) ∧
  fr.get 14 = some (.ref a1) ∧ fr.get 13 = some (.ref a2) ∧ fr.get 6 = some (.ref a3) ∧
  fr.get 16 = some (.ref a4) ∧ fr.get 12 = some (.ref a5) ∧
  ResAt σ res ld lr ∧ WsRel σ w ld lr (dOf vals5) s ∧
  RunFiles σ a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 ∧
  KeepsNonWs σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
  0 ≤ i.toInt ∧ i.toInt ≤ vals1.length ∧
  (z = 0 → vals5 ≠ [] ∧
    fin (Model.loop vals2 vals3 vals4 (dOf vals5) (vals1.drop i.toInt.toNat) tv s) =
      Model.run vals1 vals2 vals3 vals4 vals5) ∧
  (z ≠ 0 → RunIs vals1 vals2 vals3 vals4 vals5 s false)

theorem RunAt.toR {a1 a2 a3 a4 a5 : Addr} {vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal)}
    {σ0 : State} {fr : Frame} {σ : State} {res ld lr w tr : Addr} {i z : I32} {s : Model.St}
    {tv : List EquivLean.Cobol.Rec.FVal}
    (h : RunAt a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 σ0 fr σ res ld lr w tr i z s tv) :
    RunAtR a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 σ0 fr σ res ld lr w i z s tv := by
  obtain ⟨h0, h1, h8, h9, _, h11, h14, h13, h6, h16, h12, hres, hws, _, _, hf, hk, hin, hst, hi0, hi1,
    hz0, hz1⟩ := h
  exact ⟨h0, h1, h8, h9, h11, h14, h13, h6, h16, h12, hres, hws, hf, hk, hin, hst, hi0, hi1, hz0, hz1⟩

/-- What `run` has left after `processDetail` returns on transaction `t` (the `i` records read,
the step from the state `s`). -/
def afterStep (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal))
    (d : List EquivLean.Cobol.Rec.FVal) (i : Nat) (t : List EquivLean.Cobol.Rec.FVal) (s : Model.St) :
    Model.Out :=
  match Model.tranStep vals2 vals3 vals4 d s t with
  | .ok s' => fin (Model.loop vals2 vals3 vals4 d (vals1.drop i) t s')
  | .error s' => Model.out s' true

/-- The facts at the call of `processDetail` (statement 52): `RunAt`'s, `eof` clear, the record
`t` of the `i`-th transaction in the date range. -/
def RunAt52 (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State) (res ld lr w tr : Addr) (i : I32) (s : Model.St)
    (t : List EquivLean.Cobol.Rec.FVal) : Prop :=
  fr.get 0 = some (.ref res) ∧ fr.get 1 = some (.int i) ∧ fr.get 8 = some (.int 0) ∧
  fr.get 9 = some (.int 0) ∧ fr.get 10 = some (.ref tr) ∧ fr.get 11 = some (.ref w) ∧
  fr.get 14 = some (.ref a1) ∧ fr.get 13 = some (.ref a2) ∧ fr.get 6 = some (.ref a3) ∧
  fr.get 16 = some (.ref a4) ∧ fr.get 12 = some (.ref a5) ∧
  ResAt σ res ld lr ∧ WsRel σ w ld lr (dOf vals5) s ∧ TranFields σ tr t ∧ TranRecord.Valid t ∧
  RunFiles σ a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 ∧
  KeepsNonWs σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
  1 ≤ i.toInt ∧ i.toInt ≤ vals1.length ∧ vals5 ≠ [] ∧
  afterStep vals1 vals2 vals3 vals4 (dOf vals5) i.toInt.toNat t s =
    Model.run vals1 vals2 vals3 vals4 vals5

/-- The facts after `processDetail` returns (statement 53): `$z0` its result. -/
def RunAt53 (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State) (res ld lr w tr : Addr) (i : I32) (s : Model.St)
    (t : List EquivLean.Cobol.Rec.FVal) : Prop :=
  fr.get 0 = some (.ref res) ∧ fr.get 1 = some (.int i) ∧ fr.get 8 = some (.int 0) ∧
  fr.get 9 = some (.int 0) ∧ fr.get 10 = some (.ref tr) ∧ fr.get 11 = some (.ref w) ∧
  fr.get 14 = some (.ref a1) ∧ fr.get 13 = some (.ref a2) ∧ fr.get 6 = some (.ref a3) ∧
  fr.get 16 = some (.ref a4) ∧ fr.get 12 = some (.ref a5) ∧
  fr.get 7 = some (.int (if okB (Model.tranStep vals2 vals3 vals4 (dOf vals5) s t) then 0 else 1)) ∧
  ResAt σ res ld lr ∧
  WsRel σ w ld lr (dOf vals5) (stOf (Model.tranStep vals2 vals3 vals4 (dOf vals5) s t)) ∧
  TranFields σ tr t ∧ TranRecord.Valid t ∧
  RunFiles σ a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 ∧
  KeepsNonWs σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
  1 ≤ i.toInt ∧ i.toInt ≤ vals1.length ∧ vals5 ≠ [] ∧
  afterStep vals1 vals2 vals3 vals4 (dOf vals5) i.toInt.toNat t s =
    Model.run vals1 vals2 vals3 vals4 vals5

/-- The facts at the call of `processEnd` (statement 56): every record read, the record area
`tv` in the date range; the outcome is the last step's. -/
def RunAt56 (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State) (res ld lr w tr : Addr) (i : I32) (s : Model.St)
    (tv : List EquivLean.Cobol.Rec.FVal) : Prop :=
  fr.get 0 = some (.ref res) ∧ fr.get 1 = some (.int i) ∧ fr.get 8 = some (.int 1) ∧
  fr.get 9 = some (.int 1) ∧ fr.get 10 = some (.ref tr) ∧ fr.get 11 = some (.ref w) ∧
  fr.get 14 = some (.ref a1) ∧ fr.get 13 = some (.ref a2) ∧ fr.get 6 = some (.ref a3) ∧
  fr.get 16 = some (.ref a4) ∧ fr.get 12 = some (.ref a5) ∧
  ResAt σ res ld lr ∧ WsRel σ w ld lr (dOf vals5) s ∧ TranFields σ tr tv ∧ TranRecord.Valid tv ∧
  RunFiles σ a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 ∧
  KeepsNonWs σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
  0 ≤ i.toInt ∧ i.toInt ≤ vals1.length ∧
  RunIs vals1 vals2 vals3 vals4 vals5 (Model.eofTail s tv) false

/-- The model state after the entry: the start line, and the date range line when there is a
date record. -/
def sEntry : List (List EquivLean.Cobol.Rec.FVal) → Model.St
  | [] => Model.init
  | d :: _ => Model.dsp Model.init
      (Model.txt "Reporting from " ++ Model.cps (Model.dStart d) ++ Model.txt " to " ++
        Model.cps (Model.dEnd d))

/-- The facts at statement 34 (before `$i0 = 0`): the entry's state, `eof` set exactly when there
is no date record, the record area blank. -/
def RunAt34 (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State) (res ld lr w tr : Addr) (z : I32) : Prop :=
  fr.get 0 = some (.ref res) ∧ fr.get 8 = some (.int z) ∧ fr.get 9 = some (.int z) ∧
  fr.get 10 = some (.ref tr) ∧ fr.get 11 = some (.ref w) ∧
  fr.get 14 = some (.ref a1) ∧ fr.get 13 = some (.ref a2) ∧ fr.get 6 = some (.ref a3) ∧
  fr.get 16 = some (.ref a4) ∧ fr.get 12 = some (.ref a5) ∧
  ResAt σ res ld lr ∧ WsRel σ w ld lr (dOf vals5) (sEntry vals5) ∧ TranFields σ tr Model.tran0 ∧
  RunFiles σ a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 ∧
  KeepsNonWs σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
  z = (if vals5 = [] then 1 else 0)

def runInv (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal)) :
    Invariants :=
  [(34, fun _ σ0 fr σ => ∃ res ld lr w tr z,
      RunAt34 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 σ0 fr σ res ld lr w tr z),
   (35, fun _ σ0 fr σ => ∃ res ld lr w tr i z s tv,
      RunAt a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 σ0 fr σ res ld lr w tr i z s tv),
   (52, fun _ σ0 fr σ => ∃ res ld lr w tr i s t,
      RunAt52 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 σ0 fr σ res ld lr w tr i s t),
   (53, fun _ σ0 fr σ => ∃ res ld lr w tr i s t,
      RunAt53 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 σ0 fr σ res ld lr w tr i s t),
   (56, fun _ σ0 fr σ => ∃ res ld lr w tr i s tv,
      RunAt56 a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5 σ0 fr σ res ld lr w tr i s tv)]

end EquivLean.Modernize.Cbtrn03c.Java.Top
