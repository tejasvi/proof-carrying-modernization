import EquivLean.Modernize.Cbstm03a.Java.Run2.Close
import EquivLean.Modernize.Cbstm03a.Java.Run2.Cut
import EquivLean.Modernize.Cbstm03a.Java.Run2.Ld

/-!
# CBSTM03A → Java `run`, the load loop: the assertions of the extra cut points

The paths from statement 80 are cut before every call whose contract reads the heap of its argument objects
(the executor matches those premises against hypotheses about the call's own entry state): 88 (`setTrct`, a new
card), 92 (`label21`, then `memWrite` of the card number), 95 and 98 (the other two `memWrite`s), 100 (`seqRead`),
113 (`setTrct`, the last card). Each assertion holds the loop head's frame facts folded (`FrameK`) and, unfolded,
what the next statements read. `LP` bundles the loop head's values.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText space GrowsK Kept)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

/-- The values fixed at the loop head: its frame and state, the arrays, record `k` (`rec`) and the load state
`s`; `y` a string object with text `ty` (the next record's text when there is one). -/
structure LP where
  fr : Frame
  σ : State
  mem : Addr
  trct : Addr
  st1 : Addr
  t1 : Addr
  y : Addr
  xs : List Value
  k : Nat
  ty : JStr
  s : LdSt
  r : JStr
  /-- `p.k + 1` is the last record (`False` when records remain). -/
  fin : Prop

/-- The loop head's frame facts. -/
def FrameK (p : LP) (fr' : Frame) (σ' : State) : Prop :=
  Kept (Keeps (Upd3 p.mem p.trct p.st1) p.σ σ' ∧ σ'.inits = p.σ.inits ∧ σ'.statics = p.σ.statics ∧
    SameLocs p.fr fr')

/-- The objects every later statement of the loop body reads. -/
def MidBase (p : LP) (fr' : Frame) (σ' : State) : Prop :=
  FrameK p fr' σ' ∧ σ'.initOf "Cbstm03a" = .done ∧
    fr'.get 11 = some (.ref p.t1) ∧ σ'.heap p.t1 = some (.array (.cls "java.lang.String") p.xs) ∧
    fr'.get 16 = some (.ref p.mem) ∧ fr'.get 24 = some (.ref p.trct) ∧ fr'.get 1 = some (.ref p.st1) ∧
    σ'.heap p.st1 = some (.array (.prim .int) [.int (BitVec.ofNat 32 (p.k + 1)), .int 0]) ∧
    σ'.heap p.y = some (.str p.ty) ∧ ∃ vsm, σ'.heap p.mem = some (.array (.cls "java.lang.String") vsm)

/-- The three fields of record `rec` in `trest` (36), `xrefCustId` (34), `cn` (33). -/
def RecLocs (p : LP) (fr' : Frame) (σ' : State) : Prop :=
  ∃ xc xi xr, fr'.get 36 = some (.ref xc) ∧ σ'.heap xc = some (.str (sub p.r 0 16)) ∧
    fr'.get 34 = some (.ref xi) ∧ σ'.heap xi = some (.str (sub p.r 16 32)) ∧
    fr'.get 33 = some (.ref xr) ∧ σ'.heap xr = some (.str (sub p.r 32 350))

/-- The table memory `m`, the counts array and the counters of `L`. -/
def TabAt (p : LP) (m : Nat → JChar) (L : LdSt) (fr' : Frame) (σ' : State) : Prop :=
  SlotsAt σ' p.mem m ∧ σ'.heap p.trct = some (.array (.prim .long) L.trct) ∧
    fr'.get 18 = some (.long L.cr) ∧ fr'.get 17 = some (.long L.tr)

/-- The load step of the loop body. -/
abbrev LP.L (p : LP) : LdSt := ldStep p.s p.r

/-- The memory after the first and the second write. -/
def LP.m95 (p : LP) : Nat → JChar := memWr p.s.m (cardOffJ p.L.cr).toInt (sub p.r 0 16)
def LP.m98 (p : LP) : Nat → JChar := memWr p.m95 (tranOffJ p.L.cr p.L.tr).toInt (sub p.r 16 32)

def A88 (p : LP) : Frame → State → Prop := fun fr' σ' =>
  MidBase p fr' σ' ∧ RecLocs p fr' σ' ∧ TabAt p p.s.m p.s fr' σ' ∧ p.s.trct.length = 51

def A92 (p : LP) : Frame → State → Prop := fun fr' σ' =>
  MidBase p fr' σ' ∧ RecLocs p fr' σ' ∧ TabAt p p.s.m p.L fr' σ'

def A95 (p : LP) : Frame → State → Prop := fun fr' σ' =>
  MidBase p fr' σ' ∧ RecLocs p fr' σ' ∧ TabAt p p.m95 p.L fr' σ' ∧
    fr'.get 19 = some (.long (tranOffJ p.L.cr p.L.tr))

def A98 (p : LP) : Frame → State → Prop := fun fr' σ' =>
  MidBase p fr' σ' ∧ RecLocs p fr' σ' ∧ TabAt p p.m98 p.L fr' σ' ∧
    fr'.get 19 = some (.long (tranOffJ p.L.cr p.L.tr + 16))

def A100 (p : LP) : Frame → State → Prop := fun fr' σ' =>
  MidBase p fr' σ' ∧ TabAt p p.L.m p.L fr' σ' ∧
    ∃ xc, fr'.get 32 = some (.ref xc) ∧ σ'.heap xc = some (.str (sub p.r 0 16))

def A113 (p : LP) : Frame → State → Prop := fun fr' σ' =>
  FrameK p fr' σ' ∧ σ'.initOf "Cbstm03a" = .done ∧ fr'.get 16 = some (.ref p.mem) ∧
    fr'.get 24 = some (.ref p.trct) ∧ TabAt p p.L.m p.L fr' σ' ∧ p.fin

/-- The cut lists, innermost first. -/
def cuts0 (g : RunG) (args : List Value) (σ0 : State) : Cuts := (runInv g).inst args σ0
def cuts113 (g : RunG) (args : List Value) (σ0 : State) (p : LP) : Cuts := (113, A113 p) :: cuts0 g args σ0
def cuts100 (g : RunG) (args : List Value) (σ0 : State) (p : LP) : Cuts := (100, A100 p) :: cuts113 g args σ0 p
def cuts98 (g : RunG) (args : List Value) (σ0 : State) (p : LP) : Cuts := (98, A98 p) :: cuts100 g args σ0 p
def cuts95 (g : RunG) (args : List Value) (σ0 : State) (p : LP) : Cuts := (95, A95 p) :: cuts98 g args σ0 p
def cuts92 (g : RunG) (args : List Value) (σ0 : State) (p : LP) : Cuts := (92, A92 p) :: cuts95 g args σ0 p
def cuts88 (g : RunG) (args : List Value) (σ0 : State) (p : LP) : Cuts := (88, A88 p) :: cuts92 g args σ0 p

/-- `run`'s paths from `pc` with the cut list `I` (fuel `n`). -/
abbrev segWP (g : RunG) (args : List Value) (σ0 : State) (I : Cuts) (n pc : Nat) (fr : Frame) (σ : State) :
    Prop :=
  bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA I ((runSpecG g).post args σ0) n pc fr σ

end EquivLean.Modernize.Cbstm03a.Java.Seg2
