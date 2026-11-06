/-
  Examples/CardDemo/Cbact02cRun.lean

  `Cbact02c.run(CardRecord[])`, the read loop of CBACT02C as translated to Java: the list
  `displays` of the result holds the start line, the line of each record (`formatCard`) in
  order and the end line, and `abended` stays `false`. Against the contracts of `formatCard`
  and `spaces`; one loop invariant, at the head of the read loop (statement 32).
-/
import Examples.CardDemo.Cbact02cFormat

open Jimple

namespace Examples.CardDemo

def startText : JStr := JStr.ofString "START OF EXECUTION OF PROGRAM CBACT02C"
def endText : JStr := JStr.ofString "END OF EXECUTION OF PROGRAM CBACT02C"
def textN : JStr := JStr.ofString "N"
def textY : JStr := JStr.ofString "Y"

/-- The line of the record a value refers to. -/
def recLineV (σ : State) : Value → JStr
  | .ref c => cardLine σ c
  | _ => []

/-- The lines of the first `n` records. -/
def cardLines (σ : State) (xs : List Value) : Nat → List JStr
  | 0 => []
  | n + 1 => cardLines σ xs n ++ [recLineV σ (xs.getD n .null)]

theorem cardLines_eq_map (σ : State) (xs : List Value) :
    ∀ n, n ≤ xs.length → cardLines σ xs n = (xs.take n).map (recLineV σ)
  | 0, _ => by simp [cardLines]
  | n + 1, h => by
    have hn : n < xs.length := by omega
    rw [cardLines, cardLines_eq_map σ xs n (by omega), List.take_succ, List.getElem?_eq_getElem hn,
      List.map_append]
    simp only [Option.toList_some, List.map_cons, List.map_nil, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hn, Option.getD_some]

/-- All the lines: one per record. -/
theorem cardLines_length (σ : State) (xs : List Value) :
    cardLines σ xs xs.length = xs.map (recLineV σ) := by
  rw [cardLines_eq_map σ xs _ (Nat.le_refl _), List.take_length]

abbrev runRef : MethodRef := CB.Cbact02c.«run(Cbact02c$CardRecord[])».ref

/-- The contract of `run`: an array of records as `formatCard` reads them (`CardOk`). -/
def runSpecJ : Spec := Spec.of
  (fun args σ => ∃ a et xs, args = [.ref a] ∧ σ.heap a = some (.array et xs) ∧
     xs.length < 2147483648 ∧ (∀ v ∈ xs, ∃ c, v = .ref c ∧ CardOk σ c) ∧
     σ.initOf "Cbact02c" = .done ∧ σ.initOf "Cbact02c$Result" = .done ∧
     σ.initOf "Cbact02c$CardRecord" = .done)
  (fun args σ r σ' => ∀ a et xs, args = [.ref a] → σ.heap a = some (.array et xs) →
     ∃ res fs l k ys m, r = some (.ref res) ∧ σ'.heap res = some (.plain "Cbact02c$Result" fs) ∧
       Fields.get fs ("Cbact02c$Result", "displays") = some (.ref l) ∧
       σ'.heap l = some (.list k ys m) ∧
       StrsAt σ' ys (startText :: (cardLines σ xs xs.length ++ [endText])) ∧
       Fields.get fs ("Cbact02c$Result", "abended") = some (.int 0))

/-- The facts at the head of the read loop (statement 32), for given values of the invariant's
    variables: `i` records read, their lines displayed after the start line; the end-of-file flag
    `z` (local `$z0`) is set exactly when the flag string `$r5` is `"Y"`, and then all records
    have been read. Locals: `$r1` 0, `r0` 6, `i6` 7, `$i7` 8, `$r5` 9, `$z0` 15. -/
def RunAt (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (xs : List Value) (res : Addr)
    (fs : List (FieldKey × Value)) (l : Addr) (ys : List Value) (m : Nat)
    (i n : I32) (r5 : Addr) (z : I32) : Prop :=
  fr.get 6 = some (.ref a) ∧ fr.get 0 = some (.ref res) ∧
  σ.heap res = some (.plain "Cbact02c$Result" fs) ∧
  Fields.get fs ("Cbact02c$Result", "displays") = some (.ref l) ∧
  Fields.get fs ("Cbact02c$Result", "abended") = some (.int 0) ∧
  σ.heap l = some (.list .arrayList ys m) ∧
  StrsAt σ ys (startText :: cardLines σ0 xs i.toInt.toNat) ∧
  fr.get 7 = some (.int i) ∧ fr.get 8 = some (.int n) ∧ n.toInt = xs.length ∧
  0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧
  fr.get 9 = some (.ref r5) ∧ σ.heap r5 = some (.str (if z = 0 then textN else textY)) ∧
  fr.get 15 = some (.int z) ∧ (z ≠ 0 → i.toInt = n.toInt) ∧
  σ0.next ≤ res ∧ res < l ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics

/-- The loop invariant of `run`. -/
def runInv32 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ a et xs, args = [.ref a] → σ0.heap a = some (.array et xs) →
    ∃ res fs l ys m i n r5 z, RunAt σ0 fr σ a xs res fs l ys m i n r5 z

def runInv : Invariants := [(32, runInv32)]

def formatCardSig : MethodSig :=
  ⟨"Cbact02c", .cls "java.lang.String", "formatCard", [.cls "Cbact02c$CardRecord"]⟩
def spacesSig : MethodSig := ⟨"Cbact02c", .cls "java.lang.String", "spaces", [.prim .int]⟩

/-- The callee contracts of `run`. -/
def runCallees : Contracts := [(formatCardSig, formatCardSpec), (spacesSig, spacesSpec)]

/-- The paths of `run` from statement `pc` with frame `fr` and state `σ` (entry arguments `args`,
    entry state `σ0`): the verification conditions of `run_vc`, one lemma per segment
    (`Cbact02cRunEntry`, `Cbact02cRunLoop*`), checked in parallel. -/
def runWP (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP CB.prog (callWP CB.prog runCallees.env 1) CB.Cbact02c.«run(Cbact02c$CardRecord[])»
    (runInv.inst args σ0) (runSpecJ.post args σ0) 200 pc fr σ

end Examples.CardDemo

