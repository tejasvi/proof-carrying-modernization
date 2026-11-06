/-
# RECSUM: a batch program over an input file of any length ≡ a Java loop

`examples/recsum/RECSUM.cob` reads amount records until end of file
(`PERFORM 2000-PROCESS UNTIL EOF`), keeps a running total, and writes one output record with
the running total per input record.  `RecSumJava.run` transcribes `RecSum.java` (a `for`
loop over the records with a `BigDecimal` total).

The loop runs once per input record, so it cannot be unrolled: `cobol_loop` replaces it by its
result, given a loop invariant relating the COBOL storage and output file to the Java state
after the records processed so far.  The theorem holds for every input file of up to 9999
records (beyond that, `WS-TOTAL PIC S9(9)V99` may overflow and COBOL truncates it silently,
while `BigDecimal` does not).
-/
import Cobol
open Cobol

cobol_program RecSum from "../examples/recsum/recsum.ir.json"

namespace RecSumJava
open Java

/-- `RecSum.run`: `(total, outputs)` after each input record `(id, amount)`. -/
def step (acc : BigDecimal × List (List UInt8 × BigDecimal)) (r : List UInt8 × BigDecimal) :
    BigDecimal × List (List UInt8 × BigDecimal) :=
  let t := acc.1.add r.2
  (t, acc.2 ++ [(r.1, t)])

def run (recs : List (List UInt8 × BigDecimal)) : List (List UInt8 × BigDecimal) :=
  (recs.foldl step (BigDecimal.valueOf 0 2, [])).2

end RecSumJava

open RecSum

/-- An input record: `IN-ID` bytes and the `IN-AMT` value (scale 2), as stored in the file. -/
def encIn (r : List UInt8 × Int) : List UInt8 := r.1 ++ encodeNum {} IN_AMT.fmt r.2

/-- An output record as written by COBOL / expected from the Java output. -/
def encOut (r : List UInt8 × Java.BigDecimal) : List UInt8 :=
  r.1 ++ encodeNum {} OUT_TOTAL.fmt (r.2.valueAt 2)

def toJava (r : List UInt8 × Int) : List UInt8 × Java.BigDecimal := (r.1, .valueOf r.2 2)

/-- The records written to `OUT-FILE`, oldest first. -/
def writes (st : State) : List (List UInt8) :=
  st.out.reverse.filterMap fun | .write 2 bs => some bs | _ => none

/-- The Java state after the records `done`. -/
def acc (done : List (List UInt8 × Int)) : Java.BigDecimal × List (List UInt8 × Java.BigDecimal) :=
  (done.map toJava).foldl RecSumJava.step (.valueOf 0 2, [])

theorem acc_append (done : List (List UInt8 × Int)) (y : List UInt8 × Int) :
    acc (done ++ [y]) = RecSumJava.step (acc done) (toJava y) := by
  simp [acc, List.foldl_append]

theorem acc_scale (done : List (List UInt8 × Int)) : (acc done).1.scale = 2 := by
  suffices ∀ (l : List (List UInt8 × Java.BigDecimal)) (a : Java.BigDecimal × _),
      (∀ r ∈ l, r.2.scale = 2) → a.1.scale = 2 → (l.foldl RecSumJava.step a).1.scale = 2 by
    exact this _ _ (by intro r hr; simp only [List.mem_map, toJava] at hr
                       obtain ⟨_, _, rfl⟩ := hr; rfl) rfl
  intro l
  induction l with
  | nil => intro a _ h; exact h
  | cons r l ih =>
    intro a hl ha
    apply ih _ (fun r' h' => hl r' (List.mem_cons_of_mem _ h'))
    simp [RecSumJava.step, Java.BigDecimal.add, ha, hl r (by simp)]

/-- The input file at the loop head, when `xs` remain to be processed: the first of them is
already in `IN-REC`. -/
def inpOf : List (List UInt8 × Int) → List (Nat × List (List UInt8))
  | [] => [(1, [])]
  | _ :: xs => [(1, xs.map encIn)]

/-- Loop invariant at the head of `PERFORM 2000-PROCESS UNTIL EOF`, with the records `xs` still
to process: the state is `(mem, no subscripts, no PERFORM active, any save areas, out, the
rest of the file)`, the storage holds the current record, end of file flag, total and count
of the records `done` already processed, and the output file holds the Java outputs for them. -/
def RecSumInv (recs : List (List UInt8 × Int)) (xs : List (List UInt8 × Int)) (st : State) : Prop :=
  ∃ done mem saves out, recs = done ++ xs ∧ st = ⟨mem, [], [], saves, [], out, inpOf xs, [], 0⟩ ∧
    mem.size = 28 ∧
    (match xs with
     | [] => mem.field WS_EOF = [0xE8]
     | x :: _ => mem.field IN_ID = x.1 ∧ decodeNum {} IN_AMT.fmt (mem.field IN_AMT) = some x.2 ∧
         mem.field WS_EOF = [0xD5]) ∧
    decodeNum {} WS_TOTAL.fmt (mem.field WS_TOTAL) = some (acc done).1.unscaled ∧
    (acc done).1.unscaled.natAbs ≤ done.length * 9999999 ∧
    decodeNum {} WS_COUNT.fmt (mem.field WS_COUNT) = some (done.length : Int) ∧
    writes ⟨mem, [], [], saves, [], out, inpOf xs, [], 0⟩ = (acc done).2.map encOut

theorem recsum_equiv (m : Mem) (hm : m.size = 28) (recs : List (List UInt8 × Int)) (n : Nat)
    (hrecs : ∀ r ∈ recs, r.1.length = 4 ∧ r.2.natAbs < 10000000)
    (hlen : recs.length ≤ 9999) (hn : recs.length < n) :
    let r := RecSum.run {} (n + 10) (RecSum.initState m [(1, recs.map encIn)])
    r.1 = .stop .goback ∧ writes r.2 = (RecSumJava.run (recs.map toJava)).map encOut := by
  intro r
  cases recs with
  | nil =>
    -- empty file: the first READ reaches end of file, the loop body never runs
    simp only [r]
    cobol_sym [hm, List.map_nil]
    cobol_loop (RecSumInv []) ([] : List (List UInt8 × Int))
    · obtain ⟨done, mem, saves, out, hd, rfl, -, -, -, -, -, hw⟩ := hloopInv
      simp only [List.append_nil] at hd
      subst hd
      cobol_sym
      simp only [writes] at hw ⊢
      simp [hw, RecSumJava.run, acc]
    · refine ⟨[], _, [], [], by simp, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        cobol_sym [java_eval, hm, writes, acc, List.reverse_nil, List.filterMap_nil,
          Int.natCast_zero, Int.natAbs_zero]
    · simp
    · rintro st ⟨done, mem, saves, out, -, rfl, -, heof, -⟩
      cobol_sym [heof]
    · rintro y ys st ⟨done, -, -, -, hrec, -⟩
      simp at hrec
  | cons x xs =>
    obtain ⟨hx1, hx2⟩ := hrecs x (by simp)
    simp only [r]
    cobol_sym [hm, encIn, hx1, List.length_append, length_encodeNum, List.map_cons]
    cobol_loop (RecSumInv (x :: xs)) (x :: xs)
    · -- after the loop: GOBACK; the output file is the Java output
      obtain ⟨done, mem, saves, out, hd, rfl, -, -, -, -, -, hw⟩ := hloopInv
      simp only [List.append_nil] at hd
      subst hd
      cobol_sym
      simp only [writes] at hw ⊢
      simp [hw, RecSumJava.run, acc]
    · -- before the loop: no record processed, the first one read
      refine ⟨[], _, [], [], by simp, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        cobol_sym [java_eval, hm, hx1, hx2, List.take_left', List.drop_left', List.take_of_length_le, writes, acc,
          List.reverse_nil, List.filterMap_nil, Int.natCast_zero, Int.natAbs_zero]
    · simp only [List.length_cons] at hn ⊢; omega
    · -- the loop ends exactly at end of file
      rintro st ⟨done, mem, saves, out, -, rfl, -, heof, -⟩
      cobol_sym [heof]
    · -- one iteration: process the current record, read the next one
      rintro y ys st ⟨done, mem, saves, out, hrec, rfl, hsize, ⟨hid, hamt, heof⟩, htot, hbnd, hcnt, hwr⟩
      have hy := hrecs y (by rw [hrec]; simp)
      have hL : done.length + 1 + ys.length ≤ 9999 := by
        have := congrArg List.length hrec; simp only [List.length_cons] at hlen; simp at this; omega
      have hsc := acc_scale done
      refine ⟨by cobol_sym [heof], ?_⟩
      cases ys with
      | nil =>
        cobol_sym [inpOf, hsize, hid, hamt, heof, htot, hcnt, encIn, hy.1, List.length_append,
          length_encodeNum, List.take_of_length_le]
        simp only [writes] at hwr
        refine ⟨done ++ [y], _, _, _, by simp [hrec], rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals cobol_sym [java_eval, hsize, heof, hy.1, List.take_left', List.drop_left',
          List.take_of_length_le, acc_append, RecSumJava.step, hsc, writes, encOut, toJava, hwr,
          List.reverse_cons, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
          List.map_append, List.length_append]
        all_goals simp only [List.length_nil] at hL
        all_goals cobol_grind
      | cons y' ys' =>
        have hy' := hrecs y' (by rw [hrec]; simp)
        cobol_sym [inpOf, hsize, hid, hamt, heof, htot, hcnt, encIn, hy.1, hy'.1,
          List.length_append, length_encodeNum, List.take_of_length_le]
        simp only [writes] at hwr
        refine ⟨done ++ [y], _, _, _, by simp [hrec], rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals cobol_sym [java_eval, hsize, heof, hy.1, hy'.1, hy'.2, List.take_left',
          List.drop_left', List.take_of_length_le, acc_append, RecSumJava.step, hsc, writes, encOut,
          toJava, hwr, List.reverse_cons, List.filterMap_append, List.filterMap_cons,
          List.filterMap_nil, List.map_append, List.length_append]
        all_goals simp only [List.length_cons] at hL
        all_goals cobol_grind

#print axioms recsum_equiv
