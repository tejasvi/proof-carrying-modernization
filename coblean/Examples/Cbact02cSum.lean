/-
# CBACT02C again, with a summary of `1000-CARDFILE-GET-NEXT`

The paragraph is proved once (`getNext_record`), for any program `P` that has the configuration
and files of CBACT02C (it performs nothing, so nothing else about `P` matters).
Registered as a `cobol_eval` lemma, symbolic execution uses it wherever the paragraph runs
(`cbact02c_lists'`) instead of executing its statements again. `perform_getNext_record` is the
same fact at the level of the `PERFORM` statement (`performOnce_para'`), for reasoning about
ranges.
-/
import Examples.Cbact02c
open Cobol

namespace CardDemo.Cbact02c

/-- The file state the paragraph reads from. -/
abbrev inFile (recs : List (List UInt8)) (pos : Nat) (c : Option Nat) : FileSt :=
  { mode := some .input, recs, pos, eof := false, cur := c }

/-- The storage after `1000-CARDFILE-GET-NEXT` read record `r`: record area, `CARD-RECORD`
(`INTO`), `CARDFILE-STATUS` `'00'`, `APPL-RESULT` 0 (writes in increasing offset order, the normal
form symbolic execution keeps). -/
abbrev getNextMem (m : Mem) (r : List UInt8) : Mem :=
  (((m.write 0 r).write 150 r).write 300 [240, 240]).write 310
    (encodeNum {} { digits := 9, signed := true, usage := .binary } 0)

/-- **Summary**: one successful `READ` of record `recs[pos]`. -/
theorem getNext_record (P : Program) (hcfg : P.cfg = Cbact02c.cfg) (hfiles : P.files = Cbact02c.files)
    (env : Env) (rec : Nat → State → Sem.Res) (fuel : Nat) (m : Mem) (hm : m.size = 323)
    (idx : List (Nat × Int)) (slots : List (ExitPt × Nat)) (saves : List (Nat × Nat))
    (active : List Nat) (out : List Event) (inp : List (Nat × List (List UInt8))) (clockN : Nat)
    (recs : List (List UInt8)) (pos : Nat) (c : Option Nat)
    (hr : recs[pos]?.isSome = true) (hrl : (recs[pos]?.getD []).length = 150) :
    Sem.execSentences P env rec fuel Cbact02c.«1000-CARDFILE-GET-NEXT».body
      ⟨m, idx, slots, saves, active, out, inp, [(1, inFile recs pos c)], clockN⟩ =
    (.normal, ⟨getNextMem m (recs[pos]?.getD []), idx, slots, saves, active, out, inp,
               [(1, { mode := some .input, recs, pos := pos + 1, cur := some pos })], clockN⟩) := by
  obtain ⟨r, hr'⟩ : ∃ r, recs[pos]? = some r := Option.isSome_iff_exists.mp hr
  simp only [hr', Option.getD_some] at hrl ⊢
  cobol_sym [hcfg, hfiles, hm, hr', hrl]

/-- `PERFORM 1000-CARDFILE-GET-NEXT` (statement `id`, paragraph 1) reading record `recs[pos]`. -/
theorem perform_getNext_record (P : Program) (hk : P.paras[1]? = some Cbact02c.«1000-CARDFILE-GET-NEXT»)
    (hcfg : P.cfg = Cbact02c.cfg) (hfiles : P.files = Cbact02c.files) (env : Env) (fuel id : Nat)
    (hf : fuel ≠ 0)
    (m : Mem) (hm : m.size = 323) (idx : List (Nat × Int)) (slots : List (ExitPt × Nat))
    (saves : List (Nat × Nat)) (active : List Nat) (out : List Event)
    (inp : List (Nat × List (List UInt8))) (clockN : Nat) (recs : List (List UInt8)) (pos : Nat)
    (c : Option Nat) (hr : recs[pos]?.isSome = true) (hrl : (recs[pos]?.getD []).length = 150)
    (hna : id ∉ active) :
    Sem.performOnce (Sem.runFrom P env fuel) id 1 (.para 1)
      ⟨m, idx, slots, saves, active, out, inp, [(1, inFile recs pos c)], clockN⟩ =
    (.normal, performExit id 1 ⟨m, idx, slots, saves, active, out, inp, [(1, inFile recs pos c)], clockN⟩
      ⟨getNextMem m (recs[pos]?.getD []), idx, Sem.setAssoc slots (.para 1) (some id),
        Sem.setAssoc saves id (slots.lookup (.para 1)), id :: active, out, inp,
        [(1, { mode := some .input, recs, pos := pos + 1, cur := some pos })], clockN⟩) := by
  apply performOnce_para' hf hk hna
  · exact getNext_record P hcfg hfiles env _ _ m hm idx _ _ _ out inp clockN recs pos c hr hrl
  · simp [Sem.setAssoc]

-- the summary is used by symbolic execution wherever the paragraph runs, ahead of executing
-- its statements (paragraph bodies are unfolded only when they run)
attribute [local cobol_eval high] getNext_record

/-- `cbact02c_lists`, with the loop step using the summary of `1000-CARDFILE-GET-NEXT`. -/
theorem cbact02c_lists' (m : Mem) (hm : m.size = 323) (recs : List (List UInt8)) (n : Nat)
    (hrecs : ∀ r ∈ recs, r.length = 150) (hn : recs.length < n) :
    let r := Cbact02c.run {} (n + 20) (Cbact02c.initState m [(1, recs)])
    r.1 = .stop .goback ∧ displays r.2 = [startMsg] ++ recs ++ [endMsg] := by
  intro r
  simp only [r]
  cobol_sym [hm]
  cobol_loop (Inv recs) (recs.map some ++ [none])
  · -- after the loop: CLOSE, DISPLAY, GOBACK
    obtain ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩ := loopState
    obtain ⟨done, todo, hd, rfl, rfl, rfl, rfl, rfl, rfl, ⟨c, rfl⟩, hsz, hcase⟩ := hloopInv
    obtain ⟨-, rfl, heof⟩ | ⟨h, -⟩ := hcase
    · simp only [List.append_nil] at hd
      subst hd
      cobol_sym [hsz, heof]
      simp [displays, startMsg, endMsg, List.filterMap_map, Function.comp_def]
    · simp at h
  · -- before the loop: nothing displayed but the start message, file at its start
    refine ⟨[], recs, by simp, rfl, rfl, rfl, rfl, by simp [startMsg], rfl, ⟨none, by simp⟩, ?_,
      Or.inr ⟨by simp, ?_⟩⟩ <;> cobol_sym [hm]
  · simp; omega
  · -- the loop ends exactly after the end-of-file READ
    rintro ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, -, rfl, rfl, rfl, rfl, rfl, rfl, ⟨c, rfl⟩, -, (⟨-, -, heof⟩ | ⟨h, -⟩)⟩
    · cobol_sym [heof]
    · simp at h
  · -- one iteration: READ the next record and DISPLAY it, or reach the end of the file
    rintro y ys ⟨mem, idx, slots, saves, active, out, inp, files, clockN⟩
      ⟨done, todo, hd, rfl, rfl, rfl, rfl, rfl, rfl, ⟨c, rfl⟩, hsz, (⟨h, -⟩ | ⟨hrest, heof⟩)⟩
    · simp at h
    cases todo with
    | nil =>
      simp at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      simp only [List.append_nil] at hd
      subst hd
      refine ⟨by cobol_sym [heof], ?_⟩
      cobol_sym [hsz, heof, getElem?_length_self]
      refine ⟨recs, [], by simp, rfl, rfl, rfl, rfl, rfl, rfl, ⟨none, by simp⟩, ?_,
        Or.inl ⟨rfl, rfl, ?_⟩⟩ <;> cobol_sym [hsz]
    | cons t todo' =>
      simp at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      subst hd
      have ht : t.length = 150 := hrecs t (by simp)
      refine ⟨by cobol_sym [heof], ?_⟩
      -- `PERFORM 1000-CARDFILE-GET-NEXT` by its summary, not by executing the paragraph
      cobol_sym [hsz, heof, ht, getElem?_append_length, performExit]
      refine ⟨done ++ [t], todo', by simp, rfl, rfl, rfl, rfl, by simp, rfl,
        ⟨some done.length, by simp⟩, ?_, Or.inr ⟨by simp, ?_⟩⟩ <;> cobol_sym [hsz, heof, ht]

#print axioms cbact02c_lists'

end CardDemo.Cbact02c
