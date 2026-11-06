/-
# PERFORM-range summaries

A paragraph is proved once and the result is used at every `PERFORM` of it, instead of
executing its statements again at each call site.

* A **summary** of paragraph `k` is an equation for running its sentences:
  `execSentences P env rec fuel para.body st = (.normal, F st)` for every state `st` satisfying
  a precondition, where `F` is an explicit function of the state (the paragraph's effect).  It
  is stated for an *abstract* program `P` with hypotheses on just what the paragraph needs
  (`P.paras[k]? = some para`, `P.cfg = …`, `P.files = …`; a paragraph without `PERFORM` /
  `GO TO` does not even use `rec` and `fuel`), so it does not depend on the rest of the program
  and survives edits of other paragraphs.  It is proved by symbolic execution on a state whose
  fields are variables.
* **Use**: register the summary with `attribute [local cobol_eval high] summary`. Paragraph
  bodies are unfolded only when they run (`P.«name».exec`), so symbolic execution meets
  `execSentences P env rec fuel P.«name».body st` wherever the paragraph runs (`PERFORM`, fall
  through, `GO TO`) and rewrites it with the summary instead of executing the statements.
  Side conditions must be dischargeable by simp.
* `performOnce_para` turns a summary into the result of `PERFORM k` (return slot set at entry,
  restored at exit, IBM semantics), for statements about ranges.
-/
import Cobol.Logic.Eval

namespace Cobol
open Sem

/-- The state in which `PERFORM` statement `id` enters paragraph `k`: the return slot of the
end of `k` is set to `id` (its previous value saved), `id` is active. -/
def performEntry (id k : Nat) (st : State) : State :=
  { st with slots := setAssoc st.slots (.para k) (some id),
            saves := setAssoc st.saves id (st.slots.lookup (.para k)),
            active := id :: st.active }

/-- The state after the end of paragraph `k` returns to `PERFORM` statement `id`, entered from
`st0`: the slot is restored from the save area. -/
def performExit (id k : Nat) (st0 st' : State) : State :=
  { st' with slots := setAssoc st'.slots (.para k) (st'.saves.lookup id), active := st0.active }

/-- `PERFORM k` (one paragraph) whose sentences end normally in `st'`, with the return slot of
`k` still holding `id` (always the case when the paragraph performs nothing itself). -/
theorem performOnce_para {P : Program} {env : Env} {n id k : Nat} {para : Paragraph}
    {st st' : State} (hk : P.paras[k]? = some para) (hna : st.active.contains id = false)
    (hbody : execSentences P env (runFrom P env n) n para.body (performEntry id k st) =
      (.normal, st'))
    (hslot : st'.slots.lookup (.para k) = some id) :
    performOnce (runFrom P env (n + 1)) id k (.para k) st = (.normal, performExit id k st st') := by
  have hb : execSentences P env (runFrom P env n) n para.body
      { st with slots := setAssoc st.slots (.para k) (some id),
                saves := setAssoc st.saves id (st.slots.lookup (.para k)),
                active := id :: st.active } = (.normal, st') := hbody
  simp only [performOnce, hna, Bool.false_eq_true, ↓reduceIte, runFrom, hk, hb, endOfPara, hslot]
  simp [performExit]

/-- `performOnce_para` with the fuel of the call site as it appears there (`n + 19`): simp's
index does not match a literal offset against `n + 1`, so summaries are stated with this form. -/
theorem performOnce_para' {P : Program} {env : Env} {fuel id k : Nat} {para : Paragraph}
    {st st' : State} (hf : fuel ≠ 0) (hk : P.paras[k]? = some para) (hna : id ∉ st.active)
    (hbody : execSentences P env (runFrom P env (fuel - 1)) (fuel - 1) para.body
      (performEntry id k st) = (.normal, st'))
    (hslot : st'.slots.lookup (.para k) = some id) :
    performOnce (runFrom P env fuel) id k (.para k) st = (.normal, performExit id k st st') := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  exact performOnce_para hk (by simpa using hna) hbody hslot

attribute [cobol_eval] Nat.add_eq_zero_iff List.not_mem_nil List.mem_cons

/-- The slots after a paragraph that leaves them unchanged: the entry slot is still there. -/
theorem performEntry_slot (id k : Nat) (st : State) :
    (performEntry id k st).slots.lookup (.para k) = some id := by
  simp [performEntry, setAssoc, List.lookup]

end Cobol
