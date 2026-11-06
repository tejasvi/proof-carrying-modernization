import EquivLean.Modernize.Cbstm03a.Java.Mw.Defs

/-!
# CBSTM03A → Java: `memWrite`, the virtual cut points of a slot write

A slot write from the loop head (`0 ≤ o = off + pos = J < MEM_SZ`, slot `i` of `J`, `W = J - slotStart(i)`) is cut at
statement 14 (`label2`, after `o cmp 0`: `A14`, `o` a variable again), 22 (`take = len - within`: `A22`), 26
(`cur = slots[idx]`, after `take = min(len - within, n - pos)`: `A26`) and 30 (`cur = cur#7.substring(0, within)`,
the slot's text `c` in `cur#7`: `A30`). Each cut gives the values the path computed as variables with their
`toInt`s, so that the symbolic executor never meets the compound machine words of the earlier statements;
`ValI` keeps a computed value's `toInt` folded until a closer proves it.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Mw

/-- `v.toInt = z`, folded across the symbolic executor. -/
@[irreducible] def ValI (v : I32) (z : Int) : Prop := v.toInt = z

theorem valI_elim {v : I32} {z : Int} (h : ValI v z) : v.toInt = z := by unfold ValI at h; exact h

theorem valI_intro {v : I32} {z : Int} (h : v.toInt = z) : ValI v z := by unfold ValI; exact h

/-- Statement 14 (`label2`): `o = off + pos = J`. -/
def A14 (σ : State) (a : Addr) (off : I64) (x : Addr) (pos n : I32) (J : Nat) (fr : Frame) (σ' : State) : Prop :=
  σ' = σ ∧ fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧ fr.get 5 = some (.int n) ∧
  fr.get 10 = some (.int pos) ∧ fr.get 12 = some (.ref x) ∧
  ∃ o : I64, fr.get 2 = some (.long o) ∧ o.toInt = J

/-- Statement 22: `idx`, `len`, `within` computed. -/
def A22 (σ : State) (a : Addr) (off : I64) (x : Addr) (pos n : I32) (i W : Nat) (fr : Frame) (σ' : State) : Prop :=
  σ' = σ ∧ fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧ fr.get 5 = some (.int n) ∧
  fr.get 10 = some (.int pos) ∧ fr.get 12 = some (.ref x) ∧
  ∃ idx len within : I32, fr.get 6 = some (.int idx) ∧ fr.get 7 = some (.int len) ∧
    fr.get 8 = some (.int within) ∧ idx.toInt = i ∧ len.toInt = slotLn i ∧ ValI within W

/-- Statement 26: `idx`, `len`, `within`, `take` computed, the state unchanged. -/
def A26 (σ : State) (a : Addr) (off : I64) (x : Addr) (pos n : I32) (i W K : Nat) (fr : Frame) (σ' : State) :
    Prop :=
  σ' = σ ∧ fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧ fr.get 5 = some (.int n) ∧
  fr.get 10 = some (.int pos) ∧ fr.get 12 = some (.ref x) ∧
  ∃ idx len within take : I32, fr.get 6 = some (.int idx) ∧ fr.get 7 = some (.int len) ∧
    fr.get 8 = some (.int within) ∧ fr.get 11 = some (.int take) ∧
    idx.toInt = i ∧ len.toInt = slotLn i ∧ within.toInt = W ∧ ValI take K

/-- Statement 30: `cur#7` holds the slot's text `c` (the slot's string, or `spaces(len)` for a `null` slot). -/
def A30 (σ0 : State) (a : Addr) (off : I64) (x : Addr) (t : JStr) (pos n : I32) (vs : List Value) (i W K P : Nat)
    (c : JStr) (fr : Frame) (σ : State) : Prop :=
  fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧ fr.get 5 = some (.int n) ∧
  fr.get 10 = some (.int pos) ∧ fr.get 12 = some (.ref x) ∧
  (∃ idx within take : I32, fr.get 6 = some (.int idx) ∧ fr.get 8 = some (.int within) ∧
    fr.get 11 = some (.int take) ∧ idx.toInt = i ∧ within.toInt = W ∧ take.toInt = K) ∧
  (∃ y, fr.get 15 = some (.ref y) ∧ σ.heap y = some (.str c)) ∧
  σ.heap a = some (.array (.cls "java.lang.String") vs) ∧ σ.heap x = some (.str t) ∧
  σ.initOf "Cbstm03a" = .done ∧ MemK σ0 σ a off t P

end EquivLean.Modernize.Cbstm03a.Java.Mw
