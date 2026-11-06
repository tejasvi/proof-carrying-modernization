import EquivLean.Demo.Cobol.Cbact04cRust.Model
import EquivLean.Demo.Gen.Aeneas.Cbact04c.Funs

/-!
# The callees of `run`: the keyed lookups and the posting

Aeneas specifications (`c ⦃ p ⦄`: `c` returns `ok v` with `p v`, no panic, no divergence) of the
helpers of `examples/rust/cbact04c/src/lib.rs`, proved with Aeneas' `step*`:

* `read_account accounts id` is the first account with key `id` (`List.find?`), or `none`;
* `find_rate discs g t k` is the rate of the first disclosure-group record with key `(g, t, k)`;
* `read_rate discs g t k` is that rate when the key is found (the DEFAULT fallback is not
  reached), so no panic;
* `post a t` is `rPost` on the values, without overflow under the field bounds.
-/

open Aeneas Aeneas.Std Result

namespace EquivLean.Demo.Cbact04cRust
open cbact04c

/-- A specification is an `ok` result with the property. -/
theorem spec_iff_exists {α : Type} (c : Result α) (p : α → Prop) :
    c ⦃ p ⦄ ↔ ∃ v, c = ok v ∧ p v := by
  constructor
  · intro h
    cases c using Result.cases with
    | ret v => exact ⟨v, rfl, (WP.spec_ok v).1 h⟩
    | vis e k => exact absurd h (by simp)
    | div => exact absurd h (by simp)
  · rintro ⟨v, rfl, hv⟩
    exact (WP.spec_ok v).2 hv

/-- The key test of `read_account`. -/
def acctKey (id : Std.I64) (a : Account) : Bool := decide (a.id = id)

/-- The key test of `find_rate`. -/
def discKey (g : Std.U128) (t : Std.U16) (k : Std.I32) (d : Disc) : Bool :=
  decide (d.group_id = g ∧ d.type_cd = t ∧ d.cat_cd = k)

/-- Searching from position `j`: a hit at `j`. -/
theorem find?_drop_hit {α : Type} (l : List α) (p : α → Bool) (j : Nat) (hj : j < l.length)
    (hp : p l[j] = true) : (l.drop j).find? p = some l[j] := by
  rw [List.drop_eq_getElem_cons hj, List.find?_cons, hp]

/-- Searching from position `j`: no hit at `j`, continue at `j + 1`. -/
theorem find?_drop_miss {α : Type} (l : List α) (p : α → Bool) (j : Nat) (hj : j < l.length)
    (hp : p l[j] = false) : (l.drop j).find? p = (l.drop (j + 1)).find? p := by
  rw [List.drop_eq_getElem_cons hj, List.find?_cons, hp]

theorem read_account_loop_spec (accounts : Slice Account) (id : Std.I64) (i : Std.Usize)
    (hi : i.val ≤ accounts.val.length) :
    read_account_loop accounts id i ⦃ r => r = (accounts.val.drop i.val).find? (acctKey id) ⦄ := by
  unfold read_account_loop
  apply loop.spec_decr_nat (fun j => accounts.val.length - j.val)
    (fun j => j.val ≤ accounts.val.length ∧
      (accounts.val.drop i.val).find? (acctKey id) = (accounts.val.drop j.val).find? (acctKey id))
  · rintro j ⟨hj, hf⟩
    unfold read_account_loop.body
    step*
    · -- found
      rename_i hlt hid
      subst a_post
      rw [hf, find?_drop_hit _ _ _ (by scalar_tac) (by simp [acctKey, hid])]
    · -- not this one
      rename_i hlt hid
      subst a_post
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hf, find?_drop_miss _ _ _ (by scalar_tac) (by simp [acctKey, hid]), i2_post]
    · -- end of the slice
      rw [hf, List.drop_eq_nil_of_le (by scalar_tac)]
      rfl
  · exact ⟨hi, rfl⟩

/-- `read_account`: the first account with the key (`none`: INVALID KEY). -/
@[step]
theorem read_account_spec (accounts : Slice Account) (id : Std.I64) :
    read_account accounts id ⦃ r => r = accounts.val.find? (acctKey id) ⦄ := by
  unfold read_account
  have := read_account_loop_spec accounts id 0#usize (by simp)
  simpa using this

theorem find_rate_loop_spec (discs : Slice Disc) (g : Std.U128) (t : Std.U16) (k : Std.I32)
    (i : Std.Usize) (hi : i.val ≤ discs.val.length) :
    find_rate_loop discs g t k i ⦃ r =>
      r = ((discs.val.drop i.val).find? (discKey g t k)).map (·.rate) ⦄ := by
  unfold find_rate_loop
  apply loop.spec_decr_nat (fun j => discs.val.length - j.val)
    (fun j => j.val ≤ discs.val.length ∧
      (discs.val.drop i.val).find? (discKey g t k) = (discs.val.drop j.val).find? (discKey g t k))
  · rintro j ⟨hj, hf⟩
    unfold find_rate_loop.body
    step*
    · -- found
      rename_i hlt hg ht hk
      subst d_post
      rw [hf, find?_drop_hit _ _ _ (by scalar_tac) (by simp [discKey, hg, ht, hk])]
      rfl
    · rename_i hlt hg ht hk
      subst d_post
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hf, find?_drop_miss _ _ _ (by scalar_tac) (by simp [discKey, hk]), i2_post]
    · rename_i hlt hg ht
      subst d_post
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hf, find?_drop_miss _ _ _ (by scalar_tac) (by simp [discKey, ht]), i2_post]
    · rename_i hlt hg
      subst d_post
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hf, find?_drop_miss _ _ _ (by scalar_tac) (by simp [discKey, hg]), i2_post]
    · -- end of the slice
      rw [hf, List.drop_eq_nil_of_le (by scalar_tac)]
      rfl
  · exact ⟨hi, rfl⟩

/-- `find_rate`: the rate of the first disclosure-group record with the key. -/
@[step]
theorem find_rate_spec (discs : Slice Disc) (g : Std.U128) (t : Std.U16) (k : Std.I32) :
    find_rate discs g t k ⦃ r => r = (discs.val.find? (discKey g t k)).map (·.rate) ⦄ := by
  unfold find_rate
  have := find_rate_loop_spec discs g t k 0#usize (by simp)
  simpa using this

/-- `read_rate` when the key is found: its rate (the DEFAULT fallback is not reached). -/
@[step]
theorem read_rate_spec (discs : Slice Disc) (g : Std.U128) (t : Std.U16) (k : Std.I32)
    (h : (discs.val.find? (discKey g t k)).isSome) :
    read_rate discs g t k ⦃ r => some r = (discs.val.find? (discKey g t k)).map (·.rate) ⦄ := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨o, ho, hov⟩ := (spec_iff_exists _ _).1 (find_rate_spec discs g t k)
  rw [hd, Option.map_some] at hov
  subst hov
  unfold read_rate
  rw [ho, bind_ok]
  simp only [WP.spec_ok, hd, Option.map_some]

/-- `post a t`: `rPost` on the values, no overflow within `S9(10)V99` and `S9(9)V99`. -/
@[step]
theorem post_spec (a : Account) (t : Std.I64) (hb : a.bal.val.natAbs < 1000000000000)
    (ht : t.val.natAbs < 100000000000) :
    post a t ⦃ a' => RAcct.ofRust a' = rPost (RAcct.ofRust a) t.val ⦄ := by
  have hb1 : -1000000000000 < a.bal.val := by omega
  have hb2 : a.bal.val < 1000000000000 := by omega
  have ht1 : -100000000000 < t.val := by omega
  have ht2 : t.val < 100000000000 := by omega
  unfold post
  step*
  simp [RAcct.ofRust, rPost, *]

end EquivLean.Demo.Cbact04cRust
