import EquivLean.Demo.Cobol.Cbact04cRust.Lookup

/-!
# The Rust `run`: its inputs, its callees as equations, the model step by cases

* `RunPre`: the inputs of `run` (each category record's account and disclosure group found by
  key, field bounds, at most `u32::MAX` records); `acct_found`, `disc_found`: what the lookups
  of `run` return on such inputs;
* the callees of the loop body as equations (`read_account_eq`, `read_rate_eq`, …);
* `rStep` by cases (first record, account change, same account), with its rate part `rRate`.
-/

open Aeneas Aeneas.Std Result

namespace EquivLean.Demo.Cbact04cRust
open cbact04c

/-! ## The inputs -/

/-- The inputs of `run`, as the precondition `RunPre` of the Java contract `runSpec`: at most
`u32::MAX` category records and, for each record `c`: the balance within `S9(9)V99`; an account
record with key `c.acct_id`, every record with that key holding the values `acctOf c.acct_id`,
whose balance is within `S9(10)V99`; a disclosure-group record with the key (the group of that
account, `c.type_cd`, `c.cat_cd`), every record with that key holding the rate `rateOf …`,
within `S9(4)V99`. -/
def RunPre (cats : Slice Cat) (accounts : Slice Account) (discs : Slice Disc)
    (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int) : Prop :=
  cats.val.length ≤ U32.max ∧
  ∀ c ∈ cats.val, c.bal.val.natAbs < 100000000000 ∧
    (∃ a ∈ accounts.val, a.id = c.acct_id) ∧
    (∀ a ∈ accounts.val, a.id = c.acct_id → RAcct.ofRust a = acctOf c.acct_id.val) ∧
    (acctOf c.acct_id.val).bal.natAbs < 1000000000000 ∧
    (∃ d ∈ discs.val, d.group_id.val = (acctOf c.acct_id.val).grp ∧ d.type_cd = c.type_cd ∧
      d.cat_cd = c.cat_cd) ∧
    (∀ d ∈ discs.val, d.group_id.val = (acctOf c.acct_id.val).grp → d.type_cd = c.type_cd →
      d.cat_cd = c.cat_cd → d.rate.val = rateOf (acctOf c.acct_id.val).grp c.type_cd.val c.cat_cd.val) ∧
    (rateOf (acctOf c.acct_id.val).grp c.type_cd.val c.cat_cd.val).natAbs < 1000000

theorem acct_found {accounts : Slice Account} {id : Std.I64} {acctOf : Int → RAcct}
    (hex : ∃ a ∈ accounts.val, a.id = id)
    (hall : ∀ a ∈ accounts.val, a.id = id → RAcct.ofRust a = acctOf id.val) :
    ∃ a, accounts.val.find? (acctKey id) = some a ∧ RAcct.ofRust a = acctOf id.val := by
  obtain ⟨a0, ha0, hid0⟩ := hex
  have hs : (accounts.val.find? (acctKey id)).isSome :=
    List.find?_isSome.2 ⟨a0, ha0, by simp [acctKey, hid0]⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hs
  refine ⟨a, ha, hall a (List.mem_of_find?_eq_some ha) ?_⟩
  have := List.find?_some ha
  simpa [acctKey] using this

theorem disc_found {discs : Slice Disc} {g : Std.U128} {t : Std.U16} {k : Std.I32} {rate : Int}
    (hex : ∃ d ∈ discs.val, d.group_id.val = g.val ∧ d.type_cd = t ∧ d.cat_cd = k)
    (hall : ∀ d ∈ discs.val, d.group_id.val = g.val → d.type_cd = t → d.cat_cd = k →
      d.rate.val = rate) :
    ∃ d, discs.val.find? (discKey g t k) = some d ∧ d.rate.val = rate := by
  obtain ⟨d0, hd0, hg0, ht0, hk0⟩ := hex
  have hs : (discs.val.find? (discKey g t k)).isSome :=
    List.find?_isSome.2 ⟨d0, hd0, by simp [discKey, UScalar.eq_equiv, hg0, ht0, hk0]⟩
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hs
  have hp := List.find?_some hd
  simp only [discKey, decide_eq_true_eq] at hp
  exact ⟨d, hd, hall d (List.mem_of_find?_eq_some hd) (by rw [hp.1]) hp.2.1 hp.2.2⟩

/-! ## The callees as equations -/

theorem read_account_eq (accounts : Slice Account) (id : Std.I64) :
    read_account accounts id = ok (accounts.val.find? (acctKey id)) := by
  obtain ⟨v, hv, hp⟩ := (spec_iff_exists _ _).1 (read_account_spec accounts id)
  rw [hv, hp]

theorem read_rate_eq (discs : Slice Disc) (g : Std.U128) (t : Std.U16) (k : Std.I32) (d : Disc)
    (hd : discs.val.find? (discKey g t k) = some d) : read_rate discs g t k = ok d.rate := by
  obtain ⟨v, hv, hp⟩ := (spec_iff_exists _ _).1 (read_rate_spec discs g t k (by rw [hd]; rfl))
  rw [hd, Option.map_some, Option.some.injEq] at hp
  rw [hv, hp]

theorem index_usize_eq {α : Type} (v : Slice α) (i : Std.Usize) (h : i.val < v.val.length) :
    Slice.index_usize v i = ok (v.val[i.val]) := by
  simp [Slice.index_usize, List.getElem?_eq_getElem h]

theorem index_usize_eq' {α : Type} (v : Slice α) (i : Std.Usize) (h : i.val < v.val.length)
    {x : α} (hx : v.val[i.val] = x) : Slice.index_usize v i = ok x := by
  rw [index_usize_eq v i h, hx]

theorem post_eq (a : Account) (t : Std.I64) (hb : a.bal.val.natAbs < 1000000000000)
    (ht : t.val.natAbs < 100000000000) :
    ∃ a', post a t = ok a' ∧ RAcct.ofRust a' = rPost (RAcct.ofRust a) t.val :=
  (spec_iff_exists _ _).1 (post_spec a t hb ht)

theorem push_eq {α : Type} (v : alloc.vec.Vec α) (x : α) (h : v.val.length < Usize.max) :
    ∃ v', alloc.vec.Vec.push v x = ok v' ∧ v'.val = v.val ++ [x] :=
  (spec_iff_exists _ _).1 (alloc.vec.Vec.push_spec v x h)

/-- A `let … ← if … then … else …` (Aeneas' `step*` splits only an `if` at the head). -/
theorem bind_ite {α β : Type} (c : Prop) [Decidable c] (t e : Result α) (k : α → Result β) :
    Std.bind (if c then t else e) k = if c then Std.bind t k else Std.bind e k := by
  split <;> rfl

theorem expect_some {α : Type} (a : α) (m : Str) : core.option.Option.expect (some a) m = ok a :=
  rfl

theorem unwrap_some {α : Type} (a : α) : core.option.Option.unwrap (some a) = ok a := rfl

/-! ## The model step, by cases -/

section
variable (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int)

theorem rStep_first (m : RState) (c : RCat) (hf : m.first = true) :
    rStep acctOf rateOf m c =
      rRate rateOf ⟨m.rewrites, m.tx, false, c.acct, 0, acctOf c.acct⟩ c := by
  simp [rStep, rRate, hf]

theorem rStep_change (m : RState) (c : RCat) (hf : m.first = false) (hc : c.acct ≠ m.last) :
    rStep acctOf rateOf m c =
      rRate rateOf ⟨m.rewrites ++ [rPost m.acct m.total], m.tx, false, c.acct, 0, acctOf c.acct⟩ c := by
  simp [rStep, rRate, hf, hc]

theorem rStep_same (m : RState) (c : RCat) (hf : m.first = false) (hc : c.acct = m.last) :
    rStep acctOf rateOf m c = rRate rateOf m c := by
  simp [rStep, rRate, hf, hc]

end

end EquivLean.Demo.Cbact04cRust
