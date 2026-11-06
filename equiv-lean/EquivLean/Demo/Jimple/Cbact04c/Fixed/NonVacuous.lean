import EquivLean.Demo.Jimple.Cbact04c.NonVacuous
import EquivLean.Demo.Jimple.Cbact04c.Fixed.Model

/-!
# The precondition of the fixed port's `run` is not vacuous

The construction of `Cbact04c/NonVacuous.lean` with the classes of the fixed port
(`Cbact04cFixed$Cat`, …): for every input of coblean's `cbact04c_all` there is a Java heap holding
the records as objects, with record functions `acctOf` and `rateOf` (those of
`Cbact04c/NonVacuous.lean`), such that `RunPreF` holds (`runPreF_exists`).  The class-independent
definitions and lemmas are used from `EquivLean.Demo.Cbact04c.NV`.
-/

open Cobol CardDemo.Cbact04c Jimple

namespace EquivLean.Demo.Cbact04c.NVF

open EquivLean.Demo.Cbact04c.NV (strOf_inj ofInt32_inj eq_of_pairwise_id mem_items mem_items'
  jcats_length length_le_items pairs_of_getElem catRefs acctRefs discRefs catRefs_length
  acctRefs_length discRefs_length size jdisc strAt_unique acctOf_eq cat_valid rateOf_eq)

/-! ## The heap

Addresses 0, 1, 2: the arrays of the `Cat`, `Account` and `Disc` objects. Item `k` of
`items accs` (the `k`-th category record `(a, c)`) occupies `3 + 5k` .. `3 + 5k + 4`: its `Cat`
object, the `Cat`'s type string, its `Disc` object, the `Disc`'s group and type strings. Account
`j` occupies `3 + 5n + 2j` (its `Account` object) and the next address (its group string), where
`n` is the number of items. -/

def catObj (a : Acc) (c : Cat) (t : Addr) : Obj :=
  .plain "Cbact04cFixed$Cat" [(("Cbact04cFixed$Cat", "acctId"), .long (BitVec.ofInt 64 a.id)),
    (("Cbact04cFixed$Cat", "typeCd"), .ref t), (("Cbact04cFixed$Cat", "catCd"), .int (BitVec.ofInt 32 c.cat)),
    (("Cbact04cFixed$Cat", "bal"), .long (BitVec.ofInt 64 c.bal))]

def discObj (r : Int) (c : Cat) (g t : Addr) : Obj :=
  .plain "Cbact04cFixed$Disc" [(("Cbact04cFixed$Disc", "groupId"), .ref g), (("Cbact04cFixed$Disc", "typeCd"), .ref t),
    (("Cbact04cFixed$Disc", "catCd"), .int (BitVec.ofInt 32 c.cat)),
    (("Cbact04cFixed$Disc", "rate"), .long (BitVec.ofInt 64 r))]

def acctObj (a : Acc) (g : Addr) : Obj :=
  .plain "Cbact04cFixed$Account" [(("Cbact04cFixed$Account", "id"), .long (BitVec.ofInt 64 a.id)),
    (("Cbact04cFixed$Account", "bal"), .long (BitVec.ofInt 64 a.bal)),
    (("Cbact04cFixed$Account", "cycCredit"), .long (BitVec.ofInt 64 a.cc)),
    (("Cbact04cFixed$Account", "cycDebit"), .long (BitVec.ofInt 64 a.cd)),
    (("Cbact04cFixed$Account", "groupId"), .ref g)]

/-- The objects of item `(a, c)` at `base + r`. -/
def itemObj (rate : Acc → Cat → Int) (a : Acc) (c : Cat) (base r : Nat) : Obj :=
  if r = 0 then catObj a c (base + 1)
  else if r = 1 then .str (strOf c.ty)
  else if r = 2 then discObj (rate a c) c (base + 3) (base + 4)
  else if r = 3 then .str (strOf a.grp)
  else .str (strOf c.ty)

def obj (accs : List Acc) (rate : Acc → Cat → Int) (x : Nat) : Obj :=
  if x = 0 then .array (.cls "Cbact04cFixed$Cat") (catRefs accs)
  else if x = 1 then .array (.cls "Cbact04cFixed$Account") (acctRefs accs)
  else if x = 2 then .array (.cls "Cbact04cFixed$Disc") (discRefs accs)
  else if x < 3 + 5 * (items accs).length then
    match (items accs)[(x - 3) / 5]? with
    | some p => itemObj rate p.1 p.2 (3 + 5 * ((x - 3) / 5)) ((x - 3) % 5)
    | none => .str []
  else
    match accs[(x - 3 - 5 * (items accs).length) / 2]? with
    | some a =>
      if (x - 3 - 5 * (items accs).length) % 2 = 0 then acctObj a (x + 1) else .str (strOf a.grp)
    | none => .str []

def state (accs : List Acc) (rate : Acc → Cat → Int) : Jimple.State :=
  ⟨((List.range (size accs)).map (obj accs rate)).toArray, [],
   [("Cbact04cFixed", .done), ("Cbact04cFixed$Account", .done), ("Cbact04cFixed$Result", .done)], [], []⟩

section
variable {accs : List Acc} {rate : Acc → Cat → Int}

theorem heap_state {x : Nat} (hx : x < size accs) :
    (state accs rate).heap x = some (obj accs rate x) := by
  simp only [state, State.heap, List.getElem?_toArray, List.getElem?_map, List.getElem?_range hx,
    Option.map_some]

theorem heap_cats : (state accs rate).heap 0 = some (.array (.cls "Cbact04cFixed$Cat") (catRefs accs)) := by
  rw [heap_state (by unfold size; omega)]; simp [obj]

theorem heap_accts :
    (state accs rate).heap 1 = some (.array (.cls "Cbact04cFixed$Account") (acctRefs accs)) := by
  rw [heap_state (by unfold size; omega)]; simp [obj]

theorem heap_discs :
    (state accs rate).heap 2 = some (.array (.cls "Cbact04cFixed$Disc") (discRefs accs)) := by
  rw [heap_state (by unfold size; omega)]; simp [obj]

theorem heap_item {k : Nat} {a : Acc} {c : Cat} (hk : (items accs)[k]? = some (a, c)) {r : Nat}
    (hr : r < 5) : (state accs rate).heap (3 + 5 * k + r) = some (itemObj rate a c (3 + 5 * k) r) := by
  have hlt : k < (items accs).length := (List.getElem?_eq_some_iff.1 hk).1
  rw [heap_state (by unfold size; omega)]
  have h1 : (3 + 5 * k + r - 3) / 5 = k := by omega
  have h2 : (3 + 5 * k + r - 3) % 5 = r := by omega
  have h3 : 3 + 5 * k + r < 3 + 5 * (items accs).length := by omega
  simp only [obj, show 3 + 5 * k + r ≠ 0 by omega, show 3 + 5 * k + r ≠ 1 by omega,
    show 3 + 5 * k + r ≠ 2 by omega, h3, h1, h2, hk, ite_false, ite_true]

theorem heap_acct {j : Nat} {a : Acc} (hj : accs[j]? = some a) :
    (state accs rate).heap (3 + 5 * (items accs).length + 2 * j) =
      some (acctObj a (3 + 5 * (items accs).length + 2 * j + 1)) := by
  have hlt : j < accs.length := (List.getElem?_eq_some_iff.1 hj).1
  rw [heap_state (by unfold size; omega)]
  have h1 : (3 + 5 * (items accs).length + 2 * j - 3 - 5 * (items accs).length) / 2 = j := by omega
  have h2 : (3 + 5 * (items accs).length + 2 * j - 3 - 5 * (items accs).length) % 2 = 0 := by omega
  simp only [obj, show 3 + 5 * (items accs).length + 2 * j ≠ 0 by omega,
    show 3 + 5 * (items accs).length + 2 * j ≠ 1 by omega,
    show 3 + 5 * (items accs).length + 2 * j ≠ 2 by omega,
    show ¬ (3 + 5 * (items accs).length + 2 * j < 3 + 5 * (items accs).length) by omega,
    h1, h2, hj, ite_false, ite_true]

theorem heap_acct_grp {j : Nat} {a : Acc} (hj : accs[j]? = some a) :
    (state accs rate).heap (3 + 5 * (items accs).length + 2 * j + 1) = some (.str (strOf a.grp)) := by
  have hlt : j < accs.length := (List.getElem?_eq_some_iff.1 hj).1
  rw [heap_state (by unfold size; omega)]
  have h1 : (3 + 5 * (items accs).length + 2 * j + 1 - 3 - 5 * (items accs).length) / 2 = j := by
    omega
  have h2 : (3 + 5 * (items accs).length + 2 * j + 1 - 3 - 5 * (items accs).length) % 2 = 1 := by
    omega
  simp only [obj, show 3 + 5 * (items accs).length + 2 * j + 1 ≠ 0 by omega,
    show 3 + 5 * (items accs).length + 2 * j + 1 ≠ 1 by omega,
    show 3 + 5 * (items accs).length + 2 * j + 1 ≠ 2 by omega,
    show ¬ (3 + 5 * (items accs).length + 2 * j + 1 < 3 + 5 * (items accs).length) by omega,
    h1, h2, hj, ite_false, show (1 : Nat) ≠ 0 by decide]

/-! ### The records as objects -/

theorem catAt_item {k : Nat} {a : Acc} {c : Cat} (hk : (items accs)[k]? = some (a, c)) :
    CatAtC "Cbact04cFixed$Cat" (state accs rate) (.ref (3 + 5 * k)) (jcat a c) := by
  have h0 := heap_item (rate := rate) hk (r := 0) (by omega)
  have h1 := heap_item (rate := rate) hk (r := 1) (by omega)
  simp only [Nat.add_zero, itemObj, ite_true, catObj] at h0
  simp only [itemObj, show (1 : Nat) ≠ 0 by decide, ite_false, ite_true] at h1
  exact ⟨3 + 5 * k, _, .ref (3 + 5 * k + 1), rfl, h0, rfl, rfl, ⟨3 + 5 * k + 1, rfl, h1⟩, rfl, rfl⟩

theorem discAt_item {k : Nat} {a : Acc} {c : Cat} (hk : (items accs)[k]? = some (a, c)) :
    DiscAtC "Cbact04cFixed$Disc" (state accs rate) (.ref (3 + 5 * k + 2)) (jdisc rate a c) := by
  have h2 := heap_item (rate := rate) hk (r := 2) (by omega)
  have h3 := heap_item (rate := rate) hk (r := 3) (by omega)
  have h4 := heap_item (rate := rate) hk (r := 4) (by omega)
  simp only [itemObj, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false,
    ite_true, discObj] at h2
  simp only [itemObj, show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
    show (3 : Nat) ≠ 2 by decide, ite_false, ite_true] at h3
  simp only [itemObj, show (4 : Nat) ≠ 0 by decide, show (4 : Nat) ≠ 1 by decide,
    show (4 : Nat) ≠ 2 by decide, show (4 : Nat) ≠ 3 by decide, ite_false] at h4
  exact ⟨3 + 5 * k + 2, _, .ref (3 + 5 * k + 3), .ref (3 + 5 * k + 4), rfl, h2, rfl,
    ⟨3 + 5 * k + 3, rfl, h3⟩, rfl, ⟨3 + 5 * k + 4, rfl, h4⟩, rfl, rfl⟩

theorem acctAt_acct {j : Nat} {a : Acc} (hj : accs[j]? = some a) :
    AcctAtC "Cbact04cFixed$Account" (state accs rate) (.ref (3 + 5 * (items accs).length + 2 * j)) (jacct a) := by
  have h0 := heap_acct (rate := rate) hj
  have h1 := heap_acct_grp (rate := rate) hj
  simp only [acctObj] at h0
  exact ⟨_, _, .ref (3 + 5 * (items accs).length + 2 * j + 1), rfl, h0, rfl, rfl, rfl, rfl, rfl,
    ⟨_, rfl, h1⟩⟩

theorem idOf_acct {j : Nat} {a : Acc} (hj : accs[j]? = some a) :
    idOfC "Cbact04cFixed$Account" (state accs rate) (.ref (3 + 5 * (items accs).length + 2 * j)) =
      some (BitVec.ofInt 64 a.id) := by
  have h0 := heap_acct (rate := rate) hj
  simp only [acctObj] at h0
  simp only [idOfC, h0, ↓reduceIte]
  rfl

end

theorem discAtC_unique {D : ClassName} {σ : Jimple.State} {v : Jimple.Value} {d d' : JDisc}
    (h1 : DiscAtC D σ v d) (h2 : DiscAtC D σ v d') : d = d' := by
  obtain ⟨x, fs, g, t, rfl, hx, hg, hgs, ht, hts, hc, hr⟩ := h1
  obtain ⟨y, fs', g', t', hy, hy', hg', hgs', ht', hts', hc', hr'⟩ := h2
  cases hy
  rw [hx] at hy'
  cases hy'
  rw [hg] at hg'; cases hg'
  rw [ht] at ht'; cases ht'
  rw [hc] at hc'
  rw [hr] at hr'
  have e1 := strAt_unique hgs hgs'
  have e2 := strAt_unique hts hts'
  simp only [Option.some.injEq, Jimple.Value.int.injEq, Jimple.Value.long.injEq] at hc' hr'
  cases d; cases d'
  simp only at e1 e2 hc' hr' ⊢
  subst e1; subst e2; subst hc'; subst hr'
  rfl

end EquivLean.Demo.Cbact04c.NVF

namespace EquivLean.Demo.Cbact04c

open NVF in
open NV (strOf_inj ofInt32_inj eq_of_pairwise_id mem_items mem_items' jcats_length length_le_items
  pairs_of_getElem catRefs acctRefs discRefs catRefs_length acctRefs_length discRefs_length size jdisc
  strAt_unique acctOf_eq cat_valid rateOf_eq) in
set_option linter.unusedVariables false in
/-- **The precondition of the fixed port's `run` holds for every input of `cbact04c_all`**: a heap
with the records as objects of the fixed port's classes (`NVF.state`) and the record functions of
`runPre_exists`. -/
theorem runPreF_exists (accs : List Acc) (hval : ∀ a ∈ accs, a.valid)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) (hlen : (items accs).length < 999999)
    (rate : Acc → Cat → Int) (hrate : ∀ a ∈ accs, ∀ c ∈ a.cats, (rate a c).natAbs < 1000000)
    (hkey : ∀ a ∈ accs, ∀ c ∈ a.cats, ∀ a' ∈ accs, ∀ c' ∈ a'.cats,
      a.grp = a'.grp → c.ty = c'.ty → c.cat = c'.cat → rate a c = rate a' c') :
    ∃ σ ca aa da acctOf rateOf, RunPreF σ ca aa da acctOf rateOf (jcats accs) ∧
      (∀ a ∈ accs, acctOf (BitVec.ofInt 64 a.id) = jacct a) ∧
      (∀ a ∈ accs, ∀ c ∈ a.cats,
        rateOf (strOf a.grp) (strOf c.ty) (BitVec.ofInt 32 c.cat) = BitVec.ofInt 64 (rate a c)) := by
  refine ⟨state accs rate, 0, 1, 2, NV.acctOf accs, NV.rateOf accs rate, ?_,
    fun a ha => acctOf_eq hval hdist ha, fun a ha c hc => rateOf_eq hval hkey ha hc⟩
  have hm : accs.length ≤ (items accs).length :=
    length_le_items accs (fun a ha => (hval a ha).2.2.2.2.2.2.2.2.2.2.2.1)
  refine ⟨⟨_, _, heap_cats, ?_⟩, by rw [jcats_length]; omega,
    ⟨_, _, heap_accts, by rw [acctRefs_length]; omega, ?_, ?_⟩,
    ⟨_, _, heap_discs, by rw [discRefs_length]; omega, ?_, ?_⟩, rfl, rfl, rfl⟩
  · -- the category records
    refine pairs_of_getElem (by rw [catRefs_length, jcats_length]) fun k h1 h2 => ?_
    have hk : k < (items accs).length := by rw [catRefs_length] at h1; exact h1
    have hp : (items accs)[k]? = some ((items accs)[k].1, (items accs)[k].2) := by
      rw [List.getElem?_eq_getElem hk]
    simpa [catRefs, jcats] using catAt_item (rate := rate) hp
  · -- every account object
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    have hj' : j < accs.length := List.mem_range.1 hj
    exact ⟨_, acctAt_acct (rate := rate) (List.getElem?_eq_getElem hj')⟩
  · -- the account of each record
    intro c hc
    obtain ⟨⟨a, c0⟩, hp, rfl⟩ := List.mem_map.1 hc
    obtain ⟨ha, hc0⟩ := mem_items'.1 hp
    have e : NV.acctOf accs (jcat a c0).acct = jacct a := acctOf_eq hval hdist ha
    rw [e]
    refine ⟨rfl, ?_, ?_⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 ha
      have hj' : j < accs.length := (List.getElem?_eq_some_iff.1 hj).1
      exact ⟨_, List.mem_map.2 ⟨j, List.mem_range.2 hj', rfl⟩, acctAt_acct (rate := rate) hj⟩
    · intro x hx hid
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      have hj' : j < accs.length := List.mem_range.1 hj
      have hget := List.getElem?_eq_getElem hj'
      rw [idOf_acct (rate := rate) hget] at hid
      have e1 : BitVec.ofInt 64 accs[j].id = BitVec.ofInt 64 a.id := Option.some.inj hid
      have hmem : accs[j] ∈ accs := List.getElem_mem hj'
      have e2 : accs[j] = a :=
        eq_of_pairwise_id hdist hmem ha ((ofInt64_inj (hval _ hmem).1 (hval a ha).1).1 e1)
      have := acctAt_acct (rate := rate) hget
      rwa [e2] at this
  · -- every disclosure-group object
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have hk' : k < (items accs).length := List.mem_range.1 hk
    have hp : (items accs)[k]? = some ((items accs)[k].1, (items accs)[k].2) := by
      rw [List.getElem?_eq_getElem hk']
    exact ⟨_, discAt_item (rate := rate) hp⟩
  · -- the disclosure group of each record
    intro c hc
    obtain ⟨⟨a, c0⟩, hp, rfl⟩ := List.mem_map.1 hc
    obtain ⟨ha, hc0⟩ := mem_items'.1 hp
    have e : NV.acctOf accs (jcat a c0).acct = jacct a := acctOf_eq hval hdist ha
    rw [e]
    have er : NV.rateOf accs rate (jacct a).grp (jcat a c0).ty (jcat a c0).cat =
        BitVec.ofInt 64 (rate a c0) := rateOf_eq hval hkey ha hc0
    rw [er]
    refine ⟨?_, ?_⟩
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hp
      have hk' : k < (items accs).length := (List.getElem?_eq_some_iff.1 hk).1
      exact ⟨_, List.mem_map.2 ⟨k, List.mem_range.2 hk', rfl⟩, discAt_item (rate := rate) hk⟩
    · intro x hx d hd hg ht hcat
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      have hk' : k < (items accs).length := List.mem_range.1 hk
      have hget : (items accs)[k]? = some ((items accs)[k].1, (items accs)[k].2) := by
        rw [List.getElem?_eq_getElem hk']
      have hd' := discAt_item (rate := rate) hget
      have ed := discAtC_unique hd' hd
      subst ed
      have hmem : (items accs)[k] ∈ items accs := List.getElem_mem hk'
      obtain ⟨hp1, hp2⟩ := mem_items.1 hmem
      have hcv := cat_valid hval ha hc0
      have hpv := cat_valid hval hp1 hp2
      simp only [jdisc, jacct, jcat] at hg ht hcat ⊢
      have e3 : (items accs)[k].2.cat = c0.cat := ofInt32_inj (by have := hpv.2.2.1; omega)
        (by have := hcv.2.2.1; omega) hcat
      rw [hkey _ hp1 _ hp2 a ha c0 hc0 (strOf_inj hg) (strOf_inj ht) e3]

end EquivLean.Demo.Cbact04c

#print axioms EquivLean.Demo.Cbact04c.runPreF_exists
