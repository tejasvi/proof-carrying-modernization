import EquivLean.Demo.Jimple.Cbact04c.Pure

/-!
# The precondition of `run` is not vacuous

For every input of coblean's `cbact04c_all` (accounts with distinct keys, each with its category
records, and rates that agree on equal disclosure-group keys) there is a Java heap holding the
records as objects, with record functions `acctOf` and `rateOf`, such that `RunPre` holds and the
functions agree with the records (`jacct`, the rates as Java `long`s).
-/

open Cobol CardDemo.Cbact04c Jimple

namespace EquivLean.Demo.Cbact04c.NV

/-! ## Injectivity of the encodings -/

/-- The UTF-16 unit of a CP037 byte. -/
def unit037 (b : UInt8) : JChar := BitVec.ofNat 16 (Codepage.cp037Char b).toNat

theorem cp037Char_toNat_lt (b : UInt8) : (Codepage.cp037Char b).toNat < 256 := by
  obtain ⟨-, -, h, -⟩ := Codepage.cp037_check b.toNat b.toNat_lt
  unfold Codepage.cp037Char
  rw [Codepage.Char.toNat_ofNat_lt256 _ h]
  exact h

/-- The byte of a UTF-16 unit (a left inverse of `unit037`). -/
def byte037 (u : JChar) : UInt8 := (Codepage.cp037Byte (Char.ofNat u.toNat)).getD 0

theorem byte037_unit037 (b : UInt8) : byte037 (unit037 b) = b := by
  have h := cp037Char_toNat_lt b
  unfold byte037 unit037
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have : Char.ofNat (Codepage.cp037Char b).toNat = Codepage.cp037Char b := by
    apply Char.ext
    apply UInt32.toNat_inj.mp
    show (Char.ofNat (Codepage.cp037Char b).toNat).toNat = (Codepage.cp037Char b).toNat
    exact Codepage.Char.toNat_ofNat_lt256 _ h
  rw [this, Codepage.cp037Byte_cp037Char]
  rfl

theorem strOf_eq_map (bs : List UInt8) : strOf bs = bs.map unit037 := rfl

theorem map_byte037_strOf : ∀ (x : List UInt8), (strOf x).map byte037 = x
  | [] => rfl
  | b :: bs => by
    rw [strOf_eq_map, List.map_cons, List.map_cons, byte037_unit037, ← strOf_eq_map,
      map_byte037_strOf bs]

theorem strOf_inj {x y : List UInt8} (h : strOf x = strOf y) : x = y := by
  rw [← map_byte037_strOf x, ← map_byte037_strOf y, h]

theorem ofInt32_inj {x y : Int} (hx : x.natAbs < 2147483648) (hy : y.natAbs < 2147483648)
    (h : BitVec.ofInt 32 x = BitVec.ofInt 32 y) : x = y := by
  have := congrArg BitVec.toInt h
  rw [BitVec.toInt_ofInt, BitVec.toInt_ofInt] at this
  rw [Int.bmod_def, Int.bmod_def] at this
  split at this <;> split at this <;> omega

/-! ## Lists -/

theorem eq_of_pairwise_id {l : List Acc} (hd : l.Pairwise (fun a b => a.id ≠ b.id)) :
    ∀ {a b : Acc}, a ∈ l → b ∈ l → a.id = b.id → a = b := by
  induction l with
  | nil => intro a b ha; simp at ha
  | cons x xs ih =>
    intro a b ha hb hab
    rw [List.pairwise_cons] at hd
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · exact absurd hab (hd.1 b hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd hab.symm (hd.1 a ha')
      · exact ih hd.2 ha' hb' hab

theorem mem_items {accs : List Acc} {p : Acc × Cat} : p ∈ items accs ↔ p.1 ∈ accs ∧ p.2 ∈ p.1.cats := by
  obtain ⟨a, c⟩ := p
  simp only [items, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha', c', hc', rfl, rfl⟩; exact ⟨ha', hc'⟩
  · rintro ⟨ha, hc⟩; exact ⟨a, ha, c, hc, rfl, rfl⟩

theorem mem_items' {accs : List Acc} {a : Acc} {c : Cat} : (a, c) ∈ items accs ↔ a ∈ accs ∧ c ∈ a.cats :=
  mem_items

theorem jcats_length (accs : List Acc) : (jcats accs).length = (items accs).length := by
  simp [jcats]

theorem length_le_items : ∀ (accs : List Acc), (∀ a ∈ accs, a.cats ≠ []) →
    accs.length ≤ (items accs).length
  | [], _ => by simp [items]
  | a :: rest, h => by
    have h1 := length_le_items rest (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have h2 : a.cats ≠ [] := h a (List.mem_cons_self ..)
    have h3 : 1 ≤ a.cats.length := by
      cases hc : a.cats with
      | nil => exact absurd hc h2
      | cons _ _ => simp
    simp only [items, List.flatMap_cons, List.length_append, List.length_map, List.length_cons] at h1 ⊢
    omega

theorem pairs_of_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} (_hl : xs.length = ys.length),
      (∀ k (h1 : k < xs.length) (h2 : k < ys.length), R xs[k] ys[k]) → Pairs R xs ys
  | [], [], _, _ => trivial
  | x :: xs, y :: ys, hl, h => by
    refine ⟨h 0 (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega),
      pairs_of_getElem (by simpa using hl) fun k h1 h2 => ?_⟩
    have := h (k + 1) (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
    simpa only [List.getElem_cons_succ] using this
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-! ## The heap

Addresses 0, 1, 2: the arrays of the `Cat`, `Account` and `Disc` objects. Item `k` of
`items accs` (the `k`-th category record `(a, c)`) occupies `3 + 5k` .. `3 + 5k + 4`: its `Cat`
object, the `Cat`'s type string, its `Disc` object, the `Disc`'s group and type strings. Account
`j` occupies `3 + 5n + 2j` (its `Account` object) and the next address (its group string), where
`n` is the number of items. -/

def catObj (a : Acc) (c : Cat) (t : Addr) : Obj :=
  .plain "Cbact04c$Cat" [(("Cbact04c$Cat", "acctId"), .long (BitVec.ofInt 64 a.id)),
    (("Cbact04c$Cat", "typeCd"), .ref t), (("Cbact04c$Cat", "catCd"), .int (BitVec.ofInt 32 c.cat)),
    (("Cbact04c$Cat", "bal"), .long (BitVec.ofInt 64 c.bal))]

def discObj (r : Int) (c : Cat) (g t : Addr) : Obj :=
  .plain "Cbact04c$Disc" [(("Cbact04c$Disc", "groupId"), .ref g), (("Cbact04c$Disc", "typeCd"), .ref t),
    (("Cbact04c$Disc", "catCd"), .int (BitVec.ofInt 32 c.cat)),
    (("Cbact04c$Disc", "rate"), .long (BitVec.ofInt 64 r))]

def acctObj (a : Acc) (g : Addr) : Obj :=
  .plain "Cbact04c$Account" [(("Cbact04c$Account", "id"), .long (BitVec.ofInt 64 a.id)),
    (("Cbact04c$Account", "bal"), .long (BitVec.ofInt 64 a.bal)),
    (("Cbact04c$Account", "cycCredit"), .long (BitVec.ofInt 64 a.cc)),
    (("Cbact04c$Account", "cycDebit"), .long (BitVec.ofInt 64 a.cd)),
    (("Cbact04c$Account", "groupId"), .ref g)]

/-- The objects of item `(a, c)` at `base + r`. -/
def itemObj (rate : Acc → Cat → Int) (a : Acc) (c : Cat) (base r : Nat) : Obj :=
  if r = 0 then catObj a c (base + 1)
  else if r = 1 then .str (strOf c.ty)
  else if r = 2 then discObj (rate a c) c (base + 3) (base + 4)
  else if r = 3 then .str (strOf a.grp)
  else .str (strOf c.ty)

def catRefs (accs : List Acc) : List Jimple.Value :=
  (List.range (items accs).length).map fun k => .ref (3 + 5 * k)

def acctRefs (accs : List Acc) : List Jimple.Value :=
  (List.range accs.length).map fun j => .ref (3 + 5 * (items accs).length + 2 * j)

def discRefs (accs : List Acc) : List Jimple.Value :=
  (List.range (items accs).length).map fun k => .ref (3 + 5 * k + 2)

theorem catRefs_length (accs : List Acc) : (catRefs accs).length = (items accs).length := by
  simp [catRefs]

theorem acctRefs_length (accs : List Acc) : (acctRefs accs).length = accs.length := by
  simp [acctRefs]

theorem discRefs_length (accs : List Acc) : (discRefs accs).length = (items accs).length := by
  simp [discRefs]

def obj (accs : List Acc) (rate : Acc → Cat → Int) (x : Nat) : Obj :=
  if x = 0 then .array (.cls "Cbact04c$Cat") (catRefs accs)
  else if x = 1 then .array (.cls "Cbact04c$Account") (acctRefs accs)
  else if x = 2 then .array (.cls "Cbact04c$Disc") (discRefs accs)
  else if x < 3 + 5 * (items accs).length then
    match (items accs)[(x - 3) / 5]? with
    | some p => itemObj rate p.1 p.2 (3 + 5 * ((x - 3) / 5)) ((x - 3) % 5)
    | none => .str []
  else
    match accs[(x - 3 - 5 * (items accs).length) / 2]? with
    | some a =>
      if (x - 3 - 5 * (items accs).length) % 2 = 0 then acctObj a (x + 1) else .str (strOf a.grp)
    | none => .str []

def size (accs : List Acc) : Nat := 3 + 5 * (items accs).length + 2 * accs.length

def state (accs : List Acc) (rate : Acc → Cat → Int) : Jimple.State :=
  ⟨((List.range (size accs)).map (obj accs rate)).toArray, [],
   [("Cbact04c", .done), ("Cbact04c$Account", .done), ("Cbact04c$Result", .done)], [], []⟩

section
variable {accs : List Acc} {rate : Acc → Cat → Int}

theorem heap_state {x : Nat} (hx : x < size accs) :
    (state accs rate).heap x = some (obj accs rate x) := by
  simp only [state, State.heap, List.getElem?_toArray, List.getElem?_map, List.getElem?_range hx,
    Option.map_some]

theorem heap_cats : (state accs rate).heap 0 = some (.array (.cls "Cbact04c$Cat") (catRefs accs)) := by
  rw [heap_state (by unfold size; omega)]; simp [obj]

theorem heap_accts :
    (state accs rate).heap 1 = some (.array (.cls "Cbact04c$Account") (acctRefs accs)) := by
  rw [heap_state (by unfold size; omega)]; simp [obj]

theorem heap_discs :
    (state accs rate).heap 2 = some (.array (.cls "Cbact04c$Disc") (discRefs accs)) := by
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
    CatAt (state accs rate) (.ref (3 + 5 * k)) (jcat a c) := by
  have h0 := heap_item (rate := rate) hk (r := 0) (by omega)
  have h1 := heap_item (rate := rate) hk (r := 1) (by omega)
  simp only [Nat.add_zero, itemObj, ite_true, catObj] at h0
  simp only [itemObj, show (1 : Nat) ≠ 0 by decide, ite_false, ite_true] at h1
  exact ⟨3 + 5 * k, _, .ref (3 + 5 * k + 1), rfl, h0, rfl, rfl, ⟨3 + 5 * k + 1, rfl, h1⟩, rfl, rfl⟩

/-- The disclosure-group record of item `(a, c)`. -/
def jdisc (rate : Acc → Cat → Int) (a : Acc) (c : Cat) : JDisc :=
  ⟨strOf a.grp, strOf c.ty, BitVec.ofInt 32 c.cat, BitVec.ofInt 64 (rate a c)⟩

theorem discAt_item {k : Nat} {a : Acc} {c : Cat} (hk : (items accs)[k]? = some (a, c)) :
    DiscAt (state accs rate) (.ref (3 + 5 * k + 2)) (jdisc rate a c) := by
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
    AcctAt (state accs rate) (.ref (3 + 5 * (items accs).length + 2 * j)) (jacct a) := by
  have h0 := heap_acct (rate := rate) hj
  have h1 := heap_acct_grp (rate := rate) hj
  simp only [acctObj] at h0
  exact ⟨_, _, .ref (3 + 5 * (items accs).length + 2 * j + 1), rfl, h0, rfl, rfl, rfl, rfl, rfl,
    ⟨_, rfl, h1⟩⟩

theorem idOf_acct {j : Nat} {a : Acc} (hj : accs[j]? = some a) :
    idOf (state accs rate) (.ref (3 + 5 * (items accs).length + 2 * j)) =
      some (BitVec.ofInt 64 a.id) := by
  have h0 := heap_acct (rate := rate) hj
  simp only [acctObj] at h0
  simp only [idOf, h0]
  rfl

end

theorem strAt_unique {σ : Jimple.State} {v : Jimple.Value} {s s' : JStr} (h1 : StrAt σ v s)
    (h2 : StrAt σ v s') : s = s' := by
  obtain ⟨x, rfl, hx⟩ := h1
  obtain ⟨y, hy, hy'⟩ := h2
  cases hy
  rw [hx] at hy'
  cases hy'
  rfl

theorem discAt_unique {σ : Jimple.State} {v : Jimple.Value} {d d' : JDisc} (h1 : DiscAt σ v d)
    (h2 : DiscAt σ v d') : d = d' := by
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

/-! ## The record functions -/

/-- The account record with key `k`. -/
def acctOf (accs : List Acc) (k : I64) : JAcct :=
  match accs.find? (fun a => BitVec.ofInt 64 a.id == k) with
  | some a => jacct a
  | none => default

/-- The rate of the first item with key `(g, t, k)`. -/
def rateOf (accs : List Acc) (rate : Acc → Cat → Int) (g t : JStr) (k : I32) : I64 :=
  match (items accs).find? (fun p =>
      strOf p.1.grp == g && strOf p.2.ty == t && BitVec.ofInt 32 p.2.cat == k) with
  | some p => BitVec.ofInt 64 (rate p.1 p.2)
  | none => 0

theorem acctOf_eq {accs : List Acc} (hval : ∀ a ∈ accs, a.valid)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) {a : Acc} (ha : a ∈ accs) :
    acctOf accs (BitVec.ofInt 64 a.id) = jacct a := by
  unfold acctOf
  split
  · next a' h =>
    have h1 := List.find?_some h
    have h2 := List.mem_of_find?_eq_some h
    simp only [beq_iff_eq] at h1
    have h3 : a'.id = a.id := (ofInt64_inj (hval a' h2).1 (hval a ha).1).1 h1
    rw [eq_of_pairwise_id hdist h2 ha h3]
  · next h =>
    exact absurd (by simp) (List.find?_eq_none.1 h a ha)

theorem cat_valid {accs : List Acc} (hval : ∀ a ∈ accs, a.valid) {a : Acc} (ha : a ∈ accs)
    {c : Cat} (hc : c ∈ a.cats) : c.valid :=
  (hval a ha).2.2.2.2.2.2.2.2.2.2.2.2 c hc

theorem rateOf_eq {accs : List Acc} {rate : Acc → Cat → Int} (hval : ∀ a ∈ accs, a.valid)
    (hkey : ∀ a ∈ accs, ∀ c ∈ a.cats, ∀ a' ∈ accs, ∀ c' ∈ a'.cats,
      a.grp = a'.grp → c.ty = c'.ty → c.cat = c'.cat → rate a c = rate a' c')
    {a : Acc} (ha : a ∈ accs) {c : Cat} (hc : c ∈ a.cats) :
    rateOf accs rate (strOf a.grp) (strOf c.ty) (BitVec.ofInt 32 c.cat) =
      BitVec.ofInt 64 (rate a c) := by
  unfold rateOf
  split
  · next p h =>
    have h1 := List.find?_some h
    have h2 := List.mem_of_find?_eq_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨⟨hg, ht⟩, hk⟩ := h1
    obtain ⟨hp1, hp2⟩ := mem_items.1 h2
    have hcv := cat_valid hval ha hc
    have hpv := cat_valid hval hp1 hp2
    have e3 : p.2.cat = c.cat := ofInt32_inj (by have := hpv.2.2.1; omega)
      (by have := hcv.2.2.1; omega) hk
    rw [hkey p.1 hp1 p.2 hp2 a ha c hc (strOf_inj hg) (strOf_inj ht) e3]
  · next h =>
    exact absurd (by simp) (List.find?_eq_none.1 h (a, c) (mem_items.2 ⟨ha, hc⟩))

end EquivLean.Demo.Cbact04c.NV

namespace EquivLean.Demo.Cbact04c

open NV in
set_option linter.unusedVariables false in
/-- **The precondition of `run` holds for every input of `cbact04c_all`**: a heap with the
records as objects (`NV.state`) and record functions that agree with the records. -/
theorem runPre_exists (accs : List Acc) (hval : ∀ a ∈ accs, a.valid)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) (hlen : (items accs).length < 999999)
    (rate : Acc → Cat → Int) (hrate : ∀ a ∈ accs, ∀ c ∈ a.cats, (rate a c).natAbs < 1000000)
    (hkey : ∀ a ∈ accs, ∀ c ∈ a.cats, ∀ a' ∈ accs, ∀ c' ∈ a'.cats,
      a.grp = a'.grp → c.ty = c'.ty → c.cat = c'.cat → rate a c = rate a' c') :
    ∃ σ ca aa da acctOf rateOf, RunPre σ ca aa da acctOf rateOf (jcats accs) ∧
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
      have ed := discAt_unique hd' hd
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

#print axioms EquivLean.Demo.Cbact04c.runPre_exists
