import CIR.Logic.Loops

/-!
  Trees of heap records linked like cJSON items, as specifications see them.

  `CJ` is a ghost copy of a cJSON item tree: each item's block, record type,
  member values, owned strings and children. `CJForest m ts` says that the
  sibling list `ts` lies in memory `m`: item `j`'s record links to item
  `j + 1` (`next`, `listPtr`) and to its first child (`child`), its `type` is
  an `int`, its strings are live heap blocks, and its children form such a
  list too. The facts are
  stated per item index (`∀ j (h : j < ts.length), m.blocks ts[j].b = …`), the
  form symbolic execution uses at the item it reads.
-/

namespace CIR

/-- A cJSON item as it lies in memory: block `b` of record type `rt`, members
`prev`, `type`, `valueint`, `valuedouble`, the strings it owns
(`valuestring`, `string`: block, type and value; `none` for null), and its
children. -/
inductive CJ where
  | item (b : Nat) (rt : Ty) (prev : Val) (type : Int) (vi vd : Val)
      (vs st : Option (Nat × Ty × Val)) (child : List CJ)

namespace CJ

def b : CJ → Nat | item b .. => b
def rt : CJ → Ty | item _ rt .. => rt
def prev : CJ → Val | item _ _ p .. => p
def type : CJ → Int | item _ _ _ t .. => t
def vi : CJ → Val | item _ _ _ _ v .. => v
def vd : CJ → Val | item _ _ _ _ _ v .. => v
def vs : CJ → Option (Nat × Ty × Val) | item _ _ _ _ _ _ s .. => s
def st : CJ → Option (Nat × Ty × Val) | item _ _ _ _ _ _ _ s _ => s
def child : CJ → List CJ | item _ _ _ _ _ _ _ _ c => c

mutual
/-- The blocks of an item: the item and its strings, and its children's. -/
def blocks : CJ → List Nat
  | item b _ _ _ _ _ vs st child =>
    b :: ((vs.map (·.1)).toList ++ (st.map (·.1)).toList ++ forestBlocks child)
/-- The blocks of a sibling list. -/
def forestBlocks : List CJ → List Nat
  | [] => []
  | t :: ts => blocks t ++ forestBlocks ts
end

mutual
/-- The number of items of a tree. -/
def size : CJ → Nat
  | item _ _ _ _ _ _ _ _ child => forestSize child + 1
def forestSize : List CJ → Nat
  | [] => 0
  | t :: ts => size t + forestSize ts
end

end CJ

/-- The block, type and value of an owned string (anything for none). -/
def oblk : Option (Nat × Ty × Val) → Nat
  | some (s, _, _) => s
  | none => 0
def oty : Option (Nat × Ty × Val) → Ty
  | some (_, t, _) => t
  | none => .void
def oval : Option (Nat × Ty × Val) → Val
  | some (_, _, v) => v
  | none => .undef

/-- A pointer to an owned string (`char*` to its block), or null. -/
def ostr (o : Option (Nat × Ty × Val)) : Ptr :=
  if o.isSome then .loc (oblk o) [.idx 0] else .null

/-- The members of item `t` at position `j` of a sibling list with blocks
`roots`: `next` points to the following sibling, `child` to its first child. -/
def cjFields (roots : List Nat) (j : Nat) (t : CJ) : List Val :=
  [.ptr (listPtr roots (j + 1)), t.prev, .ptr (listPtr (t.child.map CJ.b) 0), .int t.type,
    .ptr (ostr t.vs), t.vi, t.vd, .ptr (ostr t.st)]

/-- The record of item `t` at position `j` (its members stay folded in
symbolic states; `cjFields_get*` read one). -/
def cjRec (roots : List Nat) (j : Nat) (t : CJ) : Val := .agg (cjFields roots j t)

section
variable (roots : List Nat) (j : Nat) (t : CJ)
theorem cjFields_get0 : (cjFields roots j t)[0]? = some (.ptr (listPtr roots (j + 1))) := rfl
theorem cjFields_get1 : (cjFields roots j t)[1]? = some t.prev := rfl
theorem cjFields_get2 : (cjFields roots j t)[2]? = some (.ptr (listPtr (t.child.map CJ.b) 0)) := rfl
theorem cjFields_get3 : (cjFields roots j t)[3]? = some (.int t.type) := rfl
theorem cjFields_get4 : (cjFields roots j t)[4]? = some (.ptr (ostr t.vs)) := rfl
theorem cjFields_get5 : (cjFields roots j t)[5]? = some t.vi := rfl
theorem cjFields_get6 : (cjFields roots j t)[6]? = some t.vd := rfl
theorem cjFields_get7 : (cjFields roots j t)[7]? = some (.ptr (ostr t.st)) := rfl
theorem cjFields_length : (cjFields roots j t).length = 8 := rfl
end

/-- The sibling list `ts` lies in memory `m` (see the module comment); its
items own their children and strings (`type` has neither
`cJSON_IsReference` (256) nor `cJSON_StringIsConst` (512)). -/
inductive CJForest (m : Mem) : List CJ → Prop
  | mk (ts : List CJ)
      (hb : ∀ j (h : j < ts.length),
        m.blocks ts[j].b = some ⟨.heap, true, ts[j].rt, cjRec (ts.map CJ.b) j ts[j]⟩)
      (hr : ∀ j (h : j < ts.length), bitwise true 32 (· &&& ·) ts[j].type 256 = 0)
      (hc : ∀ j (h : j < ts.length), bitwise true 32 (· &&& ·) ts[j].type 512 = 0)
      (ht : ∀ j (h : j < ts.length), -2147483648 ≤ ts[j].type ∧ ts[j].type ≤ 2147483647)
      (hv : ∀ j (h : j < ts.length), ts[j].vs.isSome = true →
        m.blocks (oblk ts[j].vs) = some ⟨.heap, true, oty ts[j].vs, oval ts[j].vs⟩)
      (hs : ∀ j (h : j < ts.length), ts[j].st.isSome = true →
        m.blocks (oblk ts[j].st) = some ⟨.heap, true, oty ts[j].st, oval ts[j].st⟩)
      (hk : ∀ j (h : j < ts.length), CJForest m ts[j].child) :
      CJForest m ts

theorem CJ.mem_forestBlocks {ts : List CJ} {j : Nat} (h : j < ts.length) {b : Nat}
    (hb : b ∈ ts[j].blocks) : b ∈ CJ.forestBlocks ts := by
  induction ts generalizing j with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons t ts ih =>
    cases j with
    | zero => simp only [CJ.forestBlocks, List.mem_append]; exact Or.inl hb
    | succ j =>
      simp only [CJ.forestBlocks, List.mem_append]
      exact Or.inr (ih (by simp at h; omega) hb)

theorem CJ.root_mem_blocks (t : CJ) : t.b ∈ t.blocks := by
  cases t; simp [CJ.blocks, CJ.b]

theorem CJ.child_mem_blocks {t : CJ} {b : Nat} (h : b ∈ CJ.forestBlocks t.child) : b ∈ t.blocks := by
  cases t; simp only [CJ.blocks, CJ.child] at *; simp [h]

/-- The empty sibling list lies in any memory. -/
theorem CJForest.nil (m : Mem) : CJForest m [] :=
  CJForest.mk [] (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun _ h => absurd h (Nat.not_lt_zero _))

/-- The first item of a nonempty sibling list. -/
theorem CJForest.root {m : Mem} {ts : List CJ} (hf : CJForest m ts) (h : 0 < ts.length) :
    m.blocks ts[0].b = some ⟨.heap, true, ts[0].rt, cjRec (ts.map CJ.b) 0 ts[0]⟩ := by
  cases hf with
  | mk _ hb _ _ _ _ _ _ => exact hb 0 h

/-- A sibling list stays in memory when its blocks do not change. -/
theorem CJForest.frame {m m' : Mem} {ts : List CJ} (hf : CJForest m ts)
    (hsame : ∀ b ∈ CJ.forestBlocks ts, m'.blocks b = m.blocks b) : CJForest m' ts := by
  induction hf with
  | mk ts hb hr hc ht hv hs hk ih =>
    refine CJForest.mk ts ?_ hr hc ht ?_ ?_ ?_
    · intro j h
      rw [hsame _ (CJ.mem_forestBlocks h (CJ.root_mem_blocks _))]
      exact hb j h
    · intro j h hsome
      have hm : oblk ts[j].vs ∈ ts[j].blocks := by
        revert hsome; cases ts[j]; rename_i vs _ _
        cases vs <;> simp [CJ.blocks, CJ.vs, oblk]
      rw [hsame _ (CJ.mem_forestBlocks h hm)]
      exact hv j h hsome
    · intro j h hsome
      have hm : oblk ts[j].st ∈ ts[j].blocks := by
        revert hsome; cases ts[j]; rename_i st _
        cases st <;> simp [CJ.blocks, CJ.st, oblk]
      rw [hsame _ (CJ.mem_forestBlocks h hm)]
      exact hs j h hsome
    · intro j h
      exact ih j h fun b hb' => hsame b (CJ.mem_forestBlocks h (CJ.child_mem_blocks hb'))

/-! ### Disjointness from `(CJ.forestBlocks ts).Nodup` -/

theorem CJ.blocks_eq (t : CJ) :
    t.blocks = t.b :: ((t.vs.map (·.1)).toList ++ (t.st.map (·.1)).toList ++ CJ.forestBlocks t.child) := by
  cases t; simp [CJ.blocks, CJ.b, CJ.vs, CJ.st, CJ.child]

/-- The blocks of item `j` are a sublist of the forest's (with the items
before and after it on either side). -/
theorem CJ.forestBlocks_split {ts : List CJ} {j : Nat} (h : j < ts.length) :
    ∃ pre post, CJ.forestBlocks ts = pre ++ ts[j].blocks ++ post ∧
      (∀ j' (h' : j' < ts.length), j' ≠ j → ∀ b ∈ ts[j'].blocks, b ∈ pre ∨ b ∈ post) := by
  induction ts generalizing j with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons t ts ih =>
    cases j with
    | zero =>
      refine ⟨[], CJ.forestBlocks ts, by simp [CJ.forestBlocks], ?_⟩
      intro j' h' hne b hb
      obtain ⟨j'', rfl⟩ : ∃ j'', j' = j'' + 1 := ⟨j' - 1, by omega⟩
      exact Or.inr (CJ.mem_forestBlocks (by simp at h'; omega) (by simpa using hb))
    | succ j =>
      obtain ⟨pre, post, he, hother⟩ := ih (j := j) (by simp at h; omega)
      refine ⟨t.blocks ++ pre, post, by simp [CJ.forestBlocks, he], ?_⟩
      intro j' h' hne b hb
      cases j' with
      | zero => exact Or.inl (List.mem_append_left _ (by simpa using hb))
      | succ j'' =>
        rcases hother j'' (by simp at h'; omega) (by omega) b (by simpa using hb) with h1 | h1
        · exact Or.inl (List.mem_append_right _ h1)
        · exact Or.inr h1

/-- Distinct items of a forest have disjoint blocks. -/
theorem CJ.items_disjoint {ts : List CJ} (hnd : (CJ.forestBlocks ts).Nodup) {j j' : Nat}
    (h : j < ts.length) (h' : j' < ts.length) (hne : j' ≠ j) {b : Nat}
    (hb : b ∈ ts[j'].blocks) : b ∉ ts[j].blocks := by
  obtain ⟨pre, post, he, hother⟩ := CJ.forestBlocks_split h
  rw [he] at hnd
  intro hb2
  have hnd' := List.nodup_append.mp hnd
  have hnd'' := List.nodup_append.mp hnd'.1
  rcases hother j' h' hne b hb with h1 | h1
  · exact hnd''.2.2 b h1 b hb2 rfl
  · exact hnd'.2.2 b (List.mem_append_right _ hb2) b h1 rfl

/-- An item's own blocks: the item, its strings and its children's blocks
are distinct. -/
theorem CJ.item_nodup {ts : List CJ} (hnd : (CJ.forestBlocks ts).Nodup) {j : Nat} (h : j < ts.length) :
    ts[j].blocks.Nodup := by
  obtain ⟨pre, post, he, _⟩ := CJ.forestBlocks_split h
  rw [he] at hnd
  exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1

theorem CJ.root_not_mem_child {ts : List CJ} (hnd : (CJ.forestBlocks ts).Nodup) (j : Nat)
    (h : j < ts.length) : ts[j].b ∉ CJ.forestBlocks ts[j].child := by
  have hn := CJ.item_nodup hnd h
  rw [CJ.blocks_eq] at hn
  intro hm
  exact (List.nodup_cons.mp hn).1 (by simp [hm])

theorem CJ.vs_not_mem_child {ts : List CJ} (hnd : (CJ.forestBlocks ts).Nodup) (j : Nat)
    (h : j < ts.length) (hs : ts[j].vs.isSome = true) : oblk ts[j].vs ∉ CJ.forestBlocks ts[j].child := by
  have hn := CJ.item_nodup hnd h
  rw [CJ.blocks_eq] at hn
  have hn2 := (List.nodup_cons.mp hn).2
  revert hs hn2
  cases ts[j].vs with
  | none => simp
  | some x =>
    intro _ hn2 hm
    obtain ⟨s, ty, v⟩ := x
    have := List.nodup_append.mp hn2
    exact this.2.2 s (by simp) s hm rfl

theorem CJ.st_not_mem_child {ts : List CJ} (hnd : (CJ.forestBlocks ts).Nodup) (j : Nat)
    (h : j < ts.length) (hs : ts[j].st.isSome = true) : oblk ts[j].st ∉ CJ.forestBlocks ts[j].child := by
  have hn := CJ.item_nodup hnd h
  rw [CJ.blocks_eq] at hn
  have hn2 := (List.nodup_cons.mp hn).2
  revert hs hn2
  cases ts[j].st with
  | none => simp
  | some x =>
    intro _ hn2 hm
    obtain ⟨s, ty, v⟩ := x
    have := List.nodup_append.mp hn2
    exact this.2.2 s (by simp) s hm rfl

/-- Another item's blocks are not among an item's children's blocks. -/
theorem CJ.other_not_mem_child {ts : List CJ} (hnd : (CJ.forestBlocks ts).Nodup) (j : Nat)
    (h : j < ts.length) (j' : Nat) (h' : j' < ts.length) (hne : j' ≠ j) {b : Nat}
    (hb : b ∈ ts[j'].blocks) : b ∉ CJ.forestBlocks ts[j].child :=
  fun hm => CJ.items_disjoint hnd h h' hne hb (CJ.child_mem_blocks hm)

/-- In a well-formed memory, every block of a forest lies below `next`. -/
theorem CJForest.blocks_lt {m : Mem} {ts : List CJ} (hf : CJForest m ts) (hwf : m.WF) :
    ∀ b ∈ CJ.forestBlocks ts, b < m.next := by
  have lt_of (b : Nat) (v : MemBlock) (h : m.blocks b = some v) : b < m.next := by
    apply Nat.lt_of_not_le; intro hle; rw [hwf b hle] at h; cases h
  induction hf with
  | mk ts hb hr hc ht hv hs hk ih =>
    intro b hmem
    -- the item whose blocks contain `b`
    have : ∃ j, ∃ h : j < ts.length, b ∈ ts[j].blocks := by
      clear hb hr hc ht hv hs hk ih
      induction ts with
      | nil => simp [CJ.forestBlocks] at hmem
      | cons t ts ih' =>
        simp only [CJ.forestBlocks, List.mem_append] at hmem
        rcases hmem with h1 | h1
        · exact ⟨0, by simp, by simpa using h1⟩
        · obtain ⟨j, hj, hb'⟩ := ih' h1
          exact ⟨j + 1, by simp; omega, by simpa using hb'⟩
    obtain ⟨j, hj, hbj⟩ := this
    rw [CJ.blocks_eq] at hbj
    simp only [List.mem_cons, List.mem_append] at hbj
    rcases hbj with h1 | (h1 | h1) | h1
    · subst h1; exact lt_of _ _ (hb j hj)
    · revert h1 hv
      cases hvs : ts[j].vs with
      | none => simp
      | some x =>
        intro hv h1
        obtain ⟨s, ty, v⟩ := x
        have hbs : b = s := by simpa using h1
        subst hbs
        have := hv j hj (by simp [hvs])
        simp only [hvs, oblk] at this
        exact lt_of _ _ this
    · revert h1 hs
      cases hst : ts[j].st with
      | none => simp
      | some x =>
        intro hs h1
        obtain ⟨s, ty, v⟩ := x
        have hbs : b = s := by simpa using h1
        subst hbs
        have := hs j hj (by simp [hst])
        simp only [hst, oblk] at this
        exact lt_of _ _ this
    · exact ih j hj b h1

/-! ### Prefixes of a sibling list (the items a loop has passed) -/

theorem CJ.forestBlocks_append (ts us : List CJ) :
    CJ.forestBlocks (ts ++ us) = CJ.forestBlocks ts ++ CJ.forestBlocks us := by
  induction ts with
  | nil => simp [CJ.forestBlocks]
  | cons t ts ih => simp [CJ.forestBlocks, ih]

theorem CJ.forestBlocks_take_succ {ts : List CJ} {k : Nat} (h : k < ts.length) :
    CJ.forestBlocks (ts.take (k + 1)) = CJ.forestBlocks (ts.take k) ++ ts[k].blocks := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList, CJ.forestBlocks_append, CJ.forestBlocks, List.append_nil]

theorem CJ.exists_of_mem_forestBlocks {ts : List CJ} {b : Nat} (hm : b ∈ CJ.forestBlocks ts) :
    ∃ j, ∃ h : j < ts.length, b ∈ ts[j].blocks := by
  induction ts with
  | nil => simp [CJ.forestBlocks] at hm
  | cons t ts ih =>
    simp only [CJ.forestBlocks, List.mem_append] at hm
    rcases hm with h1 | h1
    · exact ⟨0, by simp, by simpa using h1⟩
    · obtain ⟨j, hj, hb'⟩ := ih h1
      exact ⟨j + 1, by simp; omega, by simpa using hb'⟩

theorem CJ.mem_forestBlocks_take {ts : List CJ} {k b : Nat} (hm : b ∈ CJ.forestBlocks (ts.take k)) :
    b ∈ CJ.forestBlocks ts := by
  have := congrArg CJ.forestBlocks (List.take_append_drop k ts)
  rw [← this, CJ.forestBlocks_append]
  exact List.mem_append_left _ hm

/-- The blocks of item `j` are not among those of the items before `k ≤ j`. -/
theorem CJ.not_mem_take {ts : List CJ} (hnd : (CJ.forestBlocks ts).Nodup) {j k : Nat}
    (h : j < ts.length) (hjk : k ≤ j) {b : Nat} (hb : b ∈ ts[j].blocks) :
    b ∉ CJ.forestBlocks (ts.take k) := by
  intro hm
  obtain ⟨j', hj', hb'⟩ := CJ.exists_of_mem_forestBlocks hm
  simp only [List.length_take] at hj'
  simp only [List.getElem_take] at hb'
  exact CJ.items_disjoint hnd h (by omega) (by omega) hb' hb

theorem CJ.vs_mem_blocks {t : CJ} (h : t.vs.isSome = true) : oblk t.vs ∈ t.blocks := by
  revert h; cases t; rename_i vs _ _; cases vs <;> simp [CJ.blocks, CJ.vs, oblk]

theorem CJ.st_mem_blocks {t : CJ} (h : t.st.isSome = true) : oblk t.st ∈ t.blocks := by
  revert h; cases t; rename_i st _; cases st <;> simp [CJ.blocks, CJ.st, oblk]

theorem CJ.child_forestSize_lt {ts : List CJ} {j : Nat} (h : j < ts.length) :
    CJ.forestSize ts[j].child < CJ.forestSize ts := by
  induction ts generalizing j with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons t ts ih =>
    cases j with
    | zero => cases t; simp [CJ.forestSize, CJ.size, CJ.child]; omega
    | succ j =>
      have := ih (j := j) (by simp at h; omega)
      simp only [CJ.forestSize, List.getElem_cons_succ] at this ⊢
      omega

theorem CJ.child_nodup {ts : List CJ} (hnd : (CJ.forestBlocks ts).Nodup) {j : Nat} (h : j < ts.length) :
    (CJ.forestBlocks ts[j].child).Nodup := by
  have hn := CJ.item_nodup hnd h
  rw [CJ.blocks_eq] at hn
  exact (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1

theorem CJ.roots_nodup {ts : List CJ} (hnd : (CJ.forestBlocks ts).Nodup) : (ts.map CJ.b).Nodup := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [CJ.forestBlocks] at hnd
    have h3 := List.nodup_append.mp hnd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih h3.2.1⟩
    intro hm
    obtain ⟨u, hu, hub⟩ := List.mem_map.mp hm
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
    exact h3.2.2 t.b (CJ.root_mem_blocks t) _ (CJ.mem_forestBlocks hj (CJ.root_mem_blocks _)) hub.symm

/-- The blocks an item does not own: the item, its strings and its children. -/
theorem CJ.not_mem_blocks {t : CJ} {b : Nat} (h : b ∉ t.blocks) :
    b ≠ t.b ∧ (t.vs.isSome = true → b ≠ oblk t.vs) ∧ (t.st.isSome = true → b ≠ oblk t.st) ∧
      b ∉ CJ.forestBlocks t.child :=
  ⟨fun e => h (e ▸ CJ.root_mem_blocks _), fun hs e => h (e ▸ CJ.vs_mem_blocks hs),
   fun hs e => h (e ▸ CJ.st_mem_blocks hs), fun hm => h (CJ.child_mem_blocks hm)⟩

/-- The frame of a loop that frees the items of a sibling list in order: the
memory agrees with the caller's `m` except on the blocks of the items freed so
far. An iteration that changes only item `k`'s blocks moves it to `k + 1`. -/
theorem MemAgree.cj_step {m mem mem' : Mem} {ts : List CJ} {k : Nat} (hkl : k < ts.length)
    (hag : MemAgree mem m (fun b => b < m.next ∧ b ∉ CJ.forestBlocks (ts.take k)))
    (hstep : ∀ b, b < m.next → b ∉ ts[k].blocks → mem'.blocks b = mem.blocks b) :
    MemAgree mem' m (fun b => b < m.next ∧ b ∉ CJ.forestBlocks (ts.take (k + 1))) := by
  intro b ⟨hb1, hb2⟩
  rw [CJ.forestBlocks_take_succ hkl, List.mem_append, not_or] at hb2
  rw [hstep b hb1 hb2.2]
  exact hag b ⟨hb1, hb2.1⟩

/-- The frame at the end of such a loop: only the list's blocks changed. -/
theorem MemAgree.cj_done {m mem : Mem} {ts : List CJ} {k : Nat} (hk : ts.length ≤ k)
    (hag : MemAgree mem m (fun b => b < m.next ∧ b ∉ CJ.forestBlocks (ts.take k))) {b : Nat}
    (hb1 : b ∉ CJ.forestBlocks ts) (hb2 : b < m.next) : mem.blocks b = m.blocks b :=
  hag b ⟨hb2, by rwa [List.take_of_length_le hk]⟩

/-- An item's own blocks are distinct: the item, its value string, its key. -/
theorem CJ.own_ne {t : CJ} (hn : t.blocks.Nodup) :
    (t.vs.isSome = true → ¬t.b = oblk t.vs) ∧ (t.st.isSome = true → ¬t.b = oblk t.st) ∧
      (t.vs.isSome = true → t.st.isSome = true → ¬oblk t.st = oblk t.vs) := by
  cases t with
  | item b rt prev type vi vd vs st child =>
    simp only [CJ.blocks, CJ.b, CJ.vs, CJ.st] at hn ⊢
    cases vs with
    | none => cases st with
      | none => simp
      | some y => obtain ⟨s2, _, _⟩ := y; simp_all [oblk]
    | some x =>
      obtain ⟨s1, _, _⟩ := x
      cases st with
      | none => simp_all [oblk]
      | some y =>
        obtain ⟨s2, _, _⟩ := y
        simp only [Option.map_some, Option.toList_some, List.cons_append, List.nil_append,
          List.nodup_cons, List.mem_cons, List.mem_append, not_or] at hn
        simp only [oblk, Option.isSome_some, forall_const]
        omega

/-! ### Appending an item (a loop that builds a list, as cJSON's `parse_array`) -/

theorem listPtr_append_lt {bs : List Nat} {x k : Nat} (h : k < bs.length) :
    listPtr (bs ++ [x]) k = listPtr bs k := by
  unfold listPtr
  have h' : k < (bs ++ [x]).length := by simp; omega
  simp only [h, h', dite_true, List.getElem_append_left h]

theorem listPtr_append_self (bs : List Nat) (x : Nat) : listPtr (bs ++ [x]) bs.length = .loc x [] := by
  simp [listPtr]

theorem listPtr_append_succ_self (bs : List Nat) (x : Nat) : listPtr (bs ++ [x]) (bs.length + 1) = .null := by
  simp [listPtr]

/-- The records of the items before the last one do not change when an item is appended. -/
theorem cjFields_append {roots : List Nat} {x j : Nat} (t : CJ) (h : j + 1 < roots.length) :
    cjFields (roots ++ [x]) j t = cjFields roots j t := by
  simp only [cjFields, listPtr_append_lt h]

/-- Writing `next` of a record (member 0) to the pointer to the following item of `roots'`. -/
theorem cjFields_set_next (roots roots' : List Nat) (j : Nat) (t : CJ) :
    (cjFields roots j t).set 0 (.ptr (listPtr roots' (j + 1))) = cjFields roots' j t := by
  simp [cjFields]

/-- An item's blocks other than its root are not the root of another item. -/
theorem CJ.ne_root_of_mem {ts : List CJ} (hnd : (CJ.forestBlocks ts).Nodup) {j k : Nat}
    (hj : j < ts.length) (hk : k < ts.length) {b : Nat} (hb : b ∈ ts[j].blocks)
    (hne : j ≠ k ∨ b ≠ ts[j].b) : b ≠ ts[k].b := by
  intro e
  subst e
  rcases hne with hne | hne
  · exact CJ.items_disjoint hnd hj hk (Ne.symm hne) (CJ.root_mem_blocks _) hb
  · by_cases hjk : j = k
    · subst hjk; exact hne rfl
    · exact CJ.items_disjoint hnd hj hk (Ne.symm hjk) (CJ.root_mem_blocks _) hb

/-- Appending an item to a sibling list in memory (a loop that builds a list, as cJSON's
`parse_array`): the new item's block holds its record, the old last item's record links to
it, and the other blocks of the list did not change. -/
theorem CJForest.snoc {m m' : Mem} {ts : List CJ} {t : CJ} (hf : CJForest m ts)
    (hnd : (CJ.forestBlocks ts).Nodup)
    (hsame : ∀ b ∈ CJ.forestBlocks ts, (∀ h : 0 < ts.length, b ≠ ts[ts.length - 1].b) →
      m'.blocks b = m.blocks b)
    (hlast : ∀ h : 0 < ts.length, m'.blocks ts[ts.length - 1].b =
      some ⟨.heap, true, ts[ts.length - 1].rt,
        cjRec (ts.map CJ.b ++ [t.b]) (ts.length - 1) ts[ts.length - 1]⟩)
    (hnew : m'.blocks t.b = some ⟨.heap, true, t.rt, cjRec (ts.map CJ.b ++ [t.b]) ts.length t⟩)
    (hr : bitwise true 32 (· &&& ·) t.type 256 = 0) (hc : bitwise true 32 (· &&& ·) t.type 512 = 0)
    (ht : -2147483648 ≤ t.type ∧ t.type ≤ 2147483647)
    (hv : t.vs = none) (hs : t.st = none) (hk : t.child = []) :
    CJForest m' (ts ++ [t]) := by
  -- the other blocks of item `j`: unchanged unless it is the last root
  have other : ∀ j (hj : j < ts.length) b, b ∈ ts[j].blocks → (j ≠ ts.length - 1 ∨ b ≠ ts[j].b) →
      m'.blocks b = m.blocks b := fun j hj b hb hne =>
    hsame b (CJ.mem_forestBlocks hj hb) fun h =>
      CJ.ne_root_of_mem hnd hj (by omega) hb hne
  cases hf with
  | mk _ hb hr0 hc0 ht0 hv0 hs0 hk0 =>
  have hmap : (ts ++ [t]).map CJ.b = ts.map CJ.b ++ [t.b] := by simp
  refine CJForest.mk _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    rw [hmap]
    by_cases hj1 : j < ts.length
    · simp only [List.getElem_append_left hj1]
      by_cases hj2 : j = ts.length - 1
      · subst hj2; exact hlast (by omega)
      · rw [other j hj1 _ (CJ.root_mem_blocks _) (Or.inl hj2), hb j hj1]
        have hfj : cjFields (ts.map CJ.b ++ [t.b]) j ts[j] = cjFields (ts.map CJ.b) j ts[j] :=
          cjFields_append ts[j] (by simp; omega)
        simp only [cjRec, hfj]
    · have hj3 : j = ts.length := by omega
      subst hj3
      simpa using hnew
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hj1 : j < ts.length
    · simpa [List.getElem_append_left hj1] using hr0 j hj1
    · have hj3 : j = ts.length := by omega
      subst hj3; simpa using hr
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hj1 : j < ts.length
    · simpa [List.getElem_append_left hj1] using hc0 j hj1
    · have hj3 : j = ts.length := by omega
      subst hj3; simpa using hc
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hj1 : j < ts.length
    · simpa [List.getElem_append_left hj1] using ht0 j hj1
    · have hj3 : j = ts.length := by omega
      subst hj3; simpa using ht
  · intro j hj hsome
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hj1 : j < ts.length
    · simp only [List.getElem_append_left hj1] at hsome ⊢
      have hm := CJ.vs_mem_blocks hsome
      rw [other j hj1 _ hm (Or.inr (fun e => (CJ.own_ne (CJ.item_nodup hnd hj1)).1 hsome e.symm))]
      exact hv0 j hj1 hsome
    · have hj3 : j = ts.length := by omega
      subst hj3; simp [hv] at hsome
  · intro j hj hsome
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hj1 : j < ts.length
    · simp only [List.getElem_append_left hj1] at hsome ⊢
      have hm := CJ.st_mem_blocks hsome
      rw [other j hj1 _ hm (Or.inr (fun e => (CJ.own_ne (CJ.item_nodup hnd hj1)).2.1 hsome e.symm))]
      exact hs0 j hj1 hsome
    · have hj3 : j = ts.length := by omega
      subst hj3; simp [hs] at hsome
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hj1 : j < ts.length
    · simp only [List.getElem_append_left hj1]
      refine CJForest.frame (hk0 j hj1) (fun b hb' => other j hj1 b (CJ.child_mem_blocks hb') (Or.inr ?_))
      intro e; subst e
      exact CJ.root_not_mem_child hnd j hj1 hb'
    · have hj3 : j = ts.length := by omega
      subst hj3
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero, hk]
      exact CJForest.mk [] (fun _ h => absurd h (by simp)) (fun _ h => absurd h (by simp))
        (fun _ h => absurd h (by simp)) (fun _ h => absurd h (by simp)) (fun _ h => absurd h (by simp))
        (fun _ h => absurd h (by simp)) (fun _ h => absurd h (by simp))

end CIR
