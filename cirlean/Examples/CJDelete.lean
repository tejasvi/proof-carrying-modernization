import CIR
import Examples.Gen.CJDelete

/-!
  `cJSON_Delete` frees a whole item tree (`Examples/cpp/cjdelete.c`: cJSON
  1.7.19's item record and `cJSON_Delete`, with `free` for the
  `global_hooks.deallocate` call). The tree is a ghost `CJ` forest lying in
  memory (`CJForest m ts`, `CIR/Logic/CJTree.lean`): the function is called on
  the first item of the sibling list `ts`, walks it through `next`, and for
  each item first deletes its children (a recursive call), then frees its
  strings and the item itself.

  The proof is by induction on the number of items (the recursive call is on
  a smaller forest). The loop's invariant states its frame folded: the memory
  agrees with the caller's except on the blocks of the items freed so far
  (`MemAgree`). Each iteration first derives the facts about item `k` that the
  code reads from it (ground rewrite rules, cheap for symbolic execution); the
  frame obligations left by `cir_run` are closed by `cir_agree_step` (the
  frame moves from `k` to `k + 1`), `cir_wf` (well-formedness of memory),
  `CJForest.frame` (the recursive call's precondition) and `cir_refute_mem`
  (a path on which a `free` would find its block dead).

  Build: `lake build Examples.CJDelete` (about 5 minutes on one core).
-/

open CIR Gen.CJDelete

set_option maxHeartbeats 40000000

namespace Examples.CJDelete

/-- Every item of the forest, children included, is a `cJSON` record (the
type its members are read at: a scalar access to a block of another type can
be type-punned, `Mem.punnedAccess`). -/
def AllCJSON : List CJ → Prop
  | [] => True
  | .item _ rt _ _ _ _ _ _ child :: ts => rt = .record "cJSON" ∧ AllCJSON child ∧ AllCJSON ts

theorem AllCJSON.get : ∀ {ts : List CJ}, AllCJSON ts →
    ∀ j (hj : j < ts.length), ts[j].rt = .record "cJSON" ∧ AllCJSON ts[j].child := by
  intro ts
  induction ts with
  | nil => intro _ j hj; exact absurd hj (Nat.not_lt_zero _)
  | cons t ts ih =>
    intro h j hj
    cases t with
    | item b rt prev type vi vd vs st child =>
      simp only [AllCJSON] at h
      cases j with
      | zero => exact ⟨h.1, h.2.1⟩
      | succ j => exact ih h.2.2 j (by simp at hj; omega)

/-- `cJSON_Delete(item)` frees the sibling list starting at `item` and every
item's children and strings: no undefined behaviour, and only the forest's
blocks change. -/
theorem delete_spec : ∀ (n : Nat) (ts : List CJ) (m : Mem), CJ.forestSize ts < n → CJForest m ts →
    (CJ.forestBlocks ts).Nodup → m.WF → AllCJSON ts →
    Returns ctx "cJSON_Delete" [.ptr (listPtr (ts.map CJ.b) 0)] m (fun r m' => r = none ∧
      (∀ b, b ∉ CJ.forestBlocks ts → b < m.next → m'.blocks b = m.blocks b) ∧ m.next ≤ m'.next ∧
      m'.WF) := by
  intro n
  induction n with
  | zero => intro ts m hsz; exact absurd hsz (Nat.not_lt_zero _)
  | succ n ih =>
  intro ts m hsz hf hnd hwf hrec
  have hlt := CJForest.blocks_lt hf hwf
  have hndr := CJ.roots_nodup hnd
  obtain ⟨_, hb, hr, hc, ht, hv, hs, hk⟩ := hf
  cir_start
  cir_vcg
  cir_loop (fun (item : Ptr) (mem : Mem) => ∃ k, k ≤ ts.length ∧ item = listPtr (ts.map CJ.b) k ∧
      MemAgree mem m (fun b => b < m.next ∧ b ∉ CJ.forestBlocks (ts.take k)) ∧ m.next ≤ mem.next ∧
      mem.WF)
    (fun (item : Ptr) (mem : Mem) => ts.length - listIdx (ts.map CJ.b) item)
  · have hag := ‹MemAgree σ.mem m _›
    by_cases hkl : cirW_0 < ts.length
    · -- item `k` (`cirW_0`) and its blocks, in the current memory
      have cirH_lpk : listPtr (ts.map CJ.b) cirW_0 = .loc ts[cirW_0].b [] := by
        rw [listPtr_of_lt (by simpa using hkl)]; simp
      have hlk : ∀ b ∈ ts[cirW_0].blocks, b < m.next := fun b hb' => hlt b (CJ.mem_forestBlocks hkl hb')
      have hnk : ∀ b ∈ ts[cirW_0].blocks, b ∉ CJ.forestBlocks (ts.take cirW_0) :=
        fun b hb' => CJ.not_mem_take hnd hkl (Nat.le_refl _) hb'
      have cirH_ik : σ.mem.blocks ts[cirW_0].b =
          some ⟨.heap, true, ts[cirW_0].rt, cjRec (ts.map CJ.b) cirW_0 ts[cirW_0]⟩ :=
        (hag _ ⟨hlk _ (CJ.root_mem_blocks _), hnk _ (CJ.root_mem_blocks _)⟩).trans (hb _ hkl)
      have cirH_vk : ts[cirW_0].vs.isSome = true → σ.mem.blocks (oblk ts[cirW_0].vs) =
          some ⟨.heap, true, oty ts[cirW_0].vs, oval ts[cirW_0].vs⟩ := fun h =>
        (hag _ ⟨hlk _ (CJ.vs_mem_blocks h), hnk _ (CJ.vs_mem_blocks h)⟩).trans (hv _ hkl h)
      have cirH_sk : ts[cirW_0].st.isSome = true → σ.mem.blocks (oblk ts[cirW_0].st) =
          some ⟨.heap, true, oty ts[cirW_0].st, oval ts[cirW_0].st⟩ := fun h =>
        (hag _ ⟨hlk _ (CJ.st_mem_blocks h), hnk _ (CJ.st_mem_blocks h)⟩).trans (hs _ hkl h)
      have cirH_rk : bitwise true 32 (· &&& ·) ts[cirW_0].type 256 = 0 := hr _ hkl
      have cirH_ck : bitwise true 32 (· &&& ·) ts[cirW_0].type 512 = 0 := hc _ hkl
      have cirH_tyk := ht _ hkl
      -- its record type (its members are read at `cJSON`'s member types)
      have cirH_rtk : ts[cirW_0].rt = .record "cJSON" := (AllCJSON.get hrec cirW_0 hkl).1
      have hark : AllCJSON ts[cirW_0].child := (AllCJSON.get hrec cirW_0 hkl).2
      have hlt_i : ts[cirW_0].b < m.next := hlk _ (CJ.root_mem_blocks _)
      have hlt_v : oblk ts[cirW_0].vs < m.next := by
        by_cases h : ts[cirW_0].vs.isSome = true
        · exact hlk _ (CJ.vs_mem_blocks h)
        · have : ts[cirW_0].vs = none := by simpa using h
          rw [this]; simp only [oblk]; omega
      have hlt_s : oblk ts[cirW_0].st < m.next := by
        by_cases h : ts[cirW_0].st.isSome = true
        · exact hlk _ (CJ.st_mem_blocks h)
        · have : ts[cirW_0].st = none := by simpa using h
          rw [this]; simp only [oblk]; omega
      obtain ⟨hne_iv, hne_is, hne_sv⟩ := CJ.own_ne (CJ.item_nodup hnd hkl)
      -- its children, for the recursive call and the memory after it
      have hszk : CJ.forestSize ts[cirW_0].child < n := by
        have := CJ.child_forestSize_lt hkl; omega
      have hndk := CJ.child_nodup hnd hkl
      have hcl : ∀ b ∈ CJ.forestBlocks ts[cirW_0].child, b < m.next :=
        fun b hb' => hlk _ (CJ.child_mem_blocks hb')
      have hltc : ∀ j (h : j < ts[cirW_0].child.length), ts[cirW_0].child[j].b < m.next :=
        fun j h => hcl _ (CJ.mem_forestBlocks h (CJ.root_mem_blocks _))
      have hfk : CJForest σ.mem ts[cirW_0].child := CJForest.frame (hk _ hkl)
        (fun b hb' => hag b ⟨hcl b hb', hnk b (CJ.child_mem_blocks hb')⟩)
      have cirH_cb : ∀ j (h : j < ts[cirW_0].child.length), σ.mem.blocks ts[cirW_0].child[j].b =
          some ⟨.heap, true, ts[cirW_0].child[j].rt,
            cjRec (ts[cirW_0].child.map CJ.b) j ts[cirW_0].child[j]⟩ := by
        cases hfk with | mk _ hb' _ _ _ _ _ _ => exact hb'
      have hnm_i : ts[cirW_0].b ∉ CJ.forestBlocks ts[cirW_0].child := CJ.root_not_mem_child hnd _ hkl
      have hnm_v : ts[cirW_0].vs.isSome = true → oblk ts[cirW_0].vs ∉ CJ.forestBlocks ts[cirW_0].child :=
        CJ.vs_not_mem_child hnd _ hkl
      have hnm_s : ts[cirW_0].st.isSome = true → oblk ts[cirW_0].st ∉ CJ.forestBlocks ts[cirW_0].child :=
        CJ.st_not_mem_child hnd _ hkl
      have hnm_0 : m.next ∉ CJ.forestBlocks ts[cirW_0].child := fun h => by have := hcl _ h; omega
      have hnm_1 : m.next + 1 ∉ CJ.forestBlocks ts[cirW_0].child := fun h => by have := hcl _ h; omega
      -- the recursive call with its argument as computed: the first child's block
      have ih1 : ∀ (ts' : List CJ) (m' : Mem) (h : 0 < ts'.length), CJ.forestSize ts' < n →
          CJForest m' ts' → (CJ.forestBlocks ts').Nodup → m'.WF → AllCJSON ts' →
          Returns ctx "cJSON_Delete" [.ptr (.loc ts'[0].b [])] m' (fun r m'' => r = none ∧
            (∀ b, b ∉ CJ.forestBlocks ts' → b < m'.next → m''.blocks b = m'.blocks b) ∧
            m'.next ≤ m''.next ∧ m''.WF) := by
        intro ts' m' h h1 h2 h3 h4 h5
        have := ih ts' m' h1 h2 h3 h4 h5
        rwa [listPtr_of_lt (by simpa using h), List.getElem_map] at this
      -- the strings it owns, when present, are other blocks than the item and
      -- than each other (stated unconditionally per case, for the lookups after a
      -- `free`: the type-punning check of the next store reads the item's block)
      by_cases cirH_hvs : ts[cirW_0].vs.isSome = true <;>
        by_cases cirH_hss : ts[cirW_0].st.isSome = true
      all_goals (try have cirH_nev : ts[cirW_0].b ≠ oblk ts[cirW_0].vs := hne_iv cirH_hvs)
      all_goals (try have cirH_nes : ts[cirW_0].b ≠ oblk ts[cirW_0].st := hne_is cirH_hss)
      all_goals (try have cirH_nsv : oblk ts[cirW_0].st ≠ oblk ts[cirW_0].vs := hne_sv cirH_hvs cirH_hss)
      cir_run
      all_goals (try exact hark)
      all_goals (try cir_agree_step hkl hag)
      all_goals (try cir_wf)
      all_goals (try (refine CJForest.frame hfk (fun b hb => ?_)
                      simp only [upd_apply]
                      split <;> first | rfl | (have := hcl b hb; omega)))
      all_goals (try cir_refute_mem)
      all_goals (try cir_subst_nat)
      all_goals cir_close'
    · -- the end of the list
      have cirH_lpk : listPtr (ts.map CJ.b) cirW_0 = .null := listPtr_of_ge (by simpa using hkl)
      cir_run
      all_goals (try exact MemAgree.cj_done (by omega) hag ‹_› ‹_›)
      all_goals (try cir_wf)
      all_goals (try cir_subst_nat)
      all_goals cir_close'
  · -- the frame at loop entry: only the function's two stack slots are new
    cir_run
    all_goals (try (intro b hb; obtain ⟨hb1, -⟩ := hb; simp only [upd_apply]
                    (repeat' split) <;> first | rfl | omega))
    all_goals (try cir_wf)
    all_goals (try cir_subst_nat)
    all_goals cir_close'

/-- `cJSON_Delete` on any item forest in memory. -/
theorem delete_forest (ts : List CJ) (m : Mem) (hf : CJForest m ts) (hnd : (CJ.forestBlocks ts).Nodup)
    (hwf : m.WF) (hrec : AllCJSON ts) :
    Returns ctx "cJSON_Delete" [.ptr (listPtr (ts.map CJ.b) 0)] m (fun r m' => r = none ∧
      (∀ b, b ∉ CJ.forestBlocks ts → b < m.next → m'.blocks b = m.blocks b) ∧ m.next ≤ m'.next ∧
      m'.WF) :=
  delete_spec (CJ.forestSize ts + 1) ts m (Nat.lt_succ_self _) hf hnd hwf hrec

end Examples.CJDelete
