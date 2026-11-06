import CIR
import Examples.Gen.CJAppend

/-!
  Building a list of cJSON items (`Examples/cpp/cjappend.c`: cJSON 1.7.19's
  item record, `cJSON_New_Item` with `malloc` for the allocate hook, and the
  list building of `parse_array`: each new item is appended at the tail, the
  old tail's `next` and the new item's `prev` linked).

  The loop's invariant names the items built so far as a ghost list `ts`
  (`CJForest mem ts`: they lie in memory as a sibling list), with `head` and
  `current_item` the pointers to its first and last items, all blocks fresh
  and distinct, and the caller's memory unchanged (`MemAgree`). An iteration
  appends one item: the new list is `ts ++ [t]` (`CJForest.snoc`), where `t`
  is the zeroed item `cJSON_New_Item` returns with the members the loop
  writes. Each iteration first derives the facts about the items it reads;
  the obligations of the new list are memory lookups through the iteration's
  writes (`cir_simp_frame`).

  Build: `lake build Examples.CJAppend` (not in `Examples.lean`).
-/

open CIR Gen.CJAppend

set_option maxHeartbeats 100000000

namespace Examples.CJAppend

/-- `build_array(item, n)` builds `n` items in a loop that appends each at the
tail of the list: no undefined behaviour. -/
theorem build_array_spec (ib : Nat) (iv : List Val) (n : Int) (m : Mem)
    (hn : 0 ≤ n ∧ n < 2147483647) (hib : ib < m.next)
    (hiv : m.blocks ib = some ⟨.heap, true, .record "cJSON", .agg iv⟩) (hivl : iv.length = 8)
    (hwf : m.WF) :
    Returns ctx "build_array" [.ptr (.loc ib []), .int n] m (fun r _ => r = some (.int 1)) := by
  cir_start
  cir_vcg
  cir_loop (fun (i : Int) (head current_item : Ptr) (mem : Mem) => ∃ ts : List CJ,
      ts.length = i.toNat ∧ 0 ≤ i ∧ i ≤ n ∧
      head = listPtr (ts.map CJ.b) 0 ∧ current_item = listPtr (ts.map CJ.b) (ts.length - 1) ∧
      CJForest mem ts ∧ (CJ.forestBlocks ts).Nodup ∧
      (∀ j (h : j < ts.length), ts[j].child = [] ∧ ts[j].vs = none ∧ ts[j].st = none) ∧
      (∀ b ∈ CJ.forestBlocks ts, m.next + 6 ≤ b ∧ b < mem.next) ∧
      MemAgree mem m (fun b => b < m.next) ∧ m.next ≤ mem.next ∧ mem.WF ∧
      (∀ j (h : j < ts.length), ts[j].rt = .record "cJSON"))
    (fun (i : Int) (head current_item : Ptr) (mem : Mem) => n - i)
  · -- the items built so far (`cirW_0`) and the caller's item, in the current memory
    have cirH_items : ∀ j (h : j < cirW_0.length), σ.mem.blocks cirW_0[j].b =
        some ⟨.heap, true, cirW_0[j].rt, cjRec (cirW_0.map CJ.b) j cirW_0[j]⟩ := by
      cases cirU_12 with | mk _ hb _ _ _ _ _ _ => exact hb
    have cirH_ib : σ.mem.blocks ib = some ⟨.heap, true, .record "cJSON", .agg iv⟩ :=
      (cirU_20 ib hib).trans hiv
    have hfresh : ∀ j (h : j < cirW_0.length), m.next + 6 ≤ cirW_0[j].b ∧ cirW_0[j].b < σ.mem.next :=
      fun j h => cirU_18 _ (CJ.mem_forestBlocks h (CJ.root_mem_blocks _))
    -- the items' record type (accesses to their members are not type-punned)
    have cirH_rt : ∀ j (h : j < cirW_0.length), cirW_0[j].rt = .record "cJSON" := by assumption
    cir_run
    all_goals (try ((try cir_subst_nat); cir_close'))
    have hnb : ∀ b ∈ CJ.forestBlocks cirW_0, b < σ.mem.next := fun b hb' => (cirU_18 b hb').2
    have hnb6 : ∀ b ∈ CJ.forestBlocks cirW_0, m.next + 6 ≤ b := fun b hb' => (cirU_18 b hb').1
    -- the invariant at `i + 1`: the list with the new item (block `σ.mem.next + 3`) appended
    all_goals first
      | -- a nonempty list: the old tail links to the new item
        (refine ⟨cirW_0 ++ [CJ.item (σ.mem.next + 3) (.record "cJSON")
            (.ptr (.loc cirW_0[cirW_0.length - 1].b [])) 8 (.int i) (.float 0) none none []], ?_⟩
         have hl : 0 < cirW_0.length := by assumption
         have htl := hfresh (cirW_0.length - 1) (by omega)
         cir_strip_mdata
         refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
         · simp; omega
         · omega
         · omega
         · rw [List.map_append, List.map_singleton, listPtr_append_lt (by simpa using hl),
             listPtr_of_lt (by simpa using hl)]; simp
         · simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel,
             List.map_append, List.map_singleton]
           have h1 := listPtr_append_self (cirW_0.map CJ.b) (σ.mem.next + 3)
           simp only [List.length_map] at h1
           exact h1.symm
         · apply CJForest.snoc cirU_12 cirU_14
           · intro b hb hne
             have cirH_h1 := hnb b hb
             have cirH_h2 := hnb6 b hb
             have cirH_h3 := hne hl
             cir_simp_frame
           · intro h
             cir_simp_frame
             rw [show Ptr.loc (σ.mem.next + 3) [] =
                 listPtr (cirW_0.map CJ.b ++ [σ.mem.next + 3]) (cirW_0.length - 1 + 1) by
               rw [Nat.sub_add_cancel hl]
               have h1 := listPtr_append_self (cirW_0.map CJ.b) (σ.mem.next + 3)
               simp only [List.length_map] at h1
               exact h1.symm, cjFields_set_next, cirH_rt (cirW_0.length - 1) (by omega)]
             try rfl
           · simp (config := { maxSteps := 4000000 }) (disch := first | assumption | omega)
               only [CJ.b, upd_apply, ite_neg', ↓reduceIte]
             simp [cjRec, cjFields, listPtr, ostr, CJ.rt, CJ.prev, CJ.type, CJ.vi, CJ.vd,
               CJ.vs, CJ.st, CJ.child]
           all_goals first | rfl | (simp only [CJ.type]; decide)
         · rw [CJ.forestBlocks_append, List.nodup_append]
           refine ⟨cirU_14, by simp [CJ.forestBlocks, CJ.blocks], ?_⟩
           intro a ha b hb
           simp [CJ.forestBlocks, CJ.blocks] at hb
           have := hnb a ha
           omega
         · intro j h
           by_cases hj : j < cirW_0.length
           · simp only [List.getElem_append_left hj]; exact cirU_16 j hj
           · have hj' : j = cirW_0.length := by simp at h; omega
             subst hj'
             simp [CJ.child, CJ.vs, CJ.st]
         · intro b hb
           rw [CJ.forestBlocks_append] at hb
           simp [CJ.forestBlocks, CJ.blocks] at hb
           rcases hb with hb | hb
           · have := hnb b hb; have := hnb6 b hb; omega
           · omega
         · intro b hb
           have cirH_h4 : b < m.next := hb
           cir_simp_frame
           exact cirU_20 b hb
         · first | omega | (simp only; omega)
         · refine Mem.WF_of_frame cirU_24 (by simp only; omega) (fun b hb => ?_)
           have cirH_hb : σ.mem.next + 4 ≤ b := by simpa using hb
           cir_simp_frame
         · intro j h
           by_cases hj : j < cirW_0.length
           · simp only [List.getElem_append_left hj]; exact cirH_rt j hj
           · have hj' : j = cirW_0.length := by simp at h; omega
             subst hj'
             simp [CJ.rt])
      | -- the empty list: the new item is the head
        (have h0 : cirW_0 = [] := List.eq_nil_of_length_eq_zero (by omega)
         subst h0
         refine ⟨[CJ.item (σ.mem.next + 3) (.record "cJSON") (.ptr .null) 8 (.int i) (.float 0) none none []], ?_⟩
         cir_strip_mdata
         refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
         · simp; omega
         · omega
         · omega
         · simp [listPtr, CJ.b]
         · simp [listPtr, CJ.b]
         · apply CJForest.snoc (ts := []) cirU_12 cirU_14
           · intro b hb; simp [CJ.forestBlocks] at hb
           · intro h; simp at h
           · simp (config := { maxSteps := 4000000 }) (disch := first | assumption | omega)
               only [upd_apply, ite_neg', ↓reduceIte, CJ.b]
             simp [cjRec, cjFields, listPtr, ostr, CJ.rt, CJ.prev, CJ.type, CJ.vi, CJ.vd,
               CJ.vs, CJ.st, CJ.child]
           all_goals first | rfl | (simp only [CJ.type]; decide)
         · simp [CJ.forestBlocks, CJ.blocks]
         · intro j h; simp at h; subst h; simp [CJ.child, CJ.vs, CJ.st]
         · intro b hb; simp [CJ.forestBlocks, CJ.blocks] at hb; subst hb; constructor <;> omega
         · intro b hb
           have cirH_h4 : b < m.next := hb
           cir_simp_frame
           exact cirU_20 b hb
         · first | omega | (simp only; omega)
         · refine Mem.WF_of_frame cirU_24 (by simp only; omega) (fun b hb => ?_)
           have cirH_hb : σ.mem.next + 4 ≤ b := by simpa using hb
           cir_simp_frame
         · intro j h; simp at h; subst h; simp [CJ.rt])
  · -- loop entry: the empty list
    cir_run
    all_goals (try ((try cir_subst_nat); cir_close'))
    all_goals first
      | (refine ⟨[], ?_⟩
         try subst σ₀
         cir_strip_mdata
         repeat' apply And.intro
         all_goals first
           | rfl
           | omega
           | (simp [listPtr]; done)
           | exact CJForest.nil _
           | (simp [CJ.forestBlocks]; done)
           | (intro j h; simp at h; done)
           | (intro b hb; simp [CJ.forestBlocks] at hb; done)
           | (simp only; omega)
           | (intro b hb
              have cirH_hb : b < m.next := hb
              cir_simp_frame; done)
           | (refine Mem.WF_of_frame hwf (by simp only; omega) (fun b hb => ?_)
              have cirH_hb : m.next + 6 ≤ b := by simpa using hb
              cir_simp_frame; done))

end Examples.CJAppend
