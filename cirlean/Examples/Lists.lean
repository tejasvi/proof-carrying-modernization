import CIR
import Examples.Gen.Lists

/-!
  Loops over a linked list (`Examples/cpp/lists.c`). The list is given by its
  nodes' blocks in order, `bs` (distinct: `bs.Nodup`); `listPtr bs k` is the
  pointer to node `k` (null past the end), and the facts about the nodes are
  quantified over the index (`∀ k (h : k < bs.length), m.blocks bs[k] = …`),
  which symbolic execution uses at the node it reads.
  * `(p : Ptr)` names the loop's pointer variable by its value; the
    invariant locates it in the list, `∃ k, p = listPtr bs k`.
  * `(mem : Mem)` names the memory at the loop head, for loops that change
    the caller's blocks (`free_list` frees them); the invariant then
    describes them, and the loop's frame covers only the function's own
    blocks. The variant `bs.length - listIdx bs p` counts the nodes left.
-/

open CIR Gen.Lists

set_option maxHeartbeats 4000000

namespace Examples.Lists

/-- `list_len` counts the nodes of a list of distinct heap blocks `bs`. -/
theorem list_len_spec (bs : List Nat) (vals : Nat → Int) (m : Mem)
    (hlen : bs.length < 2147483647)
    (hlt : ∀ k (h : k < bs.length), bs[k] < m.next)
    (hch : ∀ k (h : k < bs.length), m.blocks bs[k] =
      some ⟨.heap, true, .record "node", .agg [.ptr (listPtr bs (k + 1)), .int (vals k)]⟩) :
    Returns ctx "list_len" [.ptr (listPtr bs 0)] m (fun r _ => r = some (.int bs.length)) := by
  cir_start
  cir_vcg
  cir_loop (fun (p : Ptr) n => ∃ k, k ≤ bs.length ∧ p = listPtr bs k ∧ n = k) (fun (p : Ptr) n => bs.length - n)
  all_goals cir_vcg

/-- `free_list` frees every node of a list of distinct heap blocks `bs`. -/
theorem free_list_spec (bs : List Nat) (vals : Nat → Int) (m : Mem) (hnd : bs.Nodup)
    (hlt : ∀ k (h : k < bs.length), bs[k] < m.next)
    (hch : ∀ k (h : k < bs.length), m.blocks bs[k] =
      some ⟨.heap, true, .record "node", .agg [.ptr (listPtr bs (k + 1)), .int (vals k)]⟩) :
    Returns ctx "free_list" [.ptr (listPtr bs 0)] m (fun r m' => r = none ∧
      ∀ k (h : k < bs.length), m'.blocks bs[k] =
        some ⟨.heap, false, .record "node", .agg [.ptr (listPtr bs (k + 1)), .int (vals k)]⟩) := by
  cir_start
  cir_vcg
  cir_loop (fun (p : Ptr) (mem : Mem) => ∃ k, k ≤ bs.length ∧ p = listPtr bs k ∧
      (∀ j (h : j < bs.length), k ≤ j → mem.blocks bs[j] = m.blocks bs[j]) ∧
      (∀ j (h : j < bs.length), j < k → mem.blocks bs[j] =
        some ⟨.heap, false, .record "node", .agg [.ptr (listPtr bs (j + 1)), .int (vals j)]⟩))
    (fun (p : Ptr) (mem : Mem) => bs.length - listIdx bs p)
  all_goals cir_vcg

end Examples.Lists
