import EquivLean.Modernize.Cbstm03a.Java.Iface2

/-!
# CBSTM03A → Java, table memory: geometry and texts

The slot of a position, the canonical memory of a slots array (`slotsMem`), `memRd`/`memWr` piece by piece.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Mem

/-- Every position below `MEM_SZ` lies in its slot, one of the 561. -/
theorem slotIdx_spec (j : Nat) (h : j < 171156) :
    slotIdx j < 561 ∧ slotSt (slotIdx j) ≤ j ∧ j < slotSt (slotIdx j) + slotLn (slotIdx j) := by
  unfold slotIdx slotSt slotLn
  split_ifs <;> omega

/-- A position inside slot `i` belongs to slot `i`. -/
theorem slotIdx_of_mem (i j : Nat) (hi : i < 561) (h1 : slotSt i ≤ j) (h2 : j < slotSt i + slotLn i) :
    slotIdx j = i := by
  unfold slotIdx slotSt slotLn at *
  split_ifs at * <;> omega

theorem slot_end_le (i : Nat) (hi : i < 561) : slotSt i + slotLn i ≤ 171156 := by
  unfold slotSt slotLn
  split_ifs <;> omega

theorem slotLn_le (i : Nat) : slotLn i ≤ 334 := by
  unfold slotLn; split_ifs <;> omega

theorem slotLn_pos (i : Nat) : 0 < slotLn i := by
  unfold slotLn; split_ifs <;> omega

/-- The character at position `j` of the memory the slots `vs` hold in `σ` (spaces for `null`). -/
def slotsMem (σ : State) (vs : List Value) (j : Nat) : JChar :=
  match vs[slotIdx j]? with
  | some (.ref x) =>
    match σ.heap x with
    | some (.str t) => t.getD (j - slotSt (slotIdx j)) space
    | _ => space
  | _ => space

/-- A memory the slots hold agrees with the canonical one below `MEM_SZ`. -/
theorem slotsAt_eq_slotsMem {σ : State} {a : Addr} {m : Nat → JChar} {vs : List Value}
    (h : SlotsAt σ a m) (ha : σ.heap a = some (.array (.cls "java.lang.String") vs)) (j : Nat) (hj : j < 171156) :
    m j = slotsMem σ vs j := by
  obtain ⟨vs', ha', -, hs⟩ := h
  rw [ha] at ha'
  cases ha'
  obtain ⟨hi, h1, h2⟩ := slotIdx_spec j hj
  have hw : j = slotSt (slotIdx j) + (j - slotSt (slotIdx j)) := by omega
  rcases hs (slotIdx j) hi with ⟨hn, hm⟩ | ⟨x, t, hx, hxt, -, hm⟩
  · rw [hw, hm _ (by omega), ← hw]
    unfold slotsMem
    rw [hn]
  · rw [hw, hm _ (by omega), ← hw]
    unfold slotsMem
    rw [hx]
    simp only [hxt]

/-- `memRd` over the natural offsets. -/
theorem memRd_eq (m : Nat → JChar) (off : Int) (n : Nat) : memRd m off n = (List.range n).map (fun i : Nat =>
    if 0 ≤ off + (i : Int) ∧ off + (i : Int) < 171156 then m (off + (i : Int)).toNat else space) := by
  unfold memRd
  simp only [bind_pure_comp, Functor.map, List.map_map]
  rfl

/-- `memRd` agrees for memories that agree below `MEM_SZ`. -/
theorem memRd_congr {m m' : Nat → JChar} (h : ∀ j, j < 171156 → m j = m' j) (off : Int) (n : Nat) :
    memRd m off n = memRd m' off n := by
  rw [memRd_eq, memRd_eq]
  apply List.map_congr_left
  intro i _
  split
  · rw [h _ (by omega)]
  · rfl

theorem memRd_zero (m : Nat → JChar) (off : Int) : memRd m off 0 = [] := by simp [memRd_eq]

theorem memRd_length (m : Nat → JChar) (off : Int) (n : Nat) : (memRd m off n).length = n := by
  simp [memRd_eq]

/-- `memRd` piece by piece: the next `k` characters. -/
theorem memRd_add (m : Nat → JChar) (off : Int) (p k : Nat) :
    memRd m off (p + k) = memRd m off p ++
      (List.range k).map (fun w => if 0 ≤ off + (p + w : Nat) ∧ off + (p + w : Nat) < 171156 then
        m (off + (p + w : Nat)).toNat else space) := by
  rw [memRd_eq, memRd_eq]
  rw [List.range_add, List.map_append, List.map_map]
  rfl

/-- The next `k` characters, all outside the memory: spaces. -/
theorem memRd_add_out (m : Nat → JChar) (off : Int) (p k : Nat)
    (h : off + (p + k : Nat) ≤ 0 ∨ 171156 ≤ off + p) :
    memRd m off (p + k) = memRd m off p ++ List.replicate k space := by
  rw [memRd_add]
  congr 1
  apply List.ext_getElem (by simp)
  intro w h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  simp at h1
  split
  · omega
  · rfl

/-- The next `k` characters, inside slot `i` from offset `w0`: the slot's characters. -/
theorem memRd_add_slot (σ : State) (vs : List Value) (off : Int) (p k i w0 : Nat) (hi : i < 561)
    (ho : off + p = (slotSt i + w0 : Nat)) (hk : w0 + k ≤ slotLn i) :
    memRd (slotsMem σ vs) off (p + k) = memRd (slotsMem σ vs) off p ++
      (List.range k).map (fun w => slotsMem σ vs (slotSt i + w0 + w)) := by
  rw [memRd_add]
  congr 1
  apply List.map_congr_left
  intro w hw
  simp at hw
  have he := slot_end_le i hi
  rw [if_pos (by omega)]
  congr 1
  omega

/-- The characters of a `null` slot: spaces. -/
theorem slotsMem_null (σ : State) (vs : List Value) (i w : Nat) (hi : i < 561) (hw : w < slotLn i)
    (hn : vs[i]? = some .null) : slotsMem σ vs (slotSt i + w) = space := by
  unfold slotsMem
  rw [slotIdx_of_mem i _ hi (by omega) (by omega), hn]

/-- The characters of a string slot: the string's. -/
theorem slotsMem_str (σ : State) (vs : List Value) (i w : Nat) (hi : i < 561) (hw : w < slotLn i) (x : Addr)
    (c : JStr) (hx : vs[i]? = some (.ref x)) (hc : σ.heap x = some (.str c)) :
    slotsMem σ vs (slotSt i + w) = c.getD w space := by
  unfold slotsMem
  rw [slotIdx_of_mem i _ hi (by omega) (by omega), hx]
  simp only [hc]
  congr 1
  omega

end EquivLean.Modernize.Cbstm03a.Java.Mem
