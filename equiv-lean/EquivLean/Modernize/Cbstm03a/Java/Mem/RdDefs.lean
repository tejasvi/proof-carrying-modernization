import EquivLean.Modernize.Cbstm03a.Java.Mem.Geo
import EquivLean.Modernize.Cbstm03a.Java.Mem.Lem
import EquivLean.Modernize.Cbstm03a.Java.Iface1

/-!
# CBSTM03A → Java: `memRead`, the loop invariant and the segments' weakest precondition

One cut point, the loop head (statement 6). The builder holds the first `pos` characters read, from the canonical
memory of the slots (`slotsMem σ0 vs`: the memory of every `m` with `SlotsAt σ0 a m` below `MEM_SZ`).
Locals: `slots` 0, `off` 1, `o` 2, `$l6` 3, `$b1` 4, `n` 5, `within` 6, `len` 7, `$i8` 8, `skip` 9, `pos` 10,
`take#8` 11, `sb` 12, `cur` 13.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java.Mem

/-- The callees of `memRead`. -/
def rdCallees : Contracts :=
  [(spacesSig, spacesSpecI), (slotIndexSig, slotIndexSpec), (slotLenSig, slotLenSpec), (slotStartSig, slotStartSpec)]

/-- The facts at the loop head. -/
def RdAt (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (n : I32) (vs : List Value) (sb : Addr)
    (pos : I32) (t : JStr) : Prop :=
  fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧ fr.get 5 = some (.int n) ∧
  fr.get 10 = some (.int pos) ∧ fr.get 12 = some (.ref sb) ∧
  σ.heap sb = some (.builder "java.lang.StringBuilder" t) ∧ t = memRd (slotsMem σ0 vs) off.toInt pos.toInt.toNat ∧
  σ0.next ≤ sb ∧ σ.heap a = some (.array (.cls "java.lang.String") vs) ∧ vs.length = 561 ∧
  -2147483648 < off.toInt ∧ 0 ≤ pos.toInt ∧ (pos.toInt ≤ n.toInt ∨ pos.toInt = 0) ∧
  (pos.toInt = 0 ∨ off.toInt < 171156) ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics

def rdInv6 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (a : Addr) (off : I64) (n : I32), args = [.ref a, .long off, .int n] →
    ∃ vs sb pos t, RdAt σ0 fr σ a off n vs sb pos t

/-- The facts after the slot read (statement 38, `if cur != null`): `ix` the slot of position `off + pos`, `wv` the
offset in it, `tk` the number of characters to read (`take#8`), `cv` the slot value read (local `cur`). -/
def Rd38At (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (n : I32) (vs : List Value) (sb : Addr)
    (pos ix wv tk : I32) (cv : Value) (t : JStr) : Prop :=
  fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧ fr.get 5 = some (.int n) ∧
  fr.get 10 = some (.int pos) ∧ fr.get 12 = some (.ref sb) ∧ fr.get 9 = some (.int ix) ∧
  fr.get 6 = some (.int wv) ∧ fr.get 11 = some (.int tk) ∧ fr.get 13 = some cv ∧
  σ.heap sb = some (.builder "java.lang.StringBuilder" t) ∧ t = memRd (slotsMem σ0 vs) off.toInt pos.toInt.toNat ∧
  σ0.next ≤ sb ∧ σ.heap a = some (.array (.cls "java.lang.String") vs) ∧ vs.length = 561 ∧
  -2147483648 < off.toInt ∧ 0 ≤ pos.toInt ∧ pos.toInt < n.toInt ∧
  0 ≤ off.toInt + pos.toInt ∧ off.toInt + pos.toInt < 171156 ∧
  ix.toInt = (slotIdx (off.toInt + pos.toInt).toNat : Int) ∧
  vs[slotIdx (off.toInt + pos.toInt).toNat]? = some cv ∧
  wv.toInt = off.toInt + pos.toInt - (slotSt (slotIdx (off.toInt + pos.toInt).toNat) : Int) ∧
  0 < tk.toInt ∧ tk.toInt ≤ n.toInt - pos.toInt ∧
  wv.toInt + tk.toInt ≤ (slotLn (slotIdx (off.toInt + pos.toInt).toNat) : Int) ∧
  Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics

def rdInv38 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (a : Addr) (off : I64) (n : I32), args = [.ref a, .long off, .int n] →
    ∃ vs sb pos ix wv tk cv t, Rd38At σ0 fr σ a off n vs sb pos ix wv tk cv t

def memReadInv : Invariants := [(6, rdInv6), (38, rdInv38)]

/-- The paths of `memRead` from statement `pc`. -/
@[irreducible] def rdWP (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog rdCallees.env 0) Gen.Cbstm03a.«memRead(java.lang.String[],long,int)»
    (memReadInv.inst args σ0) (memReadSpec.post args σ0) 120 pc fr σ

/-! ## Closing the segments -/

theorem rd_exit_close {σ0 : State} {a : Addr} {w : List Value} {m : Nat → JChar} {off : Int} {p q : Nat}
    (ha : σ0.heap a = some (.array (.cls "java.lang.String") w)) (hlen : w.length = 561)
    (hs : ∀ i < 561, (w[i]? = some Value.null ∧ ∀ w' < slotLn i, m (slotSt i + w') = space) ∨
      ∃ x t, w[i]? = some (Value.ref x) ∧ σ0.heap x = some (Obj.str t) ∧ List.length t = slotLn i ∧
        ∀ w' < slotLn i, m (slotSt i + w') = List.getD t w' space)
    (hpq : p = q) : memRd (slotsMem σ0 w) off p = memRd m off q := by
  subst hpq
  exact memRd_congr (fun j hj => (slotsAt_eq_slotsMem ⟨w, ha, hlen, hs⟩ ha j hj).symm) off p

theorem rd_out_close {M : Nat → JChar} {off : Int} {p k q : Nat} (hq : q = p + k)
    (h : off + (p + k : Nat) ≤ 0 ∨ 171156 ≤ off + p) :
    memRd M off p ++ List.replicate k space = memRd M off q := by
  subst hq
  rw [memRd_add_out M off p k h]

theorem rd_past_close {σ0 : State} {a : Addr} {w : List Value} {m : Nat → JChar} {off : Int} {p k q : Nat}
    (ha : σ0.heap a = some (.array (.cls "java.lang.String") w)) (hlen : w.length = 561)
    (hs : ∀ i < 561, (w[i]? = some Value.null ∧ ∀ w' < slotLn i, m (slotSt i + w') = space) ∨
      ∃ x t, w[i]? = some (Value.ref x) ∧ σ0.heap x = some (Obj.str t) ∧ List.length t = slotLn i ∧
        ∀ w' < slotLn i, m (slotSt i + w') = List.getD t w' space)
    (hq : q = p + k) (h : 171156 ≤ off + p) :
    memRd (slotsMem σ0 w) off p ++ List.replicate k space = memRd m off q := by
  rw [rd_out_close (M := slotsMem σ0 w) hq (Or.inr h)]
  exact rd_exit_close ha hlen hs rfl

/-- `skip = (int) -o` for `-2^31 < o = off + pos < 0`. -/
theorem neg_l2i_toInt (off : I64) (pos : I32) (h1 : -2147483648 < off.toInt) (h2 : 0 ≤ pos.toInt)
    (h3 : off.toInt + pos.toInt < 0) :
    (JLong.toInt (-JInt.toLong pos + -off)).toInt = -(off.toInt + pos.toInt) := by
  have hp : (JInt.toLong pos).toInt = pos.toInt := by
    unfold JInt.toLong
    rw [BitVec.toInt_signExtend]
    simp only [show min 64 32 = 32 from rfl]
    exact bmod32_self (by have := BitVec.le_toInt (x := pos); omega) (by have := BitVec.toInt_lt (x := pos); omega)
  have hpl := BitVec.toInt_lt (x := pos)
  have hs : (-JInt.toLong pos + -off).toInt = -(off.toInt + pos.toInt) := by
    have hol := BitVec.toInt_lt (x := off)
    have hoge := BitVec.le_toInt (x := off)
    simp only [Nat.reducePow, Nat.reduceSub, Nat.cast_ofNat] at hol hoge hpl
    rw [BitVec.toInt_add, BitVec.toInt_neg, BitVec.toInt_neg, hp]
    rw [bmod64_self (x := -pos.toInt) (by omega) (by omega), bmod64_self (x := -off.toInt) (by omega) (by omega),
      bmod64_self (by omega) (by omega)]
    omega
  unfold JLong.toInt
  rw [BitVec.toInt_setWidth]
  have e := toInt_eq_toNat_of_nonneg (-JInt.toLong pos + -off) (by omega)
  have hn := (-JInt.toLong pos + -off).isLt
  rw [show ((-JInt.toLong pos + -off).toNat : Int) = -(off.toInt + pos.toInt) by omega]
  exact bmod32_self (by omega) (by omega)

theorem rd_skip_c1 (M : Nat → JChar) (off : I64) (pos : I32) (h1 : -2147483648 < off.toInt) (h2 : 0 ≤ pos.toInt)
    (h3 : off.toInt + pos.toInt < 0) :
    memRd M off.toInt pos.toInt.toNat ++ List.replicate (JLong.toInt (-JInt.toLong pos + -off)).toInt.toNat space =
      memRd M off.toInt (pos.toInt + (JLong.toInt (-JInt.toLong pos + -off)).toInt).toNat := by
  rw [neg_l2i_toInt off pos h1 h2 h3]
  exact rd_out_close (by omega) (Or.inl (by omega))

theorem rd_skip_c2 (off : I64) (pos : I32) (h1 : -2147483648 < off.toInt) (h2 : 0 ≤ pos.toInt)
    (h3 : off.toInt + pos.toInt < 0) : 0 ≤ pos.toInt + (JLong.toInt (-JInt.toLong pos + -off)).toInt := by
  rw [neg_l2i_toInt off pos h1 h2 h3]; omega

theorem rd_skip_c3 (M : Nat → JChar) (off : I64) (pos n : I32) (h1 : -2147483648 < off.toInt)
    (h2 : 0 ≤ pos.toInt) (h3 : off.toInt + pos.toInt < 0)
    (hc : ¬ (JLong.toInt (-JInt.toLong pos + -off)).toInt ≤ n.toInt - pos.toInt) (hx : pos.toInt < n.toInt) :
    memRd M off.toInt pos.toInt.toNat ++ List.replicate (n.toInt - pos.toInt).toNat space =
      memRd M off.toInt n.toInt.toNat := by
  rw [neg_l2i_toInt off pos h1 h2 h3] at hc
  exact rd_out_close (by omega) (Or.inl (by omega))

theorem rd_past_c {σ0 : State} {a : Addr} {w : List Value} {m : Nat → JChar} (off : I64) (pos n : I32)
    (ha : σ0.heap a = some (.array (.cls "java.lang.String") w)) (hlen : w.length = 561)
    (hs : ∀ i < 561, (w[i]? = some Value.null ∧ ∀ w' < slotLn i, m (slotSt i + w') = space) ∨
      ∃ x t, w[i]? = some (Value.ref x) ∧ σ0.heap x = some (Obj.str t) ∧ List.length t = slotLn i ∧
        ∀ w' < slotLn i, m (slotSt i + w') = List.getD t w' space)
    (h2 : 0 ≤ pos.toInt) (hx : pos.toInt < n.toInt) (hp : 171156 ≤ off.toInt + pos.toInt) :
    memRd (slotsMem σ0 w) off.toInt pos.toInt.toNat ++ List.replicate (n.toInt - pos.toInt).toNat space =
      memRd m off.toInt n.toInt.toNat :=
  rd_past_close ha hlen hs (by omega) (by omega)

/-! ## The slot path's arithmetic -/

theorem slotIdx_lt (j : Nat) (hj : j < 171156) : slotIdx j < 561 := (slotIdx_spec j hj).1

theorem ofNat32_slotIdx_toNat (j : Nat) (hj : j < 171156) : (BitVec.ofNat 32 (slotIdx j)).toNat = slotIdx j := by
  have := slotIdx_lt j hj
  simp only [BitVec.toNat_ofNat]
  omega

theorem ofNat32_slotIdx_toInt (j : Nat) (hj : j < 171156) :
    (BitVec.ofNat 32 (slotIdx j)).toInt = (slotIdx j : Int) := by
  have := slotIdx_lt j hj
  rw [toInt_eq_toNat_of_lt _ (by rw [ofNat32_slotIdx_toNat j hj]; omega), ofNat32_slotIdx_toNat j hj]

theorem ofNat32_slotLn_toInt (i : Nat) : (BitVec.ofNat 32 (slotLn i)).toInt = (slotLn i : Int) := by
  have := slotLn_le i
  have h2 : (BitVec.ofNat 32 (slotLn i)).toNat = slotLn i := by simp only [BitVec.toNat_ofNat]; omega
  rw [toInt_eq_toNat_of_lt _ (by rw [h2]; omega), h2]

/-- A `null` slot read: the next `tk` characters are spaces. -/
theorem rd_null_c (σ0 : State) (vs : List Value) (i : Nat) (hn : vs[i]? = some .null) (off : I64) (pos wv tk : I32)
    (hi : i < 561) (hp : 0 ≤ pos.toInt) (hw : wv.toInt = off.toInt + pos.toInt - (slotSt i : Int))
    (hw0 : 0 ≤ wv.toInt) (htk : 0 < tk.toInt) (hk : wv.toInt + tk.toInt ≤ (slotLn i : Int)) :
    memRd (slotsMem σ0 vs) off.toInt pos.toInt.toNat ++ List.replicate tk.toInt.toNat space =
      memRd (slotsMem σ0 vs) off.toInt (pos.toInt + tk.toInt).toNat := by
  rw [show (pos.toInt + tk.toInt).toNat = pos.toInt.toNat + tk.toInt.toNat by omega,
    memRd_add_slot σ0 vs off.toInt pos.toInt.toNat tk.toInt.toNat i wv.toInt.toNat hi (by omega) (by omega)]
  congr 1
  apply List.ext_getElem (by simp)
  intro w h1 h2
  simp only [List.getElem_replicate, List.getElem_map, List.getElem_range]
  simp at h1
  rw [Nat.add_assoc, slotsMem_null σ0 vs i _ hi (by omega) hn]

/-- A string slot read: the next `tk` characters are the slot's, from `wv`. -/
theorem rd_str_c (σ0 : State) (vs : List Value) (i : Nat) (x : Addr) (hv : vs[i]? = some (.ref x)) (c : JStr)
    (hc0 : σ0.heap x = some (.str c)) (hcl : c.length = slotLn i) (off : I64) (pos wv tk : I32)
    (hi : i < 561) (hp : 0 ≤ pos.toInt) (hw : wv.toInt = off.toInt + pos.toInt - (slotSt i : Int))
    (hw0 : 0 ≤ wv.toInt) (htk : 0 < tk.toInt) (hk : wv.toInt + tk.toInt ≤ (slotLn i : Int)) :
    memRd (slotsMem σ0 vs) off.toInt pos.toInt.toNat ++
        List.drop wv.toInt.toNat (List.take (wv.toInt + tk.toInt).toNat c) =
      memRd (slotsMem σ0 vs) off.toInt (pos.toInt + tk.toInt).toNat := by
  rw [show (pos.toInt + tk.toInt).toNat = pos.toInt.toNat + tk.toInt.toNat by omega,
    memRd_add_slot σ0 vs off.toInt pos.toInt.toNat tk.toInt.toNat i wv.toInt.toNat hi (by omega) (by omega)]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro w h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_drop, List.getElem_take]
  simp at h2
  rw [Nat.add_assoc, slotsMem_str σ0 vs i _ hi (by omega) x c hv hc0]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-- `take = len - within > 0` (the `int` subtraction, as `jvc` leaves it). -/
theorem rd_take_pos (J : Int) (hJ : 0 ≤ J) (hJ1 : J < 171156) :
    0 < ((slotLn (slotIdx J.toNat) : Int) - (J - (slotSt (slotIdx J.toNat) : Int))).bmod 4294967296 := by
  obtain ⟨-, h0, h1⟩ := slotIdx_spec J.toNat (by omega)
  have hl := slotLn_le (slotIdx J.toNat)
  have e := bmod32_self (x := (slotLn (slotIdx J.toNat) : Int) - (J - (slotSt (slotIdx J.toNat) : Int)))
    (by omega) (by omega)
  simp only [Nat.reducePow] at e
  rw [e]
  omega

/-- `rd_null_c` with the slot of position `off + pos` and the facts of `Rd37At`. -/
theorem rd_null_c' (σ0 : State) (vs : List Value) (off : I64) (pos wv tk : I32)
    (hin0 : 0 ≤ off.toInt + pos.toInt) (hin1 : off.toInt + pos.toInt < 171156)
    (hn : vs[slotIdx (off.toInt + pos.toInt).toNat]? = some .null) (hp : 0 ≤ pos.toInt)
    (hw : wv.toInt = off.toInt + pos.toInt - (slotSt (slotIdx (off.toInt + pos.toInt).toNat) : Int))
    (htk : 0 < tk.toInt) (hk : wv.toInt + tk.toInt ≤ (slotLn (slotIdx (off.toInt + pos.toInt).toNat) : Int)) :
    memRd (slotsMem σ0 vs) off.toInt pos.toInt.toNat ++ List.replicate tk.toInt.toNat space =
      memRd (slotsMem σ0 vs) off.toInt (pos.toInt + tk.toInt).toNat := by
  obtain ⟨hi, h0, -⟩ := slotIdx_spec (off.toInt + pos.toInt).toNat (by omega)
  exact rd_null_c σ0 vs _ hn off pos wv tk hi hp hw (by omega) htk hk

/-- `rd_str_c` with the slot of position `off + pos` and the facts of `Rd37At`. -/
theorem rd_str_c' (σ0 : State) (vs : List Value) (x : Addr) (c : JStr) (off : I64) (pos wv tk : I32)
    (hin0 : 0 ≤ off.toInt + pos.toInt) (hin1 : off.toInt + pos.toInt < 171156)
    (hv : vs[slotIdx (off.toInt + pos.toInt).toNat]? = some (.ref x)) (hc0 : σ0.heap x = some (.str c))
    (hcl : c.length = slotLn (slotIdx (off.toInt + pos.toInt).toNat)) (hp : 0 ≤ pos.toInt)
    (hw : wv.toInt = off.toInt + pos.toInt - (slotSt (slotIdx (off.toInt + pos.toInt).toNat) : Int))
    (htk : 0 < tk.toInt) (hk : wv.toInt + tk.toInt ≤ (slotLn (slotIdx (off.toInt + pos.toInt).toNat) : Int)) :
    memRd (slotsMem σ0 vs) off.toInt pos.toInt.toNat ++
        List.drop wv.toInt.toNat (List.take (wv.toInt + tk.toInt).toNat c) =
      memRd (slotsMem σ0 vs) off.toInt (pos.toInt + tk.toInt).toNat := by
  obtain ⟨hi, h0, -⟩ := slotIdx_spec (off.toInt + pos.toInt).toNat (by omega)
  exact rd_str_c σ0 vs _ x hv c hc0 hcl off pos wv tk hi hp hw (by omega) htk hk

/-- A string slot read, in the form `jvc` leaves it (`wv` replaced by its value). -/
theorem rd_str_c2 (σ0 : State) (vs : List Value) (x : Addr) (c : JStr) (off : I64) (pos tk : I32)
    (hin0 : 0 ≤ off.toInt + pos.toInt) (hin1 : off.toInt + pos.toInt < 171156)
    (hv : vs[slotIdx (off.toInt + pos.toInt).toNat]? = some (.ref x)) (hc0 : σ0.heap x = some (.str c))
    (hcl : c.length = slotLn (slotIdx (off.toInt + pos.toInt).toNat)) (hp : 0 ≤ pos.toInt) (htk : 0 < tk.toInt)
    (hk : off.toInt + pos.toInt - (slotSt (slotIdx (off.toInt + pos.toInt).toNat) : Int) + tk.toInt ≤ (c.length : Int)) :
    memRd (slotsMem σ0 vs) off.toInt pos.toInt.toNat ++
        List.drop ((off.toInt + pos.toInt).toNat - slotSt (slotIdx (off.toInt + pos.toInt).toNat))
          (List.take ((off.toInt + pos.toInt).toNat - slotSt (slotIdx (off.toInt + pos.toInt).toNat) + tk.toInt.toNat) c) =
      memRd (slotsMem σ0 vs) off.toInt (pos.toInt + tk.toInt).toNat := by
  obtain ⟨hi, h0, h1⟩ := slotIdx_spec (off.toInt + pos.toInt).toNat (by omega)
  rw [show (pos.toInt + tk.toInt).toNat = pos.toInt.toNat + tk.toInt.toNat by omega,
    memRd_add_slot σ0 vs off.toInt pos.toInt.toNat tk.toInt.toNat (slotIdx (off.toInt + pos.toInt).toNat)
      ((off.toInt + pos.toInt).toNat - slotSt (slotIdx (off.toInt + pos.toInt).toNat)) hi (by omega) (by omega)]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro w h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_drop, List.getElem_take]
  simp at h2
  rw [Nat.add_assoc, slotsMem_str σ0 vs _ _ hi (by omega) x c hv hc0]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

end EquivLean.Modernize.Cbstm03a.Java.Mem
