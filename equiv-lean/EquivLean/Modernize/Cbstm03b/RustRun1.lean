import EquivLean.Bridge.Aeneas.SpecAuto
import EquivLean.Demo.Gen.Aeneas.ModCbstm03b.Funs

/-!
# CBSTM03B → Rust: the helpers of `call`

The translation is veriforch's (`examples/rust/mod_cbstm03b`, `Demo/Gen/Aeneas/ModCbstm03b`). Value forms of the
helpers: `fmt_status` (the status code's two ASCII digits), `eq8`/`eq9` (equality of byte arrays), `key_byte`
below 25 (a byte of `LK-M03B-KEY`), `cust_key` (the first `k` key bytes, space-padded to 9), `acct_key` (the
digits `b &&& 15` of the key's positions `k - 11 ..< k` as a number, `% 10 ^ 11` at each step),
`find_cust`/`find_acct` (the index of the first record with the key, else the number of records). The loops
of `cust_key`, `acct_key` and the searches are proved by `wp_loop` with their invariants.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas

namespace EquivLean.Modernize.Cbstm03b.Rust

/-! ## List and scalar facts -/

theorem take_succ_eq_iff {α : Type _} {a b : List α} {i : Nat} (ha : i < a.length) (hb : i < b.length) :
    a.take (i + 1) = b.take (i + 1) ↔ a.take i = b.take i ∧ a[i] = b[i] := by
  rw [take_succ_of_lt ha, take_succ_of_lt hb]
  constructor
  · intro h
    have hl : (a.take i).length = (b.take i).length := by simp; omega
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

theorem drop_take_succ {α : Type _} {l : List α} {s i : Nat} (hs : s ≤ i) (hi : i < l.length) :
    (l.take (i + 1)).drop s = (l.take i).drop s ++ [l[i]] := by
  rw [take_succ_of_lt hi, List.drop_append_of_le_length (by simp; omega)]

theorem findIdx?_lt {α : Type _} {p : α → Bool} : ∀ {l : List α} {j : Nat}, l.findIdx? p = some j → j < l.length
  | [], j, h => by simp at h
  | a :: l, j, h => by
    rw [List.findIdx?_cons] at h
    split at h
    · simp only [Option.some.injEq] at h
      simp; omega
    · cases h' : l.findIdx? p with
      | none => simp [h'] at h
      | some k =>
        simp only [h', Option.map_some, Option.some.injEq] at h
        have := findIdx?_lt h'
        simp; omega

theorem findIdx?_take_succ {α : Type _} {l : List α} {p : α → Bool} {i : Nat} (hi : i < l.length) :
    (l.take (i + 1)).findIdx? p = ((l.take i).findIdx? p).or (if p l[i] then some i else none) := by
  rw [take_succ_of_lt hi, List.findIdx?_append]
  have hl : (l.take i).length = i := by simp; omega
  cases h : p l[i] <;> simp [h, hl]

/-- A search state: the index found in the prefix, else the length. -/
theorem findIdx?_getD_eq_len {α : Type _} {l : List α} {p : α → Bool} {i : Nat} (hi : i ≤ l.length)
    (h : ((l.take i).findIdx? p).getD l.length = l.length) : (l.take i).findIdx? p = none := by
  cases h' : (l.take i).findIdx? p with
  | none => rfl
  | some j =>
    have := findIdx?_lt h'
    simp only [h', Option.getD_some] at h
    simp at this
    omega

theorem set_pad {l : List U8} {j : Nat} (b c : U8) (n : Nat) (hj : l.length = j) :
    (l ++ List.replicate (n + 1) c).set j b = l ++ b :: List.replicate n c := by
  subst hj
  simp [List.set_append_right, List.replicate_succ]

theorem hcast_usize_val (x : I64) (h0 : 0 ≤ x.val) (h25 : x.val ≤ 25) :
    (IScalar.hcast .Usize x).val = x.val.toNat := by
  have hb : x.val < 2 ^ UScalarTy.Usize.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> simp only [UScalarTy.numBits, h] <;> omega
  rw [IScalar.hcast_val_eq, Int.emod_eq_of_lt h0 hb]

theorem srem_val (x y : I64) : (IScalar.mk (x.bv.srem y.bv) : I64).val = Int.tmod x.val y.val := by
  simp only [IScalar.val, BitVec.toInt_srem]

/-- The value of `x % y` as the generated code computes it, for `x` from `IScalar.ofIntCore`. -/
theorem srem_ofIntCore_val (x : Int) (h) (y : I64) :
    (IScalar.mk (BitVec.srem (I64.bv (IScalar.ofIntCore (ty := .I64) x h)) (IScalar.bv y)) : I64).val =
      Int.tmod x y.val := by
  show (BitVec.srem (IScalar.bv (IScalar.ofIntCore (ty := .I64) x h)) (IScalar.bv y)).toInt = Int.tmod x y.val
  rw [BitVec.toInt_srem, IScalar.bv_toInt_eq, IScalar.bv_toInt_eq, IScalar.ofInt_val_eq]

/-- `a[i]` for an array, as `getD` (no proof term in the value, so later rewrites keep the goal type-correct
at the `implicit` transparency of `#usize` literals). -/
theorem index_usize_getD {α : Type _} [Inhabited α] {n : Usize} (a : Array α n) (i : Usize)
    (h : i.val < a.val.length) : Array.index_usize a i = .ok (a.val.getD i.val default) := by
  rw [array_index_usize_eq, dite_eq_left h, List.getD_eq_getElem _ _ h]

theorem u8_and15_le (b : U8) : (b &&& 15#u8).val ≤ 15 := by
  rw [UScalar.val_and]
  exact Nat.and_le_right

/-! ## Status, equality, key bytes -/

/-- `fmt_status`: the status code's two ASCII digits. -/
theorem fmt_status_eq (c : U8) :
    ∃ a, cbstm03b.fmt_status c = .ok a ∧ a.val.map (·.val) = [48 + c.val / 10 % 10, 48 + c.val % 10] := by
  aeneas_spec [cbstm03b.fmt_status]

/-- `eq8`: equality of the two byte arrays. -/
theorem eq8_eq (a b : Array U8 8#usize) : cbstm03b.eq8 a b = .ok (decide (a.val = b.val)) := by
  have ha : a.val.length = 8 := a.property
  have hb : b.val.length = 8 := b.property
  aeneas_spec [cbstm03b.eq8, cbstm03b.eq8_loop] with [take_succ_eq_iff, ha, hb]
    using (fun (eq, i) => i.val ≤ 8 ∧ eq = decide (a.val.take i.val = b.val.take i.val))
      (fun (_, i) => 8 - i.val)

/-- `eq9`: equality of the two byte arrays. -/
theorem eq9_eq (a b : Array U8 9#usize) : cbstm03b.eq9 a b = .ok (decide (a.val = b.val)) := by
  have ha : a.val.length = 9 := a.property
  have hb : b.val.length = 9 := b.property
  aeneas_spec [cbstm03b.eq9, cbstm03b.eq9_loop] with [take_succ_eq_iff, ha, hb]
    using (fun (eq, i) => i.val ≤ 9 ∧ eq = decide (a.val.take i.val = b.val.take i.val))
      (fun (_, i) => 9 - i.val)

/-- `key_byte` below 25: a byte of the key. -/
theorem key_byte_lt (area : cbstm03b.LkM03bArea) (i : Usize) (hi : i.val < 25) :
    cbstm03b.key_byte area i = Array.index_usize area.lk_m03b_key i := by
  have h : i < 25#usize := by scalar_tac
  simp only [cbstm03b.key_byte, h, ↓reduceIte]

/-! ## The keys -/

/-- The first `k` bytes of the key, space-padded to 9 (`MOVE LK-M03B-KEY (1:k) TO FD-CUST-ID`). -/
def custKeyR (key : List U8) (k : Nat) : List U8 := key.take (min k 9) ++ List.replicate (9 - min k 9) 32#u8

/-- `cust_key`, for a key length in `0 ..= 25`. -/
theorem cust_key_eq (area : cbstm03b.LkM03bArea) (h0 : 0 ≤ area.lk_m03b_key_ln.val)
    (h25 : area.lk_m03b_key_ln.val ≤ 25) :
    ∃ r, cbstm03b.cust_key area = .ok r ∧ r.val = custKeyR area.lk_m03b_key.val area.lk_m03b_key_ln.val.toNat := by
  have hk : area.lk_m03b_key.val.length = 25 := area.lk_m03b_key.property
  have hK := hcast_usize_val area.lk_m03b_key_ln h0 h25
  obtain ⟨dd, op, rc, key, kln, fldt⟩ := area
  simp only at hk hK h0 h25 ⊢
  generalize hKdef : IScalar.hcast .Usize kln = K at hK
  refine exists_ok_of_wp ?_
  simp only [cbstm03b.cust_key, cbstm03b.cust_key_loop]
  aeneas_wp []
  rw [hKdef]
  refine wp_loop (loop_shape _) (fun (s : Array U8 9#usize × Usize) => s.2.val ≤ 9 ∧
      s.1.val = key.val.take (min K.val s.2.val) ++ List.replicate (9 - min K.val s.2.val) 32#u8)
    (fun s => 9 - s.2.val) ?_ _ ?_
  · rintro ⟨id, j⟩ ⟨hj, hid⟩
    simp only at hj hid
    by_cases hj9 : j.val < 9
    · have hj25 : j.val < 25 := by omega
      by_cases hjK : j.val < K.val
      · have hjl : j.val < key.val.length := by omega
        have h9 : id.val.length = 9 := by simp
        have hidl : j.val < id.val.length := by omega
        have hmax : j.val + 1 ≤ Usize.max := by scalar_tac
        aeneas_wp [rust_loop_body, key_byte_lt _ _ hj25, index_usize_getD _ _ hjl, array_update_eq, hj9, hjK,
          hidl, hmax]
        simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [Array.from_val, hid, Nat.min_eq_right (by omega : j.val ≤ K.val),
          Nat.min_eq_right (by omega : j.val + 1 ≤ K.val), take_succ_of_lt hjl,
          show 9 - j.val = (9 - (j.val + 1)) + 1 by omega, set_pad _ _ _ (by simp; omega),
          List.getD_eq_getElem _ _ hjl]
        simp only [List.append_assoc, List.singleton_append]
      · have hmax : j.val + 1 ≤ Usize.max := by scalar_tac
        aeneas_wp [rust_loop_body, hj9, hjK, hmax]
        simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [hid, Nat.min_eq_left (by omega : K.val ≤ j.val), Nat.min_eq_left (by omega : K.val ≤ j.val + 1)]
    · aeneas_wp [rust_loop_body, hj9]
      simp only [loopCls_done]
      refine ⟨id, rfl, ?_⟩
      have : j.val = 9 := by omega
      rw [hid, this, custKeyR, hK]
  · simp

/-- The digits `b &&& 15` of a byte string, as a number. -/
def digitsVal (bs : List U8) : Int := bs.foldl (fun acc b => acc * 10 + ((b.val &&& 15 : Nat) : Int)) 0

theorem digitsVal_append (bs : List U8) (b : U8) :
    digitsVal (bs ++ [b]) = digitsVal bs * 10 + ((b.val &&& 15 : Nat) : Int) := by
  simp [digitsVal, List.foldl_append]

theorem acct_step_val (val v D d : Int) (e : Nat) (hv : v = (val * 10 ^ e + D) % 100000000000) (hd : 0 ≤ d)
    (_hv0 : 0 ≤ v) :
    Int.tmod (v * 10 + d) 100000000000 = (val * 10 ^ (e + 1) + (D * 10 + d)) % 100000000000 := by
  rw [Int.tmod_eq_emod_of_nonneg (by omega), hv, Int.add_emod, Int.mul_emod,
    Int.emod_emod_of_dvd _ (by norm_num), ← Int.mul_emod, ← Int.add_emod, pow_succ]
  ring_nf

/-- The digit loop of `acct_key` from position `i` with value `val`. -/
theorem acct_key_loop_eq (dd : Array U8 8#usize) (op : Array U8 1#usize) (rc : Array U8 2#usize)
    (key : Array U8 25#usize) (kln : I64) (fldt : Array U8 1000#usize) (k : Usize) (val : I64) (i : Usize)
    (hk : k.val ≤ 25) (hi : i.val ≤ k.val) (h0 : 0 ≤ val.val) (h1 : val.val < 100000000000) :
    ∃ r, cbstm03b.acct_key_loop dd op rc key kln fldt k val i = .ok r ∧
      r.val = (val.val * 10 ^ (k.val - i.val) + digitsVal ((key.val.take k.val).drop i.val)) % 100000000000 := by
  have hkl0 : key.val.length = 25 := key.property
  have hm : cbstm03b.ACCT_MOD.val = 100000000000 := by simp [cbstm03b.ACCT_MOD]
  -- the bytes as a list, so that the goals no longer mention `key` (whose type holds a `25#usize` literal)
  have hidxG : ∀ j : Usize, j.val < key.val.length → Array.index_usize key j = .ok (key.val.getD j.val default) :=
    fun j hj => index_usize_getD _ _ hj
  generalize hks : key.val = ks at hkl0 hidxG ⊢
  refine exists_ok_of_wp ?_
  simp only [cbstm03b.acct_key_loop]
  refine wp_loop (loop_shape _) (fun (s : I64 × Usize) => i.val ≤ s.2.val ∧ s.2.val ≤ k.val ∧ 0 ≤ s.1.val ∧
      s.1.val < 100000000000 ∧
      s.1.val = (val.val * 10 ^ (s.2.val - i.val) + digitsVal ((ks.take s.2.val).drop i.val)) % 100000000000)
    (fun s => k.val - s.2.val) ?_ _ ?_
  · rintro ⟨v, j⟩ ⟨hij, hjk, hv0, hv1, hv⟩
    simp only at hij hjk hv0 hv1 hv
    by_cases hjk' : j.val < k.val
    · have hj25 : j.val < 25 := by omega
      have hjl : j.val < ks.length := by omega
      have hmax : j.val + 1 ≤ Usize.max := by scalar_tac
      obtain ⟨b, hbdef⟩ : ∃ b, ks.getD j.val default = b := ⟨_, rfl⟩
      have hidx : Array.index_usize key j = .ok b := by rw [hidxG j hjl, hbdef]
      aeneas_wp [rust_loop_body, key_byte_lt _ _ hj25, hidx, hjk', hmax]
      have hb := u8_and15_le b
      split_ifs with hA hB hC
      all_goals try first
        | (exfalso; omega)
        | (simp [hm] at *; done)
      try simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
      have hval := acct_step_val val.val v.val (digitsVal ((ks.take j.val).drop i.val))
        ((b &&& 15#u8).val : Int) (j.val - i.val) hv (by omega) hv0
      rw [srem_ofIntCore_val, hm, hval]
      refine ⟨⟨by omega, by omega, Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num), ?_⟩,
        by omega⟩
      rw [show j.val + 1 - i.val = (j.val - i.val) + 1 by omega, drop_take_succ hij hjl, digitsVal_append,
        UScalar.val_and, ← hbdef, List.getD_eq_getElem _ _ hjl]
      rfl
    · aeneas_wp [rust_loop_body, hjk']
      simp only [loopCls_done]
      refine ⟨v, rfl, ?_⟩
      have : j.val = k.val := by omega
      rw [hv, this]
  · refine ⟨le_refl _, hi, h0, h1, ?_⟩
    simp [digitsVal, Int.emod_eq_of_lt h0 h1]

/-- `acct_key`, for a key length in `0 ..= 25`: the value of the digits of the key's positions `start ..< k`
(`start = k - 11` when `k > 11`), `% 10 ^ 11`. -/
theorem acct_key_eq (area : cbstm03b.LkM03bArea) (h0 : 0 ≤ area.lk_m03b_key_ln.val)
    (h25 : area.lk_m03b_key_ln.val ≤ 25) :
    ∃ r, cbstm03b.acct_key area = .ok r ∧
      r.val = digitsVal ((area.lk_m03b_key.val.take area.lk_m03b_key_ln.val.toNat).drop
        (area.lk_m03b_key_ln.val.toNat - 11)) % 100000000000 := by
  have hK := hcast_usize_val area.lk_m03b_key_ln h0 h25
  obtain ⟨dd, op, rc, key, kln, fldt⟩ := area
  simp only at hK h0 h25 ⊢
  generalize hKdef : IScalar.hcast .Usize kln = K at hK
  refine exists_ok_of_wp ?_
  simp only [cbstm03b.acct_key]
  aeneas_wp []
  rw [hKdef]
  by_cases h11 : 11 < K.val
  · aeneas_wp [h11, show 11 ≤ K.val by omega]
    obtain ⟨r, hr, hrv⟩ := acct_key_loop_eq dd op rc key kln fldt K 0#i64
      (UScalar.ofNatCore (K.val - 11) (by scalar_tac)) (by omega) (by simp) (by simp) (by simp)
    rw [hr]
    refine (wp_ok _ _).2 ⟨r, rfl, ?_⟩
    rw [hrv]
    simp [UScalar.ofNatCore_val_eq, hK]
  · aeneas_wp [h11]
    obtain ⟨r, hr, hrv⟩ := acct_key_loop_eq dd op rc key kln fldt K 0#i64 0#usize (by omega) (by simp)
      (by simp) (by simp)
    rw [hr]
    refine (wp_ok _ _).2 ⟨r, rfl, ?_⟩
    rw [hrv]
    simp [hK, show kln.val.toNat - 11 = 0 by omega]

/-! ## The searches -/

/-- `find_cust`: the index of the first record with the customer id, else the number of records. -/
theorem find_cust_eq (recs : alloc.vec.Vec cbstm03b.FdCustfileRec) (id : Array U8 9#usize) :
    ∃ r, cbstm03b.find_cust recs id = .ok r ∧
      r.val = (recs.val.findIdx? (fun x => decide (x.fd_cust_id.val = id.val))).getD recs.val.length := by
  have hlen : recs.val.length ≤ Usize.max := recs.property
  refine exists_ok_of_wp ?_
  simp only [cbstm03b.find_cust, cbstm03b.find_cust_loop]
  refine wp_loop (loop_shape _) (fun (s : Usize × Usize) => s.2.val ≤ recs.val.length ∧
      s.1.val = ((recs.val.take s.2.val).findIdx? (fun x => decide (x.fd_cust_id.val = id.val))).getD
        recs.val.length)
    (fun s => recs.val.length - s.2.val) ?_ _ ?_
  · rintro ⟨idx, i⟩ ⟨hi, hidx⟩
    simp only at hi hidx
    by_cases hlt : i.val < recs.val.length
    · have hmax : i.val + 1 ≤ Usize.max := by omega
      by_cases heq : idx.val = recs.val.length
      · have hnone := findIdx?_getD_eq_len hi (hidx ▸ heq)
        by_cases hm : (recs.val[i.val]'hlt).fd_cust_id.val = id.val
        · aeneas_wp [rust_loop_body, cbstm03b.cust_id_at, eq9_eq, hlt, heq, hm, hmax]
          simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          simp [findIdx?_take_succ hlt, hnone, hm]
        · aeneas_wp [rust_loop_body, cbstm03b.cust_id_at, eq9_eq, hlt, heq, hm, hmax]
          simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          simp [findIdx?_take_succ hlt, hnone, hm, heq]
      · aeneas_wp [rust_loop_body, cbstm03b.cust_id_at, eq9_eq, hlt, heq, hmax]
        simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        cases h : (recs.val.take i.val).findIdx? (fun x => decide (x.fd_cust_id.val = id.val)) with
        | none => simp [h] at hidx; omega
        | some j => simp [findIdx?_take_succ hlt, h, hidx]
    · aeneas_wp [rust_loop_body, hlt]
      simp only [loopCls_done]
      refine ⟨idx, rfl, ?_⟩
      have : i.val = recs.val.length := by omega
      rw [hidx, this, List.take_length]
  · simp

/-- `find_acct`: the index of the first record with the account id, else the number of records. -/
theorem find_acct_eq (recs : alloc.vec.Vec cbstm03b.FdAcctfileRec) (key : I64) :
    ∃ r, cbstm03b.find_acct recs key = .ok r ∧
      r.val = (recs.val.findIdx? (fun x => decide (x.fd_acct_id.val = key.val))).getD recs.val.length := by
  have hlen : recs.val.length ≤ Usize.max := recs.property
  refine exists_ok_of_wp ?_
  simp only [cbstm03b.find_acct, cbstm03b.find_acct_loop]
  refine wp_loop (loop_shape _) (fun (s : Usize × Usize) => s.2.val ≤ recs.val.length ∧
      s.1.val = ((recs.val.take s.2.val).findIdx? (fun x => decide (x.fd_acct_id.val = key.val))).getD
        recs.val.length)
    (fun s => recs.val.length - s.2.val) ?_ _ ?_
  · rintro ⟨idx, i⟩ ⟨hi, hidx⟩
    simp only at hi hidx
    by_cases hlt : i.val < recs.val.length
    · have hmax : i.val + 1 ≤ Usize.max := by omega
      by_cases heq : idx.val = recs.val.length
      · have hnone := findIdx?_getD_eq_len hi (hidx ▸ heq)
        by_cases hm : (recs.val[i.val]'hlt).fd_acct_id.val = key.val
        · aeneas_wp [rust_loop_body, cbstm03b.acct_id_at, hlt, heq, hm, hmax]
          simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          simp [findIdx?_take_succ hlt, hnone, hm]
        · aeneas_wp [rust_loop_body, cbstm03b.acct_id_at, hlt, heq, hm, hmax]
          simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          simp [findIdx?_take_succ hlt, hnone, hm, heq]
      · aeneas_wp [rust_loop_body, cbstm03b.acct_id_at, hlt, heq, hmax]
        simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        cases h : (recs.val.take i.val).findIdx? (fun x => decide (x.fd_acct_id.val = key.val)) with
        | none => simp [h] at hidx; omega
        | some j => simp [findIdx?_take_succ hlt, h, hidx]
    · aeneas_wp [rust_loop_body, hlt]
      simp only [loopCls_done]
      refine ⟨idx, rfl, ?_⟩
      have : i.val = recs.val.length := by omega
      rw [hidx, this, List.take_length]
  · simp

end EquivLean.Modernize.Cbstm03b.Rust
