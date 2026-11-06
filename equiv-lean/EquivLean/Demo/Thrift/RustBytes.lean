import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact___impl_thrift__protocol__TInputProtocol_for_thrift__protocol__compact__TCompactInputP_f9dd05ed9a810499
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact___impl_thrift__protocol__TOutputProtocol_for_thrift__protocol__compact__TCompactOutpu_01b9c8c0bed16257
import EquivLean.Demo.Thrift.RustList

/-!
# Thrift (T4), Rust side: the compact string/binary length prefix

`read_binary_len` / `read_bytes` (compact.rs:162, 323) against `Spec.lenPrefix` / `Spec.readLenPrefix`.
-/

open Aeneas Aeneas.Std Result EquivLean EquivLean.Aeneas thrift

namespace EquivLean.Demo.Thrift.Rust

/-- (D) `read_binary_len` reads the varint32 length (inside the configured string limit). -/
theorem read_binary_len_D (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (n : Nat) (hn : n < 2 ^ 32)
    (hcfg : ∀ m : Usize, self.config.max_string_size = some m → n ≤ m.val)
    (pre rest : List U8) (hpre : pre.map (·.val) = (Spec.varint n).map UInt8.toNat)
    (h : rem self.transport = pre ++ rest) :
    ∃ (t' : T) (len : Usize), protocol.compact.TCompactInputProtocol.read_binary_len inst self =
        ok (.Ok len, { self with transport := t' }) ∧ len.val = n ∧ rem t' = rest := by
  have hsz : n < 2 ^ UScalarTy.U32.numBits := by rw [UScalarTy.U32_numBits_eq]; omega
  obtain ⟨t1, hrv, ht1⟩ := read_varint32_D hS hR self (UScalar.ofNatCore n hsz) pre rest
    (by rw [UScalar.ofNatCore_val_eq, encVar_eq_varint]; exact hpre) h
  have hcast : (UScalar.cast UScalarTy.Usize (UScalar.ofNatCore n hsz : U32)).val = n := by
    rw [UScalar.cast_val_eq, UScalar.ofNatCore_val_eq]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.numBits, h] <;> omega
  refine ⟨t1, UScalar.cast UScalarTy.Usize (UScalar.ofNatCore n hsz : U32), ?_, hcast, ht1⟩
  apply eq_ok_of_wp
  unfold protocol.compact.TCompactInputProtocol.read_binary_len
  aeneas_wp [hrv, core.result.Result.Insts.CoreOpsTry.branch,
    configuration.TConfiguration.impl.max_string_size]
  rcases hm : self.config.max_string_size with _ | m
  · simp
  · have := hcfg m hm
    have hn' : ¬ m.val < (UScalar.cast UScalarTy.Usize (UScalar.ofNatCore n hsz : U32)).val := by omega
    simp [hn']
    intro hlt
    omega

/-- (D, compact string/binary) On a transport holding the varint of the length, the bytes `bs`, and then any
bytes `rest`, `read_bytes` returns `bs` and leaves exactly `rest` (for a length inside the configured limit). -/
theorem read_bytes_D (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (bs pre rest : List U8) (hlen : bs.length < 2 ^ 32)
    (hcfg : ∀ m : Usize, self.config.max_string_size = some m → bs.length ≤ m.val)
    (hpre : pre.map (·.val) = (Spec.varint bs.length).map UInt8.toNat)
    (h : rem self.transport = pre ++ (bs ++ rest)) :
    ∃ (t' : T) (v : alloc.vec.Vec U8),
      protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_bytes inst self =
        ok (.Ok v, { self with transport := t' }) ∧ v.val = bs ∧ rem t' = rest := by
  obtain ⟨t1, len, hrl, hlv, ht1⟩ := read_binary_len_D hS hR self bs.length hlen hcfg pre (bs ++ rest) hpre h
  have hmx : len.val ≤ Usize.max := by scalar_tac
  have hfe : alloc.vec.from_elem core.clone.CloneU8 0#u8 len =
      ok (alloc.vec.Vec.from (List.replicate len.val 0#u8) (by simpa using hmx)) := by
    unfold alloc.vec.from_elem
    rw [list_clone_ok _ (fun x => rfl)]
    simp only [bind_tc_ok, bind_ok]
  have hsl : (alloc.vec.Vec.from (List.replicate len.val 0#u8) (by simpa using hmx)).slice.length ≤
      (rem t1).length := by
    rw [ht1]
    simp [alloc.vec.Vec.from, Slice.length, hlv]
  obtain ⟨t2, s', hre, hs', ht2⟩ := hR.read_exact_ok t1 _ hsl
  have hslen : (alloc.vec.Vec.from (List.replicate len.val 0#u8) (by simpa using hmx)).slice.length = bs.length := by
    simp [alloc.vec.Vec.from, Slice.length, hlv]
  refine ⟨t2, { slice := s' }, ?_, ?_, ?_⟩
  · apply eq_ok_of_wp
    unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_bytes
    aeneas_wp [hrl, core.result.Result.Insts.CoreOpsTry.branch, hfe, alloc.vec.Vec.deref_mut, hre,
      core.result.Result.map_err_ok, hS.map_ok,
      protocol.compact.TInputProtocolTCompactInputProtocol.read_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTupleVecU8,
      protocol.compact.TInputProtocolTCompactInputProtocol.read_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleTupleVecU8.call_once]
  · show s'.val = bs
    rw [hs', ht1, hslen]
    simp
  · rw [ht2, ht1, hslen]
    simp

/-! ## `write_bytes` -/

set_option maxHeartbeats 8000000 in
/-- (E, compact string/binary) For every byte slice shorter than 2^32, `write_bytes` appends exactly
`Spec.lenPrefix`: the varint of the length, then the bytes. -/
theorem write_bytes_E (hV : VarintContract) {T : Type} {inst : transport.TWriteTransport T}
    {sent : T → List U8} (hW : WriteContract inst sent) (self : protocol.compact.TCompactOutputProtocol T)
    (b : Slice U8) (hb : b.length < 2 ^ 32) :
    ∃ t', protocol.compact.TCompactOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_bytes inst self b =
        ok (.Ok (), { self with transport := t' }) ∧
      (sent t').map (·.val) = (sent self.transport).map (·.val) ++
        ((Spec.varint b.length).map UInt8.toNat ++ b.val.map (·.val)) := by
  have hv : (UScalar.cast UScalarTy.U32 (Slice.len b)).val = b.length := by
    rw [UScalar.cast_val_eq, Slice.len_val, UScalarTy.U32_numBits_eq]
    exact Nat.mod_eq_of_lt hb
  have hlen : (rusttrn_model.leb128 b.length).length ≤ 5 := leb128_length_le _ 4 (by omega)
  have hbuf0 : (Array.repeat 5#usize (0#u8)).to_slice.val = [0#u8, 0#u8, 0#u8, 0#u8, 0#u8] := by
    simp [Array.to_slice, Array.repeat_val]
  have hwb5 := writeBytes_cursor0 (rusttrn_model.leb128 b.length) [0#u8, 0#u8, 0#u8, 0#u8, 0#u8] id
    (by simpa using hlen)
  have hk : (rusttrn_model.leb128 b.length).length < 2 ^ 64 := by omega
  have hL := leb128_eq_varint b.length
  suffices hwp : wp (protocol.compact.TCompactOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_bytes inst
      self b) (fun o => ∃ t', o = .ok (.Ok (), { self with transport := t' }) ∧
        (sent t').map (·.val) = (sent self.transport).map (·.val) ++
          ((Spec.varint b.length).map UInt8.toNat ++ b.val.map (·.val))) by
    rcases (wp_iff _ _).1 hwp with ⟨a, ha, t', hat, ht'⟩ | ⟨e, _, t', hfalse, _⟩
    · cases hat
      exact ⟨t', ha, ht'⟩
    · cases hfalse
  unfold protocol.compact.TCompactOutputProtocol.Insts.ThriftProtocolTOutputProtocol.write_bytes
  aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch,
    core.array.Array.index_mut, core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
    thrift.core.io.cursor.Cursor.new, hV.u32, varint_rs.VarintWriterWError.Blanket, rusttrn_model.blanketBase,
    core.slice.index.SliceIndexRangeFullSlice.index_mut, hv, hbuf0, hwb5, thrift.core.io.cursor.Cursor.position,
    Array.index_SliceIndexRangeToUsizeSlice, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    UScalar.cast_val_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, id_eq]
  have hmax : 5 ≤ Usize.max := by scalar_tac
  have hk6 : ∀ k, k < 6 → k % 2 ^ System.Platform.numBits = k := fun k hk => by
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  revert hL
  generalize rusttrn_model.leb128 b.length = L at hlen ⊢
  intro hL
  match L, hlen with
  | [], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t1 ht1
    aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch]
    apply wp_write_all hW
    intro t2 ht2
    aeneas_wp [core.result.Result.map_err_ok]
    refine ⟨t2, rfl, ?_⟩
    rw [ht2, ht1]
    simp only [Slice.from_val, List.map_append, ← hL, List.append_assoc]
  | [a], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t1 ht1
    aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch]
    apply wp_write_all hW
    intro t2 ht2
    aeneas_wp [core.result.Result.map_err_ok]
    refine ⟨t2, rfl, ?_⟩
    rw [ht2, ht1]
    simp only [Slice.from_val, List.map_append, ← hL, List.append_assoc]
  | [a, b], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t1 ht1
    aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch]
    apply wp_write_all hW
    intro t2 ht2
    aeneas_wp [core.result.Result.map_err_ok]
    refine ⟨t2, rfl, ?_⟩
    rw [ht2, ht1]
    simp only [Slice.from_val, List.map_append, ← hL, List.append_assoc]
  | [a, b, c], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t1 ht1
    aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch]
    apply wp_write_all hW
    intro t2 ht2
    aeneas_wp [core.result.Result.map_err_ok]
    refine ⟨t2, rfl, ?_⟩
    rw [ht2, ht1]
    simp only [Slice.from_val, List.map_append, ← hL, List.append_assoc]
  | [a, b, c, d], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t1 ht1
    aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch]
    apply wp_write_all hW
    intro t2 ht2
    aeneas_wp [core.result.Result.map_err_ok]
    refine ⟨t2, rfl, ?_⟩
    rw [ht2, ht1]
    simp only [Slice.from_val, List.map_append, ← hL, List.append_assoc]
  | [a, b, c, d, e], _ =>
    simp [uval_mk, Array.from_slice, Array.to_slice, List.slice, hk6, hmax]
    apply wp_write_all hW
    intro t1 ht1
    aeneas_wp [core.result.Result.Insts.CoreOpsTry.branch]
    apply wp_write_all hW
    intro t2 ht2
    aeneas_wp [core.result.Result.map_err_ok]
    refine ⟨t2, rfl, ?_⟩
    rw [ht2, ht1]
    simp only [Slice.from_val, List.map_append, ← hL, List.append_assoc]

end EquivLean.Demo.Thrift.Rust
