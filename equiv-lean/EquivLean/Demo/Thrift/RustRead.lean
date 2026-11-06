import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact___thrift__protocol__compact__TCompactInputProtocol_T____read_varint32
import EquivLean.Demo.Gen.Aeneas.ThriftRs.F_protocol__compact___thrift__protocol__compact__TCompactInputProtocol_T____read_varint64
import EquivLean.Demo.Thrift.RustContracts
import EquivLean.Bridge.Aeneas.Tactic
import EquivLean.Bridge.Aeneas.SpecAuto

/-!
# Thrift (T4), Rust side: the compact protocol's readers

The Rust readers (`lib/rs/src/protocol/compact.rs` at f0eb8b84e, through Aeneas) on a generic transport, under
the transport contract `ReadContract` and the library contract `StdContract` (`RustContracts.lean`).
-/

open Aeneas Aeneas.Std Result EquivLean EquivLean.Aeneas thrift

namespace EquivLean.Demo.Thrift.Rust

/-! ## `read_byte` -/

theorem read_byte_ok (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (b : U8) (bs : List U8) (h : rem self.transport = b :: bs) :
    ∃ t', protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_byte inst self =
      ok (.Ok b, { self with transport := t' }) ∧ rem t' = bs := by
  have hs : (Array.to_slice (Array.repeat 1#usize (0#u8))).length ≤ (rem self.transport).length := by
    rw [h]
    simp [Array.to_slice, Slice.length]
  obtain ⟨t', s', hre, hs', ht'⟩ := hR.read_exact_ok self.transport _ hs
  refine ⟨t', ?_, ?_⟩
  · apply eq_ok_of_wp
    unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_byte
    have hlen : s'.val.length = (1#usize).val := by
      rw [hs', h]
      simp [Array.to_slice, Slice.length]
    have hb : (Array.from_slice (Array.repeat 1#usize (0#u8)) s').val = [b] := by
      rw [Array.from_slice_val _ _ hlen, hs', h]
      simp [Array.to_slice, Slice.length]
    aeneas_wp [Array.to_slice_mut, hre, core.result.Result.map_err_ok, hS.map_ok,
      protocol.compact.TInputProtocolTCompactInputProtocol.read_byte.closure.Insts.CoreOpsFunctionFnOnceTupleTupleU8,
      protocol.compact.TInputProtocolTCompactInputProtocol.read_byte.closure.Insts.CoreOpsFunctionFnOnceTupleTupleU8.call_once,
      array_index_usize_eq, hb]
    simp
  · rw [ht', h]
    simp [Array.to_slice, Slice.length]

/-- At the end of the input, `read_byte` returns the transport error `EndOfFile` (`From<io::Error>` of the
transport's `UnexpectedEof`). -/
theorem read_byte_eof (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (h : rem self.transport = []) :
    ∃ t' m, protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_byte inst self =
      ok (.Err (.Transport { kind := .EndOfFile, message := m }), { self with transport := t' }) := by
  have hs : (rem self.transport).length < (Array.to_slice (Array.repeat 1#usize (0#u8))).length := by
    rw [h]
    simp [Array.to_slice, Slice.length]
  obtain ⟨e, t', s', hre, hk⟩ := hR.read_exact_eof self.transport _ hs
  obtain ⟨m, hm⟩ := hS.io_to_string e
  refine ⟨t', m, ?_⟩
  apply eq_ok_of_wp
  unfold protocol.compact.TCompactInputProtocol.Insts.ThriftProtocolTInputProtocol.read_byte
  aeneas_wp [Array.to_slice_mut, hre, core.result.Result.map_err_err, hS.map_err,
    P.Insts.CoreOpsFunctionFnOnceTupleErrorError, P.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    errors.Error.Insts.CoreConvertFromError.from, hk, hm]

/-! ## The range iterator of the varint loops -/

theorem range_next_usize_lt (i e : Usize) (h : i.val < e.val) :
    ∃ i', core.iter.range.IteratorRange.next core.iter.range.StepUsize { start := i, «end» := e } =
      ok (some i, { start := i', «end» := e }) ∧ i'.val = i.val + 1 := by
  have hm : i.val < UScalar.max .Usize := by scalar_tac
  refine ⟨UScalar.ofNatCore (i.val + 1) (by scalar_tac), ?_, by simp⟩
  unfold core.iter.range.IteratorRange.next
  simp [core.iter.range.UScalarStep, core.iter.range.UScalarStep.forward_checked, h, hm,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, liftFun2, core.clone.CloneUsize]

theorem range_next_usize_ge (i e : Usize) (h : e.val ≤ i.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize { start := i, «end» := e } =
      ok (none, { start := i, «end» := e }) := by
  have h' : ¬ i.val < e.val := by omega
  unfold core.iter.range.IteratorRange.next
  simp [core.iter.range.UScalarStep, h', core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt,
    liftFun2]

/-! ## Varints -/

/-- The outcome of reading a varint of at most `k` bytes: the value of its 7-bit groups (least significant first,
unbounded) and the bytes after it; `overlong` when all `k` bytes have the continuation bit; `eof` when the input ends
first. -/
inductive VarDec where
  | ok (v : Nat) (rest : List U8)
  | overlong
  | eof

/-- The reference decoder: at most `k` bytes. -/
def decVar : Nat → List U8 → VarDec
  | 0, _ => .overlong
  | _ + 1, [] => .eof
  | k + 1, b :: bs =>
    if b.val < 128 then .ok b.val bs
    else match decVar k bs with
      | .ok v rest => .ok (b.val - 128 + 128 * v) rest
      | r => r

/-- Rust's varint loop on the transport's bytes: `k` iterations left, value `acc` and shift `sh` so far, in `w` bits
(`result |= ((b & 0x7F) as uw) << shift`). -/
def rdLoop (w : Nat) : Nat → Nat → Nat → List U8 → VarDec
  | 0, _, _, _ => .overlong
  | _ + 1, _, _, [] => .eof
  | k + 1, acc, sh, b :: bs =>
    if b.val < 128 then .ok (acc ||| (b.val % 128 * 2 ^ sh % 2 ^ w)) bs
    else rdLoop w k (acc ||| (b.val % 128 * 2 ^ sh % 2 ^ w)) (sh + 7) bs

/-- A varint reader's result against the outcome `d`: the value (in `ty`) and the bytes left, the protocol error
`InvalidData` with the message `msg`, or the transport error `EndOfFile`. -/
def OutVar {ty : UScalarTy} (msg : Str) (d : VarDec) (r : core.result.Result (UScalar ty) errors.Error)
    (left : List U8) : Prop :=
  match d with
  | .ok v rest => (∃ x : UScalar ty, r = .Ok x ∧ x.val = v) ∧ left = rest
  | .overlong => ∃ m, alloc.string.String.Insts.CoreConvertFromShared0Str.from msg = ok m ∧
      r = .Err (.Protocol { kind := .InvalidData, message := m })
  | .eof => ∃ m, r = .Err (.Transport { kind := .EndOfFile, message := m })

theorem and128_val (b : U8) : (b &&& 128#u8).val = 0 ↔ b.val < 128 := by
  rw [UScalar.val_and, show (128#u8 : U8).val = 128 from rfl]
  have hb : b.val < 256 := by scalar_tac
  have key : ∀ n < 256, (n &&& 128 = 0 ↔ n < 128) := by decide +kernel
  exact key _ hb

theorem cast_and127_val (ty : UScalarTy) (b : U8) (h : 7 ≤ ty.numBits) :
    (UScalar.cast ty (b &&& 127#u8)).val = b.val % 128 := by
  rw [UScalar.cast_val_eq, UScalar.val_and, show (127#u8 : U8).val = 2 ^ 7 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.mod_eq_of_lt
  have : b.val % 2 ^ 7 < 2 ^ 7 := Nat.mod_lt _ (by decide)
  have : 2 ^ 7 ≤ 2 ^ ty.numBits := Nat.pow_le_pow_right (by decide) h
  omega

theorem or_shl_val {ty : UScalarTy} (result c : UScalar ty) (sh : Nat) :
    (result ||| (⟨c.bv <<< sh⟩ : UScalar ty)).val = result.val ||| (c.val * 2 ^ sh % 2 ^ ty.numBits) := by
  rw [UScalar.val_or]
  congr 1
  show (c.bv <<< sh).toNat = c.val * 2 ^ sh % 2 ^ ty.numBits
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rfl

/-- The state of `read_varint32`'s loop `(iter, self, result, shift)`: `iter` = `start..5`, `shift = 7 * start`, only
the transport has changed, and the rest of the loop gives `D`. -/
def LoopInv32 {T : Type} (rem : T → List U8) (self0 : protocol.compact.TCompactInputProtocol T) (D : VarDec)
    (st : core.ops.range.Range Usize × protocol.compact.TCompactInputProtocol T × U32 × U32) : Prop :=
  st.1.end.val = 5 ∧ st.1.start.val ≤ 5 ∧ st.2.2.2.val = 7 * st.1.start.val ∧
    st.2.1 = { self0 with transport := st.2.1.transport } ∧
    rdLoop 32 (5 - st.1.start.val) st.2.2.1.val st.2.2.2.val (rem st.2.1.transport) = D

set_option maxHeartbeats 4000000 in
theorem read_varint32_loop_spec (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self0 : protocol.compact.TCompactInputProtocol T)
    (D : VarDec) (iter : core.ops.range.Range Usize) (self : protocol.compact.TCompactInputProtocol T)
    (result shift : U32) (hinv : LoopInv32 rem self0 D (iter, self, result, shift)) :
    wp (protocol.compact.TCompactInputProtocol.read_varint32_loop inst iter self result shift)
      (fun o => ∃ r s', o = .ok (r, s') ∧ s' = { self0 with transport := s'.transport } ∧
        OutVar (toStr "Variable-length int over 5 bytes.") D r (rem s'.transport)) := by
  unfold protocol.compact.TCompactInputProtocol.read_varint32_loop
  refine wp_loop (loop_shape _) (LoopInv32 rem self0 D) (fun st => 5 - st.1.start.val) ?_ _ hinv
  simp only [Prod.forall]
  intro iter self result shift hinv
  obtain ⟨hend, hstart, hsh, hself, hD⟩ := hinv
  dsimp only at hend hstart hsh hself hD
  subst hD
  obtain ⟨i, e⟩ := iter
  dsimp only at hend hstart hsh ⊢
  simp only [protocol.compact.TCompactInputProtocol.read_varint32_loop.body]
  by_cases hlt : i.val < 5
  · obtain ⟨i', hnext, hi'⟩ := range_next_usize_lt i e (by omega)
    have h5 : 5 - i.val = (4 - i.val) + 1 := by omega
    rcases hb : rem self.transport with _ | ⟨b, bs⟩
    · obtain ⟨t', m, hrb⟩ := read_byte_eof hS hR self hb
      aeneas_wp [hnext, hrb, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, loopCls_done,
        core.convert.FromSame, core.convert.FromSame.from]
      refine ⟨_, _, rfl, by rw [hself], ?_⟩
      rw [h5, rdLoop]
      exact ⟨m, rfl⟩
    · obtain ⟨t', hrb, ht'⟩ := read_byte_ok hS hR self b bs hb
      have hsh32 : shift.val < 32 := by omega
      have hsh' : shift.val ≤ 4294967288 := by omega
      aeneas_wp [hnext, hrb, core.result.Result.Insts.CoreOpsTry.branch, loopCls_done, loopCls_cont,
        hsh32, hsh', and128_val]
      rw [h5, rdLoop]
      by_cases hlo : b.val < 128
      · simp only [hlo, _root_.ite_true]
        refine ⟨_, _, rfl, by rw [hself], ⟨_, rfl, ?_⟩, ht'⟩
        rw [or_shl_val, cast_and127_val _ _ (by decide)]
        simp
      · simp only [hlo, _root_.ite_false, _root_.dite_true, LoopInv32, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, by omega, by omega, by rw [hself], ?_⟩, by omega⟩
        rw [ht', hi', show 5 - (i.val + 1) = 4 - i.val by omega, or_shl_val,
          cast_and127_val _ _ (by decide)]
        simp [hsh]
  · have hnext := range_next_usize_ge i e (by omega)
    obtain ⟨m, hm⟩ := hS.str_from (toStr "Variable-length int over 5 bytes.")
    aeneas_wp [hnext, loopCls_done, errors.ProtocolError.new, core.convert.IntoFrom,
      core.convert.IntoFrom.into, hm]
    refine ⟨_, _, rfl, hself, ?_⟩
    rw [show 5 - i.val = 0 by omega, rdLoop]
    exact ⟨m, hm, rfl⟩

/-- `read_varint32` (all inputs): the Rust loop's outcome on the transport's bytes. -/
theorem read_varint32_wp (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T) :
    wp (protocol.compact.TCompactInputProtocol.read_varint32 inst self)
      (fun o => ∃ r s', o = .ok (r, s') ∧ s' = { self with transport := s'.transport } ∧
        OutVar (toStr "Variable-length int over 5 bytes.") (rdLoop 32 5 0 0 (rem self.transport)) r
          (rem s'.transport)) :=
  read_varint32_loop_spec hS hR self _ _ self 0#u32 0#u32
    ⟨by simp [protocol.compact.MAX_VARINT32_BYTES], by simp, by simp, rfl, by simp⟩

/-! ## The varint arithmetic -/

/-- A 7-bit group OR-ed into the accumulator below it is an addition (modulo the width). -/
theorem lor_shift_eq (acc c sh w : Nat) (h1 : acc < 2 ^ sh) (h2 : acc < 2 ^ w) :
    acc ||| (c * 2 ^ sh % 2 ^ w) = (acc + c * 2 ^ sh) % 2 ^ w := by
  by_cases hw : w ≤ sh
  · have hd : 2 ^ w ∣ c * 2 ^ sh := Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 hw) c
    obtain ⟨q, hq⟩ := hd
    rw [hq, Nat.mul_mod_right, Nat.or_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
  · obtain ⟨d, rfl⟩ : ∃ d, w = sh + d := ⟨w - sh, by omega⟩
    have hpow : 2 ^ (sh + d) = 2 ^ d * 2 ^ sh := by rw [Nat.pow_add, Nat.mul_comm]
    have hmod : c * 2 ^ sh % (2 ^ d * 2 ^ sh) = (c % 2 ^ d) * 2 ^ sh := Nat.mul_mod_mul_right _ c _
    have hor : acc ||| (c % 2 ^ d) * 2 ^ sh = 2 ^ sh * (c % 2 ^ d) + acc := by
      rw [Nat.lor_comm, Nat.mul_comm (c % 2 ^ d) (2 ^ sh)]
      exact (Nat.two_pow_add_eq_or_of_lt h1 (c % 2 ^ d)).symm
    have hc := Nat.mod_add_div c (2 ^ d)
    have hlt : c % 2 ^ d < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)
    have hle : 2 ^ sh * (c % 2 ^ d) + 2 ^ sh ≤ 2 ^ sh * 2 ^ d := by
      have := Nat.mul_le_mul_left (2 ^ sh) (Nat.succ_le_of_lt hlt)
      rwa [Nat.mul_succ] at this
    have hsplit : acc + c * 2 ^ sh =
        (acc + 2 ^ sh * (c % 2 ^ d)) + (2 ^ d * 2 ^ sh) * (c / 2 ^ d) := by
      calc acc + c * 2 ^ sh = acc + (c % 2 ^ d + 2 ^ d * (c / 2 ^ d)) * 2 ^ sh := by rw [hc]
        _ = _ := by ring
    have hcomm : 2 ^ sh * 2 ^ d = 2 ^ d * 2 ^ sh := Nat.mul_comm _ _
    have h3 : acc + 2 ^ sh * (c % 2 ^ d) < 2 ^ d * 2 ^ sh := by omega
    calc acc ||| (c * 2 ^ sh % 2 ^ (sh + d))
        = acc ||| (c % 2 ^ d) * 2 ^ sh := by rw [hpow, hmod]
      _ = 2 ^ sh * (c % 2 ^ d) + acc := hor
      _ = (acc + c * 2 ^ sh) % 2 ^ (sh + d) := by
        rw [hpow, hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h3]
        omega

/-- The outcome with its value mapped. -/
def VarDec.mapV (f : Nat → Nat) : VarDec → VarDec
  | .ok v rest => .ok (f v) rest
  | .overlong => .overlong
  | .eof => .eof

/-- Rust's loop is the reference decoder, with the value cut to `w` bits. -/
theorem rdLoop_eq (w : Nat) : ∀ (k acc sh : Nat) (bs : List U8), acc < 2 ^ sh → acc < 2 ^ w →
    rdLoop w k acc sh bs = (decVar k bs).mapV (fun v => (acc + v * 2 ^ sh) % 2 ^ w)
  | 0, _, _, _, _, _ => by simp [rdLoop, decVar, VarDec.mapV]
  | k + 1, acc, sh, [], _, _ => by simp [rdLoop, decVar, VarDec.mapV]
  | k + 1, acc, sh, b :: bs, h1, h2 => by
    have hb : b.val < 256 := by scalar_tac
    have hor := lor_shift_eq acc (b.val % 128) sh w h1 h2
    by_cases hlo : b.val < 128
    · simp only [rdLoop, decVar, hlo, _root_.ite_true, VarDec.mapV]
      rw [hor, Nat.mod_eq_of_lt hlo]
    · have hc : b.val % 128 = b.val - 128 := by omega
      have hacc1 : (acc + b.val % 128 * 2 ^ sh) % 2 ^ w < 2 ^ (sh + 7) := by
        have : b.val % 128 * 2 ^ sh ≤ 127 * 2 ^ sh := Nat.mul_le_mul_right _ (by omega)
        have : 2 ^ (sh + 7) = 128 * 2 ^ sh := by rw [Nat.pow_add]; ring
        have := Nat.mod_le (acc + b.val % 128 * 2 ^ sh) (2 ^ w)
        omega
      have hacc2 : (acc + b.val % 128 * 2 ^ sh) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
      simp only [rdLoop, decVar, hlo, _root_.ite_false, hor]
      rw [rdLoop_eq w k _ (sh + 7) bs hacc1 hacc2]
      cases decVar k bs with
      | ok v rest =>
        simp only [VarDec.mapV, VarDec.ok.injEq, and_true]
        rw [Nat.mod_add_mod, hc, Nat.pow_add]
        congr 1
        ring
      | overlong => rfl
      | eof => rfl

/-- The unsigned varint of `n`, as byte values. -/
def encVar (n : Nat) : List Nat := if n < 128 then [n] else (n % 128 + 128) :: encVar (n / 128)
termination_by n
decreasing_by omega

theorem encVar_length_le (n k : Nat) (h : n < 2 ^ (7 * (k + 1))) : (encVar n).length ≤ k + 1 := by
  induction k generalizing n with
  | zero =>
    rw [encVar]
    have : n < 128 := by simpa using h
    simp [this]
  | succ k ih =>
    rw [encVar]
    split_ifs with h128
    · simp
    · simp only [List.length_cons, Nat.add_le_add_iff_right]
      apply ih
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      have : 2 ^ (7 * (k + 1 + 1)) = 2 ^ (7 * (k + 1)) * 128 := by
        rw [show 7 * (k + 1 + 1) = 7 * (k + 1) + 7 by ring, Nat.pow_add]
      omega

/-- The reference decoder reads back the encoding (within `k` bytes). -/
theorem decVar_encVar : ∀ (n k : Nat) (bs rest : List U8), bs.map (·.val) = encVar n →
    (encVar n).length ≤ k → decVar k (bs ++ rest) = .ok n rest := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k bs rest hbs hk
    rw [encVar] at hbs hk
    split_ifs at hbs hk with h128
    · obtain ⟨b, rfl⟩ : ∃ b, bs = [b] := by
        match bs, hbs with
        | [b], _ => exact ⟨b, rfl⟩
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hbs
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
      simp [decVar, hbs, h128]
    · match bs, hbs with
      | b :: bs', hbs =>
        simp only [List.map_cons, List.cons.injEq] at hbs
        obtain ⟨hb, hbs'⟩ := hbs
        simp only [List.length_cons] at hk
        obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have hrec := ih (n / 128) (by omega) k bs' rest hbs' (by omega)
        have hge : ¬ b.val < 128 := by omega
        simp only [List.cons_append, decVar, hge, _root_.ite_false, hrec, VarDec.ok.injEq, and_true]
        omega

/-! ## `read_varint32`: D and M -/

/-- (M, all inputs) `read_varint32` reads the reference decoder's outcome on the transport's bytes (at most 5
bytes): the value cut to 32 bits (a 5-byte varint's bits above bit 31 are dropped) and the transport left after it;
5 bytes with the continuation bit: `InvalidData` "Variable-length int over 5 bytes."; the input ends first: the
transport error `EndOfFile`. Only the transport changes. -/
theorem read_varint32_spec (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T) :
    ∃ r t', protocol.compact.TCompactInputProtocol.read_varint32 inst self =
        ok (r, { self with transport := t' }) ∧
      OutVar (toStr "Variable-length int over 5 bytes.")
        ((decVar 5 (rem self.transport)).mapV (· % 2 ^ 32)) r (rem t') := by
  have h := read_varint32_wp hS hR self
  have hrd : rdLoop 32 5 0 0 (rem self.transport) = (decVar 5 (rem self.transport)).mapV (· % 2 ^ 32) := by
    rw [rdLoop_eq 32 5 0 0 _ (by decide) (by decide)]
    simp
  rw [hrd] at h
  have h' : wp (protocol.compact.TCompactInputProtocol.read_varint32 inst self)
      (fun o => ∃ v : core.result.Result U32 errors.Error × protocol.compact.TCompactInputProtocol T,
        o = .ok v ∧ v.2 = { self with transport := v.2.transport } ∧
        OutVar (toStr "Variable-length int over 5 bytes.")
          ((decVar 5 (rem self.transport)).mapV (· % 2 ^ 32)) v.1 (rem v.2.transport)) :=
    wp_mono h fun o ⟨r, s', ho, h1, h2⟩ => ⟨(r, s'), ho, h1, h2⟩
  obtain ⟨⟨r, s'⟩, ho, hs', hout⟩ := exists_ok_of_wp h'
  refine ⟨r, s'.transport, ?_, hout⟩
  rw [ho]
  dsimp only at hs' ⊢
  rw [← hs']

/-- (D) On a transport holding the varint of `x` and then any bytes `rest`, `read_varint32` returns `x` and leaves
exactly `rest`. -/
theorem read_varint32_D (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (x : U32) (bs rest : List U8) (hbs : bs.map (·.val) = encVar x.val)
    (h : rem self.transport = bs ++ rest) :
    ∃ t', protocol.compact.TCompactInputProtocol.read_varint32 inst self =
      ok (.Ok x, { self with transport := t' }) ∧ rem t' = rest := by
  obtain ⟨r, t', hrv, hout⟩ := read_varint32_spec hS hR self
  have hx : x.val < 2 ^ 32 := by scalar_tac
  have hlen : (encVar x.val).length ≤ 5 := encVar_length_le x.val 4 (by omega)
  rw [h, decVar_encVar x.val 5 bs rest hbs hlen] at hout
  obtain ⟨⟨x', hr, hx'⟩, hrest⟩ := hout
  refine ⟨t', ?_, hrest⟩
  rw [hrv, hr, show x' = x from UScalar.eq_of_val_eq (by rw [hx']; exact Nat.mod_eq_of_lt hx)]

/-- The state of `read_varint64`'s loop `(iter, self, result, shift)`: `iter` = `start..10`, `shift = 7 * start`, only
the transport has changed, and the rest of the loop gives `D`. -/
def LoopInv64 {T : Type} (rem : T → List U8) (self0 : protocol.compact.TCompactInputProtocol T) (D : VarDec)
    (st : core.ops.range.Range Usize × protocol.compact.TCompactInputProtocol T × U64 × U32) : Prop :=
  st.1.end.val = 10 ∧ st.1.start.val ≤ 10 ∧ st.2.2.2.val = 7 * st.1.start.val ∧
    st.2.1 = { self0 with transport := st.2.1.transport } ∧
    rdLoop 64 (10 - st.1.start.val) st.2.2.1.val st.2.2.2.val (rem st.2.1.transport) = D

set_option maxHeartbeats 4000000 in
theorem read_varint64_loop_spec (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self0 : protocol.compact.TCompactInputProtocol T)
    (D : VarDec) (iter : core.ops.range.Range Usize) (self : protocol.compact.TCompactInputProtocol T)
    (result : U64) (shift : U32) (hinv : LoopInv64 rem self0 D (iter, self, result, shift)) :
    wp (protocol.compact.TCompactInputProtocol.read_varint64_loop inst iter self result shift)
      (fun o => ∃ r s', o = .ok (r, s') ∧ s' = { self0 with transport := s'.transport } ∧
        OutVar (toStr "Variable-length int over 10 bytes.") D r (rem s'.transport)) := by
  unfold protocol.compact.TCompactInputProtocol.read_varint64_loop
  refine wp_loop (loop_shape _) (LoopInv64 rem self0 D) (fun st => 10 - st.1.start.val) ?_ _ hinv
  simp only [Prod.forall]
  intro iter self result shift hinv
  obtain ⟨hend, hstart, hsh, hself, hD⟩ := hinv
  dsimp only at hend hstart hsh hself hD
  subst hD
  obtain ⟨i, e⟩ := iter
  dsimp only at hend hstart hsh ⊢
  simp only [protocol.compact.TCompactInputProtocol.read_varint64_loop.body]
  by_cases hlt : i.val < 10
  · obtain ⟨i', hnext, hi'⟩ := range_next_usize_lt i e (by omega)
    have h5 : 10 - i.val = (9 - i.val) + 1 := by omega
    rcases hb : rem self.transport with _ | ⟨b, bs⟩
    · obtain ⟨t', m, hrb⟩ := read_byte_eof hS hR self hb
      aeneas_wp [hnext, hrb, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, loopCls_done,
        core.convert.FromSame, core.convert.FromSame.from]
      refine ⟨_, _, rfl, by rw [hself], ?_⟩
      rw [h5, rdLoop]
      exact ⟨m, rfl⟩
    · obtain ⟨t', hrb, ht'⟩ := read_byte_ok hS hR self b bs hb
      have hsh32 : shift.val < 64 := by omega
      have hsh' : shift.val ≤ 4294967288 := by omega
      aeneas_wp [hnext, hrb, core.result.Result.Insts.CoreOpsTry.branch, loopCls_done, loopCls_cont,
        hsh32, hsh', and128_val]
      rw [h5, rdLoop]
      by_cases hlo : b.val < 128
      · simp only [hlo, _root_.ite_true]
        refine ⟨_, _, rfl, by rw [hself], ⟨_, rfl, ?_⟩, ht'⟩
        rw [or_shl_val, cast_and127_val _ _ (by decide)]
        simp
      · simp only [hlo, _root_.ite_false, _root_.dite_true, LoopInv64, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, by omega, by omega, by rw [hself], ?_⟩, by omega⟩
        rw [ht', hi', show 10 - (i.val + 1) = 9 - i.val by omega, or_shl_val,
          cast_and127_val _ _ (by decide)]
        simp [hsh]
  · have hnext := range_next_usize_ge i e (by omega)
    obtain ⟨m, hm⟩ := hS.str_from (toStr "Variable-length int over 10 bytes.")
    aeneas_wp [hnext, loopCls_done, errors.ProtocolError.new, core.convert.IntoFrom,
      core.convert.IntoFrom.into, hm]
    refine ⟨_, _, rfl, hself, ?_⟩
    rw [show 10 - i.val = 0 by omega, rdLoop]
    exact ⟨m, hm, rfl⟩

/-- `read_varint64` (all inputs): the Rust loop's outcome on the transport's bytes. -/
theorem read_varint64_wp (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T) :
    wp (protocol.compact.TCompactInputProtocol.read_varint64 inst self)
      (fun o => ∃ r s', o = .ok (r, s') ∧ s' = { self with transport := s'.transport } ∧
        OutVar (toStr "Variable-length int over 10 bytes.") (rdLoop 64 10 0 0 (rem self.transport)) r
          (rem s'.transport)) :=
  read_varint64_loop_spec hS hR self _ _ self 0#u64 0#u32
    ⟨by simp [protocol.compact.MAX_VARINT64_BYTES], by simp, by simp, rfl, by simp⟩

/-! ## `read_varint64`: D and M -/

/-- (M, all inputs) `read_varint64` reads the reference decoder's outcome on the transport's bytes (at most 10
bytes): the value cut to 64 bits (a 10-byte varint's bits above bit 63 are dropped) and the transport left after it;
10 bytes with the continuation bit: `InvalidData` "Variable-length int over 10 bytes."; the input ends first: the
transport error `EndOfFile`. Only the transport changes. -/
theorem read_varint64_spec (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T) :
    ∃ r t', protocol.compact.TCompactInputProtocol.read_varint64 inst self =
        ok (r, { self with transport := t' }) ∧
      OutVar (toStr "Variable-length int over 10 bytes.")
        ((decVar 10 (rem self.transport)).mapV (· % 2 ^ 64)) r (rem t') := by
  have h := read_varint64_wp hS hR self
  have hrd : rdLoop 64 10 0 0 (rem self.transport) = (decVar 10 (rem self.transport)).mapV (· % 2 ^ 64) := by
    rw [rdLoop_eq 64 10 0 0 _ (by decide) (by decide)]
    simp
  rw [hrd] at h
  have h' : wp (protocol.compact.TCompactInputProtocol.read_varint64 inst self)
      (fun o => ∃ v : core.result.Result U64 errors.Error × protocol.compact.TCompactInputProtocol T,
        o = .ok v ∧ v.2 = { self with transport := v.2.transport } ∧
        OutVar (toStr "Variable-length int over 10 bytes.")
          ((decVar 10 (rem self.transport)).mapV (· % 2 ^ 64)) v.1 (rem v.2.transport)) :=
    wp_mono h fun o ⟨r, s', ho, h1, h2⟩ => ⟨(r, s'), ho, h1, h2⟩
  obtain ⟨⟨r, s'⟩, ho, hs', hout⟩ := exists_ok_of_wp h'
  refine ⟨r, s'.transport, ?_, hout⟩
  rw [ho]
  dsimp only at hs' ⊢
  rw [← hs']

/-- (D) On a transport holding the varint of `x` and then any bytes `rest`, `read_varint64` returns `x` and leaves
exactly `rest`. -/
theorem read_varint64_D (hS : StdContract) {T : Type} {inst : transport.TReadTransport T}
    {rem : T → List U8} (hR : ReadContract inst rem) (self : protocol.compact.TCompactInputProtocol T)
    (x : U64) (bs rest : List U8) (hbs : bs.map (·.val) = encVar x.val)
    (h : rem self.transport = bs ++ rest) :
    ∃ t', protocol.compact.TCompactInputProtocol.read_varint64 inst self =
      ok (.Ok x, { self with transport := t' }) ∧ rem t' = rest := by
  obtain ⟨r, t', hrv, hout⟩ := read_varint64_spec hS hR self
  have hx : x.val < 2 ^ 64 := by scalar_tac
  have hlen : (encVar x.val).length ≤ 10 := encVar_length_le x.val 9 (by omega)
  rw [h, decVar_encVar x.val 10 bs rest hbs hlen] at hout
  obtain ⟨⟨x', hr, hx'⟩, hrest⟩ := hout
  refine ⟨t', ?_, hrest⟩
  rw [hrv, hr, show x' = x from UScalar.eq_of_val_eq (by rw [hx']; exact Nat.mod_eq_of_lt hx)]

end EquivLean.Demo.Thrift.Rust
