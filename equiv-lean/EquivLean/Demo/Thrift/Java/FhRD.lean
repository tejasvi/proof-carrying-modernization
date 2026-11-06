import EquivLean.Demo.Thrift.Java.FhRP
import EquivLean.Demo.Thrift.Java.Zz

/-!
# Thrift → Java (T4): the field header reader on specified headers (D) and on the named inputs (M)
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem ofNat32_ne_zero {d : Nat} (h0 : 0 < d) (h1 : d < 2 ^ 32) : BitVec.ofNat 32 d ≠ 0#32 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1] at this
  rw [this] at h0
  exact absurd h0 (by decide)

/-- The short form: `(short) (last + delta)` is the id. -/
theorem short_id {last id : I32} (his : JInt.toShort id = id)
    (hd : 1 ≤ id.toInt - last.toInt ∧ id.toInt - last.toInt ≤ 15) :
    JInt.toShort (last + BitVec.ofNat 32 (id.toInt - last.toInt).toNat) = id := by
  have hl : -2147483648 ≤ id.toInt := BitVec.le_toInt id
  have hu : id.toInt < 2147483648 := BitVec.toInt_lt
  have hadd : last + BitVec.ofNat 32 (id.toInt - last.toInt).toNat = id := by
    apply BitVec.toInt_inj.mp
    rw [BitVec.toInt_add, BitVec.toInt_ofNat']
    have h1 : (((id.toInt - last.toInt).toNat : Nat) : Int) = id.toInt - last.toInt :=
      Int.toNat_of_nonneg (by omega)
    rw [h1, Int.bmod_eq_of_le (n := id.toInt - last.toInt) (m := 2 ^ 32) (by omega) (by omega),
      show last.toInt + (id.toInt - last.toInt) = id.toInt by omega]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [hadd, his]

/-- The long form: `(short) zigzagToInt(zigzag id)` is the id. -/
theorem long_id {id : I32} (his : JInt.toShort id = id) :
    JInt.toShort (uzzJ (BitVec.ofNat 32 (Spec.zigzag id.toInt))) = id := by
  have hz := Spec.zigzag_lt32 (inI32_toInt id)
  have h : uzzJ (BitVec.ofNat 32 (Spec.zigzag id.toInt)) = id := by
    apply BitVec.toInt_inj.mp
    unfold uzzJ
    rw [uzz32_val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hz, Spec.unzigzag_zigzag]
  rw [h, his]

/-- **D for the field header**: on `fieldHeader last id ty ++ rest` (a type nibble `ty ≥ 1` with
a TType, `id` a `short`), `readFieldBegin()` returns a new `TField` with the TType of `ty` and
the id `id`, sets `lastFieldId_ = id`, and leaves `rest`. -/
theorem rfb_D (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) {σ : State} {p t tmp : Addr} {fs : List (FieldKey × Value)} {last id : I32}
    {ty : Nat} {rest : Bytes} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hty : 1 ≤ ty ∧ ty < 16) (htt : (Spec.ttypeOfCompact ty).isSome)
    (his : JInt.toShort id = id)
    (hsrc : R.src σ t = Spec.fieldHeader last.toInt id.toInt ty ++ rest)
    (hm : MExec P rfbRef [.ref p] σ o) :
    ∃ tt σ' r0 ffs, Spec.ttypeOfCompact ty = some tt ∧ o = .normal (some (.ref r0)) σ' ∧
      σ'.heap r0 = some (.plain tfCls ffs) ∧
      Fields.get ffs (tfCls, "type") = some (.int (BitVec.ofNat 32 tt)) ∧
      Fields.get ffs (tfCls, "id") = some (.int id) ∧ R.src σ' t = rest ∧
      R.sink σ' t = R.sink σ t ∧ LastAt σ' p id ∧ CPAt P R σ' p t tmp := by
  obtain ⟨u, rest0, hs, hu, hnib, hfid⟩ : ∃ u rest0, R.src σ t = u :: rest0 ∧ u.toNat ≠ 0 ∧
      u.toNat % 16 = ty ∧ fieldIdJ last (BitVec.signExtend 32 u.toBitVec) rest0 = some (id, rest) := by
    by_cases hd : 1 ≤ id.toInt - last.toInt ∧ id.toInt - last.toInt ≤ 15
    · rw [Spec.fieldHeader_short hd hty.2, List.cons_append, List.nil_append] at hsrc
      have hb : (UInt8.ofNat (16 * (id.toInt - last.toInt).toNat + ty)).toNat =
          16 * (id.toInt - last.toInt).toNat + ty := by
        rw [UInt8.toNat_ofNat']; omega
      have hq : (16 * (id.toInt - last.toInt).toNat + ty) / 16 = (id.toInt - last.toInt).toNat := by
        omega
      refine ⟨_, rest, hsrc, by rw [hb]; omega, by rw [hb]; omega, ?_⟩
      have hm0 : ¬ modJ (BitVec.signExtend 32 (UInt8.ofNat (16 * (id.toInt - last.toInt).toNat + ty)).toBitVec) = 0#32 := by
        rw [modJ_sx, hb, hq]
        exact ofNat32_ne_zero (by omega) (by omega)
      rw [fieldIdJ_short hm0, modJ_sx, hb, hq, short_id his hd]
    · rw [Spec.fieldHeader_long hd, List.cons_append] at hsrc
      have hb : (UInt8.ofNat ty).toNat = ty := by rw [UInt8.toNat_ofNat']; omega
      refine ⟨_, _, hsrc, by rw [hb]; omega, by rw [hb]; omega, ?_⟩
      have hz := Spec.zigzag_lt32 (inI32_toInt id)
      have hm0 : modJ (BitVec.signExtend 32 (UInt8.ofNat ty).toBitVec) = 0#32 := by
        rw [modJ_sx, hb, Nat.div_eq_of_lt hty.2]
      rw [fieldIdJ_long hm0 (Spec.readVarint_varint 5 _ rest (Spec.varint_length_le5 hz)), long_id his]
  rcases rfb_run R hF hV hn hCP hp hlast hB h1 h2 h3 hs hu (by rw [hnib]; exact htt) hm with
    ⟨tt, id', rest', σ', r0, ffs, htt', hf, ho, hr0, hty', hid, hs', hk, hL, hC, -⟩ | ⟨e, σ', -, hf, -⟩
  · rw [hfid] at hf
    simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    rw [hnib] at htt'
    exact ⟨tt, σ', r0, ffs, htt', ho, hr0, hty', hid, hs', hk, hL, hC⟩
  · rw [hfid] at hf
    cases hf

/-- A header byte `u ≠ 0` with a known type nibble, when `readFieldId` gives `id`. -/
theorem rfb_inst (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) {σ : State} {p t tmp : Addr} {fs : List (FieldKey × Value)} {last id : I32}
    {u : UInt8} {rest0 rest' : Bytes} {tt : Nat} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int last)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hsrc : R.src σ t = u :: rest0) (hu : u.toNat ≠ 0)
    (htt : Spec.ttypeOfCompact (u.toNat % 16) = some tt)
    (hfid : fieldIdJ last (BitVec.signExtend 32 u.toBitVec) rest0 = some (id, rest'))
    (hm : MExec P rfbRef [.ref p] σ o) :
    ∃ σ' r0 ffs, o = .normal (some (.ref r0)) σ' ∧ σ'.heap r0 = some (.plain tfCls ffs) ∧
      Fields.get ffs (tfCls, "type") = some (.int (BitVec.ofNat 32 tt)) ∧
      Fields.get ffs (tfCls, "id") = some (.int id) ∧ R.src σ' t = rest' ∧
      R.sink σ' t = R.sink σ t ∧ LastAt σ' p id ∧ CPAt P R σ' p t tmp := by
  rcases rfb_run R hF hV hn hCP hp hlast hB h1 h2 h3 hsrc hu (by rw [htt]; rfl) hm with
    ⟨tt', id', rest'', σ', r0, ffs, htt', hf, ho, hr0, hty', hid, hs', hk, hL, hC, -⟩ |
      ⟨e, σ', -, hf, -⟩
  · rw [hfid] at hf
    simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    rw [htt] at htt'
    simp only [Option.some.injEq] at htt'
    subst htt'
    exact ⟨σ', r0, ffs, ho, hr0, hty', hid, hs', hk, hL, hC⟩
  · rw [hfid] at hf
    cases hf

/-! ## The named inputs -/

/-- **`exStopNibble` `[0x10]` after id 0** (statement 2 of `readFieldBegin`, `if type != 0`, then
`readFieldId`): Java returns a new `TField` of type 0 (`TType.STOP`) with id 1 and sets
`lastFieldId_ = 1`; the specification rejects the input (`StopNibble`). -/
theorem rfb_exStopNibble (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) {σ : State} {p t tmp : Addr} {fs : List (FieldKey × Value)} {rest : Bytes}
    {o : Outcome} (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int 0#32)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hsrc : R.src σ t = Spec.exStopNibble ++ rest) (hm : MExec P rfbRef [.ref p] σ o) :
    Spec.readFieldHeader 0 Spec.exStopNibble = none ∧
    ∃ σ' r0 ffs, o = .normal (some (.ref r0)) σ' ∧ σ'.heap r0 = some (.plain tfCls ffs) ∧
      Fields.get ffs (tfCls, "type") = some (.int 0#32) ∧ Fields.get ffs (tfCls, "id") = some (.int 1#32) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ LastAt σ' p 1#32 ∧ CPAt P R σ' p t tmp := by
  refine ⟨Spec.exStopNibble_malformed.2, ?_⟩
  have hfid : fieldIdJ 0#32 (BitVec.signExtend 32 (0x10 : UInt8).toBitVec) rest = some (1#32, rest) := by
    rw [fieldIdJ_short (b := BitVec.signExtend 32 (0x10 : UInt8).toBitVec) (by decide)]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    decide
  exact rfb_inst R hF hV hn hCP hp hlast hB h1 h2 h3 hsrc (by decide) (by decide) hfid hm

/-- **`[0x15]` after id 32767** (the one-byte header a writer that wraps the `i16` delta gives for
`exI16Overflow`): Java returns a new `TField` of type 8 (`TType.I32`) with id −32768
(`(short) (32767 + 1)`) and sets `lastFieldId_ = −32768`; the specification rejects the input
(`DeltaIdOverflow`). -/
theorem rfb_I16Overflow_short (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) {σ : State} {p t tmp : Addr} {fs : List (FieldKey × Value)} {rest : Bytes}
    {o : Outcome} (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int 32767#32)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hsrc : R.src σ t = [0x15] ++ rest) (hm : MExec P rfbRef [.ref p] σ o) :
    Spec.readFieldHeader 32767 [0x15] = none ∧
    ∃ σ' r0 ffs, o = .normal (some (.ref r0)) σ' ∧ σ'.heap r0 = some (.plain tfCls ffs) ∧
      Fields.get ffs (tfCls, "type") = some (.int 8#32) ∧
      Fields.get ffs (tfCls, "id") = some (.int (BitVec.ofInt 32 (-32768))) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ LastAt σ' p (BitVec.ofInt 32 (-32768)) ∧
      CPAt P R σ' p t tmp := by
  refine ⟨Spec.readFieldHeader_exI16Overflow_short, ?_⟩
  have hfid : fieldIdJ 32767#32 (BitVec.signExtend 32 (0x15 : UInt8).toBitVec) rest =
      some (BitVec.ofInt 32 (-32768), rest) := by
    rw [fieldIdJ_short (b := BitVec.signExtend 32 (0x15 : UInt8).toBitVec) (by decide)]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    decide
  exact rfb_inst R hF hV hn hCP hp hlast hB h1 h2 h3 hsrc (by decide) (by decide) hfid hm

/-- **`exIdOutOfRange` `[0x05, 0x80, 0x80, 0x04]` after id 0**: the long-form id is the zigzag
varint 65536; Java returns a new `TField` of type 8 (`TType.I32`) with id −32768
(`(short) zigzagToInt(65536)`, `(short) 32768`) and sets `lastFieldId_ = −32768`; the
specification rejects the input (`IdOutOfRange`, the id 32768). -/
theorem rfb_exIdOutOfRange (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) {σ : State} {p t tmp : Addr} {fs : List (FieldKey × Value)} {rest : Bytes}
    {o : Outcome} (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int 0#32)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hsrc : R.src σ t = Spec.exIdOutOfRange ++ rest) (hm : MExec P rfbRef [.ref p] σ o) :
    Spec.readFieldHeader 0 Spec.exIdOutOfRange = none ∧
    ∃ σ' r0 ffs, o = .normal (some (.ref r0)) σ' ∧ σ'.heap r0 = some (.plain tfCls ffs) ∧
      Fields.get ffs (tfCls, "type") = some (.int 8#32) ∧
      Fields.get ffs (tfCls, "id") = some (.int (BitVec.ofInt 32 (-32768))) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ LastAt σ' p (BitVec.ofInt 32 (-32768)) ∧
      CPAt P R σ' p t tmp := by
  refine ⟨Spec.exIdOutOfRange_malformed.2.2.2, ?_⟩
  have hs : R.src σ t = (0x05 : UInt8) :: (Spec.varint 65536 ++ rest) := by
    rw [hsrc]; rfl
  have hv : Spec.readVarint 5 (Spec.varint 65536 ++ rest) = some (65536, rest) :=
    Spec.readVarint_varint 5 65536 rest (by decide)
  have hfid : fieldIdJ 0#32 (BitVec.signExtend 32 (0x05 : UInt8).toBitVec) (Spec.varint 65536 ++ rest) =
      some (BitVec.ofInt 32 (-32768), rest) := by
    rw [fieldIdJ_long (b := BitVec.signExtend 32 (0x05 : UInt8).toBitVec) (by decide) hv]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    decide
  exact rfb_inst R hF hV hn hCP hp hlast hB h1 h2 h3 hs (by decide) (by decide) hfid hm

/-- **`[0x05, 0x1E]` after id 0** (the long form of `exDelta15`): Java returns a new `TField` of
type 8 (`TType.I32`) with id 15; the specification reads the same field. -/
theorem rfb_exDelta15_long (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC]) (hV : Valid P (tContracts R).env)
    (hn : NoRedeclR P) {σ : State} {p t tmp : Addr} {fs : List (FieldKey × Value)} {rest : Bytes}
    {o : Outcome} (hCP : CPAt P R σ p t tmp) (hp : σ.heap p = some (.plain cpCls fs))
    (hlast : Fields.get fs (cpCls, "lastFieldId_") = some (.int 0#32)) (hB : BoolAt σ p)
    (h1 : σ.initOf tpeCls = .done) (h2 : σ.initOf cpCls = .done) (h3 : σ.initOf tfCls = .done)
    (hsrc : R.src σ t = [0x05, 0x1E] ++ rest) (hm : MExec P rfbRef [.ref p] σ o) :
    Spec.readFieldHeader 0 [0x05, 0x1E] = some (.field 5 15, []) ∧
    ∃ σ' r0 ffs, o = .normal (some (.ref r0)) σ' ∧ σ'.heap r0 = some (.plain tfCls ffs) ∧
      Fields.get ffs (tfCls, "type") = some (.int 8#32) ∧ Fields.get ffs (tfCls, "id") = some (.int 15#32) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ LastAt σ' p 15#32 ∧ CPAt P R σ' p t tmp := by
  refine ⟨Spec.readFieldHeader_exDelta15_long, ?_⟩
  have hs : R.src σ t = (0x05 : UInt8) :: (Spec.varint 30 ++ rest) := by
    rw [hsrc]; rfl
  have hv : Spec.readVarint 5 (Spec.varint 30 ++ rest) = some (30, rest) :=
    Spec.readVarint_varint 5 30 rest (by decide)
  have hfid : fieldIdJ 0#32 (BitVec.signExtend 32 (0x05 : UInt8).toBitVec) (Spec.varint 30 ++ rest) =
      some (15#32, rest) := by
    rw [fieldIdJ_long (b := BitVec.signExtend 32 (0x05 : UInt8).toBitVec) (by decide) hv]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    decide
  exact rfb_inst R hF hV hn hCP hp hlast hB h1 h2 h3 hs (by decide) (by decide) hfid hm

end EquivLean.Demo.Thrift.Java
