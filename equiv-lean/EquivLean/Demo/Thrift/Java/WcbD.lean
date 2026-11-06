import EquivLean.Demo.Thrift.Java.WfbP

/-!
# Thrift → Java (T4): the compact list/set header writer, definitions

`writeCollectionBegin(elemType, size)`: for `size ≤ 14` the byte `size << 4 | getCompactType(elemType)`
(`writeByteDirect(int)`), else the byte `0xF0 | getCompactType(elemType)` and `writeVarint32(size)`.
`getCompactType` reads the static table `ttypeToCompactType`; it and `writeByteDirect(int)` are
executed inline, `writeByteDirect(byte)` and `writeVarint32(int)` are used through their proved
contracts.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev wcbRef : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«writeCollectionBegin(byte,int)».ref

/-- `ttypeToCompactType` as `TCompactProtocol`'s static initializer leaves it: 18 bytes, entry `e`
is `Spec.compactType e` for the 13 TTypes it names and 0 elsewhere. -/
def ctTable : List Value :=
  [0, 0, 1, 3, 7, 0, 4, 0, 5, 0, 6, 8, 12, 11, 10, 9, 13, 0].map fun n => .int (BitVec.ofNat 32 n)

/-- What `writeCollectionBegin(elemType, size)` guarantees: it appends `listHeader size c`, `c` the
compact type nibble of the TType `elemType`. -/
def wcbN (P : Program) (R : TRep) (args : List Value) (σ : State) (r : Option Value) (σ' : State) :
    Prop :=
  ∀ (p t tmp : Addr) (fs : List (FieldKey × Value)) (et sz : I32) (c : Nat),
    args = [.ref p, .int et, .int sz] →
    σ.heap p = some (.plain cpCls fs) → Fields.get fs (tpCls, "trans_") = some (.ref t) →
    Fields.get fs (cpCls, "temp") = some (.ref tmp) → Spec.compactType et.toNat = some c →
    r = none ∧ R.sink σ' t = R.sink σ t ++ Spec.listHeader sz.toNat c ∧ R.src σ' t = R.src σ t ∧
      CPAt P R σ' p t tmp ∧ PFrame R σ σ' t tmp

attribute [irreducible] wcbN

/-- The precondition: a size `≥ 0`, a TType with a compact nibble, the class initialized with its
table (the table entry stated for the symbolic execution). -/
def wcbSpecI (P : Program) (R : TRep) : Spec := Spec.of
  (fun args σ => ∃ (p t tmp ta : Addr) (et sz : I32) (c : Nat), args = [.ref p, .int et, .int sz] ∧
     CPAt P R σ p t tmp ∧ CPAtH P R σ p t tmp ∧ 0 ≤ sz.toInt ∧ 0 ≤ et.toInt ∧
     et.toInt < (ctTable.length : Int) ∧ Spec.compactType et.toNat = some c ∧ c < 16 ∧
     σ.initOf cpCls = .done ∧ σ.static (cpCls, "ttypeToCompactType") = some (.ref ta) ∧
     σ.heap ta = some (.array (.prim .byte) ctTable) ∧
     ctTable[et.toInt.toNat]? = some (.int (BitVec.ofNat 32 c)) ∧
     (∃ h : et.toInt.toNat < ctTable.length, ctTable[et.toInt.toNat]'h = .int (BitVec.ofNat 32 c)))
  (wcbN P R) (fun _ _ _ _ => False)

/-- The contracts `writeCollectionBegin` uses: `writeByteDirect(byte)`, and `Γ2` (`writeVarint32`). -/
def Γ5 (P : Program) (R : TRep) : SpecEnv := fun sig =>
  if sig = wbdSig then some (wbdSpecA P R) else Γ2 P R sig

/-! ## The closers of the verification conditions -/

theorem byte_short_tab : ∀ n, n < 15 → ∀ c, c < 16 →
    UInt8.ofNat (JInt.toByte (JInt.shl (BitVec.ofNat 32 n) 4#32 ||| BitVec.ofNat 32 c)).toNat =
      UInt8.ofNat (16 * n + c) := by decide

theorem byte_long_tab : ∀ c, c < 16 →
    UInt8.ofNat (JInt.toByte (240#32 ||| JInt.toShort (BitVec.ofNat 32 c))).toNat =
      UInt8.ofNat (0xF0 + c) := by decide

/-- The short form: the byte `size << 4 | c`. -/
theorem wcb_byte_short {sz : I32} {c : Nat} (hn : sz.toNat < 15) (hc : c < 16) :
    UInt8.ofNat (JInt.toByte (JInt.shl sz 4#32 ||| BitVec.ofNat 32 c)).toNat =
      UInt8.ofNat (16 * sz.toNat + c) := by
  have hsub : BitVec.ofNat 32 sz.toNat = sz := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sz.isLt]
  have h := byte_short_tab sz.toNat hn c hc
  rw [hsub] at h
  exact h

/-- A size `≥ 0` as `Nat`. -/
theorem toNat_of_toInt {sz : I32} (h0 : 0 ≤ sz.toInt) : (sz.toNat : Int) = sz.toInt := by
  have e := BitVec.toInt_eq_toNat_cond sz
  have hl := sz.isLt
  split at e <;> omega

/-- The short form (`size ≤ 14`): one call, the byte `size << 4 | c`. -/
theorem wcb_post_short {P : Program} {R : TRep} {σ0 σ1 : State} {p t tmp : Addr} {et sz : I32} {c : Nat}
    (hH0 : CPAtH P R σ0 p t tmp)
    (hct : Spec.compactType et.toNat = some c) (h0 : 0 ≤ sz.toInt) (hcond : ¬ 14 < sz.toInt)
    (hs1 : R.sink σ1 t = R.sink σ0 t ++
      [UInt8.ofNat (JInt.toByte (JInt.shl sz 4#32 ||| BitVec.ofNat 32 c)).toNat])
    (hr1 : R.src σ1 t = R.src σ0 t) (hH1 : CPAtH P R σ1 p t tmp)
    (hn1 : σ0.next ≤ σ1.next) (hi1 : σ1.inits = σ0.inits) (hst1 : σ1.statics = σ0.statics)
    (hh1 : ∀ a, a < σ0.next → ¬a = t → ¬a = tmp → ¬R.owns σ0 t a → σ1.heap a = σ0.heap a) :
    wcbN P R [.ref p, .int et, .int sz] σ0 none σ1 := by
  have hC0 := CPAtH.elim hH0
  have hc16 := Spec.compactType_lt hct
  have hn : sz.toNat < 15 := by have := toNat_of_toInt h0; omega
  unfold wcbN
  intro p' t' tmp' fs' et' sz' c' he hp htr hte hct'
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at he
  obtain ⟨h1, h2, h3⟩ := he
  subst p' et' sz'
  obtain ⟨h4, h5⟩ := cpAt_fields hC0 hp htr hte
  subst t' tmp'
  rw [hct] at hct'
  simp only [Option.some.injEq] at hct'
  subst hct'
  refine ⟨rfl, ?_, hr1, CPAtH.elim hH1, hn1, hi1, hst1, hh1⟩
  rw [hs1, Spec.listHeader_short hn hc16, wcb_byte_short hn hc16]

/-- The long form (`size > 14`): the byte `0xF0 | c`, then `writeVarint32(size)`. -/
theorem wcb_post_long {P : Program} {R : TRep} {σ0 σ1 σ2 : State} {p t tmp : Addr} {et sz : I32}
    {c : Nat}
    (hH0 : CPAtH P R σ0 p t tmp)
    (hct : Spec.compactType et.toNat = some c) (hcond : 14 < sz.toInt)
    (hs1 : R.sink σ1 t = R.sink σ0 t ++
      [UInt8.ofNat (JInt.toByte (240#32 ||| JInt.toShort (BitVec.ofNat 32 c))).toNat])
    (hr1 : R.src σ1 t = R.src σ0 t) (hom : OwnsMono R σ0 σ1 t)
    (hn1 : σ0.next ≤ σ1.next) (hi1 : σ1.inits = σ0.inits) (hst1 : σ1.statics = σ0.statics)
    (hh1 : ∀ a, a < σ0.next → ¬a = t → ¬a = tmp → ¬R.owns σ0 t a → σ1.heap a = σ0.heap a)
    (hH2 : CPAtH P R σ2 p t tmp)
    (hs2 : R.sink σ2 t = R.sink σ1 t ++ Spec.varint sz.toNat) (hr2 : R.src σ2 t = R.src σ1 t)
    (hn2 : σ1.next ≤ σ2.next) (hi2 : σ2.inits = σ1.inits) (hst2 : σ2.statics = σ1.statics)
    (hh2 : ∀ a, a < σ1.next → a ≠ t → a ≠ tmp → ¬R.owns σ1 t a → σ2.heap a = σ1.heap a) :
    wcbN P R [.ref p, .int et, .int sz] σ0 none σ2 := by
  have hC0 := CPAtH.elim hH0
  have hc16 := Spec.compactType_lt hct
  have hn : 15 ≤ sz.toNat := by have := toNat_of_toInt (show 0 ≤ sz.toInt by omega); omega
  unfold wcbN
  intro p' t' tmp' fs' et' sz' c' he hp htr hte hct'
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at he
  obtain ⟨h1, h2, h3⟩ := he
  subst p' et' sz'
  obtain ⟨h4, h5⟩ := cpAt_fields hC0 hp htr hte
  subst t' tmp'
  rw [hct] at hct'
  simp only [Option.some.injEq] at hct'
  subst hct'
  refine ⟨rfl, ?_, by rw [hr2, hr1], CPAtH.elim hH2, Nat.le_trans hn1 hn2, hi2.trans hi1,
    hst2.trans hst1, ?_⟩
  · rw [hs2, hs1, Spec.listHeader_long hn hc16, byte_long_tab c hc16, List.append_assoc]
    rfl
  · intro a ha hat hatm hao
    rw [hh2 a (Nat.lt_of_lt_of_le ha hn1) hat hatm (hom a ha hao), hh1 a ha hat hatm hao]

/-- `ttypeToCompactType` holds `compactType e` at `e`. -/
theorem ctTable_get : ∀ e c, Spec.compactType e = some c →
    ctTable[e]? = some (.int (BitVec.ofNat 32 c)) := by
  intro e c h
  unfold Spec.compactType at h
  split at h <;> first | (cases h; rfl) | cases h

theorem ctTable_length : ctTable.length = 18 := rfl

theorem compactType_le : ∀ e c, Spec.compactType e = some c → e ≤ 16 := by
  intro e c h
  unfold Spec.compactType at h
  split at h <;> first | (cases h; decide) | cases h

end EquivLean.Demo.Thrift.Java
