/-!
# Apache Thrift wire encodings: the specification of T4

The encodings of PREREG_T_v1 §T4, against which Thrift's C++ (`TCompactProtocolT`, `TBinaryProtocolT`),
Java (`TCompactProtocol`, `TBinaryProtocol`) and Rust (`protocol/compact.rs`, `protocol/binary.rs`)
functions are proved (Thrift f0eb8b84e).  Core Lean only.

* Encoders: `varint`, `zigzag`, `fieldHeader` (and `fieldStop`), `listHeader`, `lenPrefix` (compact
  protocol); `beI16`, `beI32`, `beI64`, `binLenPrefix` (binary protocol).
* Decoders, `none` = malformed: `readVarint32`, `readVarint64`, `unzigzag`, `readFieldHeader`,
  `readListHeader`, `readLenPrefix`, `readI16`, `readI32`, `readI64`, `readBinLenPrefix`, with the
  round trips `read (enc x ++ rest) = some (x, rest)` (`readVarint32_varint`, ...).
* Malformed input (M): `VarintOverlong`, `VarintTruncated`, `VarintExceeds`, `StopNibble`,
  `IdOutOfRange`, `DeltaIdOverflow`, `NegSize`, `Truncated`.  The decoders test them by name, and each
  decoder's `_eq_none_iff` says which of them make it fail.  `readVarint k` reads at most `k` bytes
  and does not bound the value, so that a language's theorem can say what it does instead (C++ reads a
  varint32 with its 10-byte varint64 reader and truncates; Java and Rust truncate a 5-byte value).
* Transports: a sink is the bytes written so far (`Sink.write` appends); a source is the bytes not read
  yet (`Source.read` returns the next bytes, or `none` = end of input).  `WriteAppends` and `ReadNext`
  are the contracts in this vocabulary.
* Named inputs, so that the languages are compared on the same bytes: for the field-header writer,
  `exDelta15` (delta 15) and `exI16Overflow` (a delta past `i16`), with their specified bytes; and six
  malformed inputs (`exVarint32Exceeds`, `exVarint64Exceeds`, `exVarint32Overlong`, `exStopNibble`,
  `exIdOutOfRange`, `exNegSize`), with the specification's verdict on each.

Values are mathematical: unsigned values are `Nat`, signed ones `Int` with `InI16`, `InI32`, `InI64`;
`toU w` and `toS w` convert two's complement patterns.  Type nibbles are returned as read;
`compactType` and `ttypeOfCompact` map TType codes to nibbles and back.  Size and message limits
(`string_limit_`, `container_limit_`, `max_message_size`, ...) are configuration, not wire format.
A section near the end gives the shift/mask forms the three libraries compute.
-/

namespace EquivLean.Demo.Thrift.Spec

/-- Bytes on the wire. -/
abbrev Bytes := List UInt8

/-! ## Integer widths -/

/-- `v` is an `i16`. -/
def InI16 (v : Int) : Prop := -32768 ≤ v ∧ v < 32768
/-- `v` is an `i32`. -/
def InI32 (v : Int) : Prop := -2147483648 ≤ v ∧ v < 2147483648
/-- `v` is an `i64`. -/
def InI64 (v : Int) : Prop := -9223372036854775808 ≤ v ∧ v < 9223372036854775808

instance (v : Int) : Decidable (InI16 v) := inferInstanceAs (Decidable (-32768 ≤ v ∧ v < 32768))
instance (v : Int) : Decidable (InI32 v) :=
  inferInstanceAs (Decidable (-2147483648 ≤ v ∧ v < 2147483648))
instance (v : Int) : Decidable (InI64 v) :=
  inferInstanceAs (Decidable (-9223372036854775808 ≤ v ∧ v < 9223372036854775808))

/-- The `w`-bit two's complement pattern of `n`, as an unsigned value (`n mod 2^w`). -/
def toU (w : Nat) (n : Int) : Nat := (n % (2 ^ w : Nat)).toNat

/-- The signed `w`-bit value of the pattern `v mod 2^w` (balanced: in `[-2^(w-1), 2^(w-1))`). -/
def toS (w : Nat) (v : Int) : Int := Int.bmod v (2 ^ w)

theorem toU_lt (w : Nat) (n : Int) : toU w n < 2 ^ w := by
  have h : (0 : Int) < (2 ^ w : Nat) := by exact_mod_cast Nat.two_pow_pos w
  have h1 := Int.emod_nonneg n (Int.ne_of_gt h)
  have h2 := Int.emod_lt_of_pos n h
  unfold toU
  omega

theorem toU_toS (w : Nat) (v : Int) : toU w (toS w v) = toU w v := by
  unfold toU toS
  rw [Int.bmod_emod]

theorem toU_of_nonneg {w : Nat} {n : Int} (h0 : 0 ≤ n) (h : n < (2 ^ w : Nat)) :
    (toU w n : Int) = n := by
  unfold toU
  rw [Int.emod_eq_of_lt h0 h, Int.toNat_of_nonneg h0]

theorem toU_of_neg {w : Nat} {n : Int} (h0 : n < 0) (h : -((2 ^ w : Nat) : Int) ≤ n) :
    (toU w n : Int) = n + (2 ^ w : Nat) := by
  unfold toU
  have e : n % ((2 ^ w : Nat) : Int) = n + (2 ^ w : Nat) := by
    rw [← Int.add_emod_right]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [e, Int.toNat_of_nonneg (by omega)]

theorem toS_toU16 {n : Int} (h : InI16 n) : toS 16 (toU 16 n) = n := by
  unfold InI16 at h
  unfold toS toU
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)), Int.emod_bmod]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem toS_toU32 {n : Int} (h : InI32 n) : toS 32 (toU 32 n) = n := by
  unfold InI32 at h
  unfold toS toU
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)), Int.emod_bmod]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem toS_toU64 {n : Int} (h : InI64 n) : toS 64 (toU 64 n) = n := by
  unfold InI64 at h
  unfold toS toU
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)), Int.emod_bmod]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-! ## Transports

A sink is the list of bytes written so far: a write appends.  A source is the list of bytes not read
yet: a read of `n` bytes returns the next `n` bytes and what is left, or end of input.  Each language
states its transport (C++ and Java `TTransport` with their buffer fast paths, Rust `TReadTransport` /
`TWriteTransport` or `io::Read` / `io::Write`) once, in its own error monad, against these;
`WriteAppends` and `ReadNext` are the shapes of those contracts. -/

/-- A sink: the bytes written so far. -/
abbrev Sink := Bytes

/-- Writing `bs` appends it. -/
def Sink.write (s : Sink) (bs : Bytes) : Sink := s ++ bs

/-- A source: the bytes not read yet. -/
abbrev Source := Bytes

/-- Reading `n` bytes: the next `n` bytes and what is left, or `none` (end of input) when fewer than
`n` are left. -/
def Source.read (src : Source) (n : Nat) : Option (Bytes × Source) :=
  if src.length < n then none else some (src.take n, src.drop n)

/-- Reading one byte. -/
def Source.readByte : Source → Option (UInt8 × Source)
  | [] => none
  | b :: r => some (b, r)

/-- A partial read of at most `n` bytes (`TTransport::read`, `io::Read::read`): `got` is a prefix of
the source, at most `n` bytes long, and empty only at end of input or when `n = 0`. -/
def Source.ReadSome (src : Source) (n : Nat) (got : Bytes) (src' : Source) : Prop :=
  src = got ++ src' ∧ got.length ≤ n ∧ (got = [] → src = [] ∨ n = 0)

/-- The write contract of a transport with state `σ`: `write` appends exactly its bytes to the sink. -/
def WriteAppends {σ : Type} (contents : σ → Sink) (write : σ → Bytes → σ) : Prop :=
  ∀ s bs, contents (write s bs) = Sink.write (contents s) bs

/-- The read contract of a transport with state `σ`: reading `n` bytes returns the next `n` bytes of
the source and leaves the rest, and reports end of input exactly when fewer than `n` are left. -/
def ReadNext {σ : Type} (remaining : σ → Source) (read : σ → Nat → Option (Bytes × σ)) : Prop :=
  ∀ s n, (read s n).map (fun p => (p.1, remaining p.2)) = Source.read (remaining s) n

/-! ## Compact protocol: zigzag and varints -/

/-- Zigzag: `0, -1, 1, -2, 2, …` ↦ `0, 1, 2, 3, 4, …` (`2n` for `n ≥ 0`, `-2n - 1` below). -/
def zigzag (n : Int) : Nat := if 0 ≤ n then (2 * n).toNat else (-2 * n - 1).toNat

/-- The inverse of `zigzag`. -/
def unzigzag (v : Nat) : Int := if v % 2 = 0 then ((v / 2 : Nat) : Int) else -((v / 2 : Nat) : Int) - 1

theorem unzigzag_zigzag (n : Int) : unzigzag (zigzag n) = n := by
  unfold zigzag unzigzag
  split <;> split <;> omega

theorem zigzag_unzigzag (v : Nat) : zigzag (unzigzag v) = v := by
  unfold zigzag unzigzag
  split <;> split <;> omega

theorem zigzag_lt16 {n : Int} (h : InI16 n) : zigzag n < 2 ^ 16 := by
  unfold InI16 at h; unfold zigzag; split <;> omega
theorem zigzag_lt32 {n : Int} (h : InI32 n) : zigzag n < 2 ^ 32 := by
  unfold InI32 at h; unfold zigzag; split <;> omega
theorem zigzag_lt64 {n : Int} (h : InI64 n) : zigzag n < 2 ^ 64 := by
  unfold InI64 at h; unfold zigzag; split <;> omega

theorem unzigzag_range16 {v : Nat} (h : v < 2 ^ 16) : InI16 (unzigzag v) := by
  unfold InI16 unzigzag; split <;> omega
theorem unzigzag_range32 {v : Nat} (h : v < 2 ^ 32) : InI32 (unzigzag v) := by
  unfold InI32 unzigzag; split <;> omega
theorem unzigzag_range64 {v : Nat} (h : v < 2 ^ 64) : InI64 (unzigzag v) := by
  unfold InI64 unzigzag; split <;> omega

/-- `varint` with fuel; `varint n` runs it with fuel `n`, which is enough (`varintF_fuel`). -/
def varintF : Nat → Nat → Bytes
  | 0, n => [UInt8.ofNat n]
  | f + 1, n => if n < 128 then [UInt8.ofNat n] else UInt8.ofNat (n % 128 + 128) :: varintF f (n / 128)

/-- The unsigned varint of `n`: 7-bit groups, least significant first, the high bit set on every byte
but the last. -/
def varint (n : Nat) : Bytes := varintF n n

theorem varintF_fuel : ∀ (f g n : Nat), n ≤ f → n ≤ g → varintF f n = varintF g n
  | 0, 0, _, _, _ => rfl
  | 0, g + 1, n, h, _ => by
    have : n = 0 := by omega
    subst this; simp [varintF]
  | f + 1, 0, n, _, h => by
    have : n = 0 := by omega
    subst this; simp [varintF]
  | f + 1, g + 1, n, hf, hg => by
    simp only [varintF]
    by_cases h : n < 128
    · simp only [ite_eq_left h]
    · simp only [ite_eq_right h]
      rw [varintF_fuel f g (n / 128) (by omega) (by omega)]

theorem varint_eq (n : Nat) : varint n =
    if n < 128 then [UInt8.ofNat n] else UInt8.ofNat (n % 128 + 128) :: varint (n / 128) := by
  unfold varint
  cases n with
  | zero => simp [varintF]
  | succ m =>
    simp only [varintF]
    by_cases h : m + 1 < 128
    · simp only [ite_eq_left h]
    · simp only [ite_eq_right h]
      rw [varintF_fuel m ((m + 1) / 128) ((m + 1) / 128) (by omega) (Nat.le_refl _)]

theorem varint_of_lt {n : Nat} (h : n < 128) : varint n = [UInt8.ofNat n] := by
  rw [varint_eq, ite_eq_left h]

theorem varint_of_ge {n : Nat} (h : 128 ≤ n) :
    varint n = UInt8.ofNat (n % 128 + 128) :: varint (n / 128) := by
  rw [varint_eq, ite_eq_right (by omega)]

/-- The byte values of `varint n` (for semantics whose bytes are numbers). -/
theorem varint_map_toNat (n : Nat) : (varint n).map UInt8.toNat =
    if n < 128 then [n] else (n % 128 + 128) :: (varint (n / 128)).map UInt8.toNat := by
  rw [varint_eq]
  split <;> simp <;> omega

theorem varint_length_pos (n : Nat) : 0 < (varint n).length := by
  rw [varint_eq]; split <;> simp

theorem varint_length_le : ∀ (k : Nat) {n : Nat}, n < 128 ^ (k + 1) → (varint n).length ≤ k + 1
  | 0, n, h => by
    rw [varint_of_lt (by simpa using h)]; simp
  | k + 1, n, h => by
    by_cases hn : n < 128
    · rw [varint_of_lt hn]; simp
    · rw [varint_of_ge (by omega)]
      have h' : n / 128 < 128 ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        rw [Nat.pow_succ] at h
        exact h
      have := varint_length_le k h'
      simp only [List.length_cons]
      omega

theorem varint_length_le5 {n : Nat} (h : n < 2 ^ 32) : (varint n).length ≤ 5 :=
  varint_length_le 4 (Nat.lt_of_lt_of_le h (by decide))

theorem varint_length_le10 {n : Nat} (h : n < 2 ^ 64) : (varint n).length ≤ 10 :=
  varint_length_le 9 (Nat.lt_of_lt_of_le h (by decide))

/-- The first `k` bytes are present and all have the high bit set: a varint longer than `k` bytes. -/
def VarintOverlong (k : Nat) (bs : Bytes) : Prop := k ≤ bs.length ∧ ∀ b ∈ bs.take k, 128 ≤ b.toNat

/-- The input ends inside a varint of at most `k` bytes: fewer than `k` bytes, all with the high bit
set. -/
def VarintTruncated (k : Nat) (bs : Bytes) : Prop := bs.length < k ∧ ∀ b ∈ bs, 128 ≤ b.toNat

/-- Reads an unsigned varint of at most `k` bytes: its value (not bounded) and the bytes after it;
`none` when the first `k` bytes all have the high bit set (`VarintOverlong k`) or the input ends inside
the varint (`VarintTruncated k`). -/
def readVarint : Nat → Bytes → Option (Nat × Bytes)
  | 0, _ => none
  | _ + 1, [] => none
  | k + 1, b :: bs =>
    if b.toNat < 128 then some (b.toNat, bs)
    else (readVarint k bs).map fun p => (b.toNat % 128 + 128 * p.1, p.2)

/-- A varint of at most `k` bytes whose value is `bound` or more (`2^32` for a varint32, `2^64` for a
varint64). -/
def VarintExceeds (k bound : Nat) (bs : Bytes) : Prop :=
  ∃ v r, readVarint k bs = some (v, r) ∧ bound ≤ v

/-- A compact varint32 (`readVarint32`): at most 5 bytes, value below `2^32`. -/
def readVarint32 (bs : Bytes) : Option (Nat × Bytes) :=
  (readVarint 5 bs).bind fun p => if 2 ^ 32 ≤ p.1 then none else some p

/-- A compact varint64 (`readVarint64`): at most 10 bytes, value below `2^64`. -/
def readVarint64 (bs : Bytes) : Option (Nat × Bytes) :=
  (readVarint 10 bs).bind fun p => if 2 ^ 64 ≤ p.1 then none else some p

theorem readVarint_varint : ∀ (k n : Nat) (rest : Bytes), (varint n).length ≤ k →
    readVarint k (varint n ++ rest) = some (n, rest)
  | 0, n, _, h => absurd h (Nat.not_le.mpr (varint_length_pos n))
  | k + 1, n, rest, h => by
    by_cases hn : n < 128
    · rw [varint_of_lt hn]
      have hb : (UInt8.ofNat n).toNat = n := by rw [UInt8.toNat_ofNat']; omega
      simp only [List.cons_append, List.nil_append, readVarint]
      rw [hb, ite_eq_left hn]
    · rw [varint_of_ge (by omega)] at h ⊢
      have hb : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 := by
        rw [UInt8.toNat_ofNat']; omega
      simp only [List.cons_append, readVarint]
      rw [hb, ite_eq_right (by omega), readVarint_varint k (n / 128) rest (by simp at h; omega),
        Option.map_some]
      congr 2
      omega

theorem readVarint32_varint {n : Nat} (h : n < 2 ^ 32) (rest : Bytes) :
    readVarint32 (varint n ++ rest) = some (n, rest) := by
  unfold readVarint32
  rw [readVarint_varint 5 n rest (varint_length_le5 h), Option.bind_some]
  dsimp only
  rw [ite_eq_right (by omega)]

theorem readVarint64_varint {n : Nat} (h : n < 2 ^ 64) (rest : Bytes) :
    readVarint64 (varint n ++ rest) = some (n, rest) := by
  unfold readVarint64
  rw [readVarint_varint 10 n rest (varint_length_le10 h), Option.bind_some]
  dsimp only
  rw [ite_eq_right (by omega)]

theorem readVarint32_eq_some_iff {bs : Bytes} {v : Nat} {r : Bytes} :
    readVarint32 bs = some (v, r) ↔ readVarint 5 bs = some (v, r) ∧ v < 2 ^ 32 := by
  unfold readVarint32
  rcases h : readVarint 5 bs with _ | ⟨v', r'⟩
  · simp
  · by_cases hv : 2 ^ 32 ≤ v'
    · simp only [Option.bind_some, ite_eq_left hv, reduceCtorEq, false_iff, not_and, Option.some.injEq,
        Prod.mk.injEq]
      rintro ⟨rfl, rfl⟩; omega
    · simp only [Option.bind_some, ite_eq_right hv, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, by omega⟩
      · rintro ⟨⟨rfl, rfl⟩, -⟩; exact ⟨rfl, rfl⟩

theorem readVarint64_eq_some_iff {bs : Bytes} {v : Nat} {r : Bytes} :
    readVarint64 bs = some (v, r) ↔ readVarint 10 bs = some (v, r) ∧ v < 2 ^ 64 := by
  unfold readVarint64
  rcases h : readVarint 10 bs with _ | ⟨v', r'⟩
  · simp
  · by_cases hv : 2 ^ 64 ≤ v'
    · simp only [Option.bind_some, ite_eq_left hv, reduceCtorEq, false_iff, not_and, Option.some.injEq,
        Prod.mk.injEq]
      rintro ⟨rfl, rfl⟩; omega
    · simp only [Option.bind_some, ite_eq_right hv, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, by omega⟩
      · rintro ⟨⟨rfl, rfl⟩, -⟩; exact ⟨rfl, rfl⟩

/-- (M) A varint of at most `k` bytes fails to read exactly when it is overlong or truncated. -/
theorem readVarint_eq_none_iff : ∀ (k : Nat) (bs : Bytes),
    readVarint k bs = none ↔ VarintOverlong k bs ∨ VarintTruncated k bs
  | 0, bs => by simp [readVarint, VarintOverlong]
  | k + 1, [] => by simp [readVarint, VarintOverlong, VarintTruncated]
  | k + 1, b :: bs => by
    by_cases hb : b.toNat < 128
    · have e : readVarint (k + 1) (b :: bs) = some (b.toNat, bs) := by
        simp only [readVarint, ite_eq_left hb]
      rw [e]
      constructor
      · intro h; cases h
      · rintro (⟨_, h⟩ | ⟨_, h⟩)
        · have := h b (by simp); omega
        · have := h b (by simp); omega
    · have e : readVarint (k + 1) (b :: bs) =
          (readVarint k bs).map fun p => (b.toNat % 128 + 128 * p.1, p.2) := by
        simp only [readVarint, ite_eq_right hb]
      rw [e, Option.map_eq_none_iff, readVarint_eq_none_iff k bs]
      have hb' : 128 ≤ b.toNat := by omega
      simp only [VarintOverlong, VarintTruncated, List.take_succ_cons, List.length_cons,
        List.mem_cons, forall_eq_or_imp, hb', true_and, Nat.add_le_add_iff_right,
        Nat.add_lt_add_iff_right]

/-- (M) The varint32 cases: overlong (more than 5 bytes), truncated, or a value of `2^32` or more. -/
theorem readVarint32_eq_none_iff (bs : Bytes) :
    readVarint32 bs = none ↔
      VarintOverlong 5 bs ∨ VarintTruncated 5 bs ∨ VarintExceeds 5 (2 ^ 32) bs := by
  rw [← or_assoc, ← readVarint_eq_none_iff]
  unfold readVarint32 VarintExceeds
  rcases h : readVarint 5 bs with _ | ⟨v, r⟩
  · simp
  · by_cases hv : 2 ^ 32 ≤ v <;> simp [hv]

/-- (M) The varint64 cases: overlong (more than 10 bytes), truncated, or a value of `2^64` or more. -/
theorem readVarint64_eq_none_iff (bs : Bytes) :
    readVarint64 bs = none ↔
      VarintOverlong 10 bs ∨ VarintTruncated 10 bs ∨ VarintExceeds 10 (2 ^ 64) bs := by
  rw [← or_assoc, ← readVarint_eq_none_iff]
  unfold readVarint64 VarintExceeds
  rcases h : readVarint 10 bs with _ | ⟨v, r⟩
  · simp
  · by_cases hv : 2 ^ 64 ≤ v <;> simp [hv]

/-! ## Compact protocol: field header -/

/-- `d << 4 | t = 16 d + t` for a nibble `t`. -/
theorem shl4_or (d : Nat) {t : Nat} (ht : t < 16) : d <<< 4 ||| t = 16 * d + t := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 4) (by omega) d, Nat.shiftLeft_eq]
  omega

/-- The compact field header of a field with compact type nibble `ty` and id `id`, after a field with
id `last`: the byte `delta << 4 | ty` when `1 ≤ delta = id - last ≤ 15`, else the byte `ty` followed by
the zigzag varint of the `i16` id. -/
def fieldHeader (last id : Int) (ty : Nat) : Bytes :=
  if 1 ≤ id - last ∧ id - last ≤ 15 then [UInt8.ofNat ((id - last).toNat <<< 4 ||| ty)]
  else UInt8.ofNat ty :: varint (zigzag id)

theorem fieldHeader_short {last id : Int} {ty : Nat} (hd : 1 ≤ id - last ∧ id - last ≤ 15)
    (ht : ty < 16) : fieldHeader last id ty = [UInt8.ofNat (16 * (id - last).toNat + ty)] := by
  unfold fieldHeader
  rw [ite_eq_left hd, shl4_or _ ht]

theorem fieldHeader_long {last id : Int} {ty : Nat} (hd : ¬ (1 ≤ id - last ∧ id - last ≤ 15)) :
    fieldHeader last id ty = UInt8.ofNat ty :: varint (zigzag id) := by
  unfold fieldHeader
  rw [ite_eq_right hd]

/-- The end of a struct's fields: the byte 0 (STOP). -/
def fieldStop : Bytes := [0]

/-- What a field header says: the end of the struct, or a field with its compact type nibble and id. -/
inductive FieldHead where
  | stop
  | field (ty : Nat) (id : Int)
  deriving DecidableEq, Repr

/-- A header byte with type nibble 0 (STOP) but a nonzero delta nibble; STOP is the byte 0. -/
def StopNibble (b : UInt8) : Prop := b.toNat % 16 = 0 ∧ b.toNat / 16 ≠ 0

/-- A long-form field id (zigzag varint value `z`) outside `i16`. -/
def IdOutOfRange (z : Nat) : Prop := ¬ InI16 (unzigzag z)

/-- A delta that takes the field id past `i16`. -/
def DeltaIdOverflow (last : Int) (delta : Nat) : Prop := ¬ InI16 (last + delta)

instance (b : UInt8) : Decidable (StopNibble b) :=
  inferInstanceAs (Decidable (b.toNat % 16 = 0 ∧ b.toNat / 16 ≠ 0))
instance (z : Nat) : Decidable (IdOutOfRange z) := inferInstanceAs (Decidable (¬ InI16 (unzigzag z)))
instance (last : Int) (d : Nat) : Decidable (DeltaIdOverflow last d) :=
  inferInstanceAs (Decidable (¬ InI16 (last + d)))

/-- Reads a compact field header after a field with id `last`.  `none`: no byte (`Truncated 1`),
`StopNibble`, a long-form id that is not a varint32 (`readVarint32_eq_none_iff`) or `IdOutOfRange`,
or `DeltaIdOverflow`. -/
def readFieldHeader (last : Int) : Bytes → Option (FieldHead × Bytes)
  | [] => none
  | b :: bs =>
    if b.toNat = 0 then some (.stop, bs)
    else if StopNibble b then none
    else if b.toNat / 16 = 0 then
      (readVarint32 bs).bind fun p =>
        if IdOutOfRange p.1 then none else some (.field (b.toNat % 16) (unzigzag p.1), p.2)
    else if DeltaIdOverflow last (b.toNat / 16) then none
    else some (.field (b.toNat % 16) (last + (b.toNat / 16 : Nat)), bs)

theorem readFieldHeader_fieldStop (last : Int) (rest : Bytes) :
    readFieldHeader last (fieldStop ++ rest) = some (.stop, rest) := by
  simp [fieldStop, readFieldHeader]

theorem readFieldHeader_fieldHeader {last id : Int} {ty : Nat} (hty : 1 ≤ ty ∧ ty < 16)
    (hid : InI16 id) (rest : Bytes) :
    readFieldHeader last (fieldHeader last id ty ++ rest) = some (.field ty id, rest) := by
  unfold fieldHeader
  by_cases hd : 1 ≤ id - last ∧ id - last ≤ 15
  · rw [ite_eq_left hd, shl4_or _ hty.2, List.cons_append, List.nil_append]
    have hb : (UInt8.ofNat (16 * (id - last).toNat + ty)).toNat = 16 * (id - last).toNat + ty := by
      rw [UInt8.toNat_ofNat']; omega
    have h0 : ¬ (UInt8.ofNat (16 * (id - last).toNat + ty)).toNat = 0 := by rw [hb]; omega
    have hs : ¬ StopNibble (UInt8.ofNat (16 * (id - last).toNat + ty)) := by
      unfold StopNibble; rw [hb]; omega
    have h16 : ¬ (UInt8.ofNat (16 * (id - last).toNat + ty)).toNat / 16 = 0 := by rw [hb]; omega
    have hq : (UInt8.ofNat (16 * (id - last).toNat + ty)).toNat / 16 = (id - last).toNat := by
      rw [hb]; omega
    have hr : (UInt8.ofNat (16 * (id - last).toNat + ty)).toNat % 16 = ty := by rw [hb]; omega
    have he : last + (((id - last).toNat : Nat) : Int) = id := by omega
    have hov : ¬ DeltaIdOverflow last (id - last).toNat := by
      unfold DeltaIdOverflow; rw [he]; exact fun h => h hid
    simp only [readFieldHeader]
    rw [ite_eq_right h0, ite_eq_right hs, ite_eq_right h16, hq, ite_eq_right hov, hr, he]
  · rw [ite_eq_right hd, List.cons_append]
    have hb : (UInt8.ofNat ty).toNat = ty := by rw [UInt8.toNat_ofNat']; omega
    have h0 : ¬ (UInt8.ofNat ty).toNat = 0 := by rw [hb]; omega
    have hs : ¬ StopNibble (UInt8.ofNat ty) := by unfold StopNibble; rw [hb]; omega
    have h16 : (UInt8.ofNat ty).toNat / 16 = 0 := by rw [hb]; omega
    have hz : zigzag id < 2 ^ 32 := Nat.lt_trans (zigzag_lt16 hid) (by decide)
    have hio : ¬ IdOutOfRange (zigzag id) := by
      unfold IdOutOfRange; rw [unzigzag_zigzag]; exact fun h => h hid
    simp only [readFieldHeader]
    rw [ite_eq_right h0, ite_eq_right hs, ite_eq_left h16, readVarint32_varint hz, Option.bind_some]
    dsimp only
    rw [ite_eq_right hio, unzigzag_zigzag, hb, Nat.mod_eq_of_lt hty.2]

theorem readFieldHeader_nil (last : Int) : readFieldHeader last [] = none := rfl

/-- (M) The field header cases (`readFieldHeader_nil`: no byte at all). -/
theorem readFieldHeader_eq_none_iff (last : Int) (b : UInt8) (bs : Bytes) :
    readFieldHeader last (b :: bs) = none ↔
      StopNibble b ∨
      (b.toNat % 16 ≠ 0 ∧ b.toNat / 16 = 0 ∧
        (readVarint32 bs = none ∨ ∃ z r, readVarint32 bs = some (z, r) ∧ IdOutOfRange z)) ∨
      (b.toNat % 16 ≠ 0 ∧ b.toNat / 16 ≠ 0 ∧ DeltaIdOverflow last (b.toNat / 16)) := by
  simp only [readFieldHeader]
  by_cases h0 : b.toNat = 0
  · have hs : ¬ StopNibble b := by unfold StopNibble; omega
    rw [ite_eq_left h0]
    simp only [reduceCtorEq, false_iff]
    rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
    · exact hs h
    · omega
    · omega
  · rw [ite_eq_right h0]
    by_cases hs : StopNibble b
    · rw [ite_eq_left hs]; simp [hs]
    · rw [ite_eq_right hs]
      have h16 : b.toNat % 16 ≠ 0 := by unfold StopNibble at hs; omega
      by_cases hq : b.toNat / 16 = 0
      · rw [ite_eq_left hq]
        rcases h : readVarint32 bs with _ | ⟨z, r⟩
        · simp [h16, hq]
        · by_cases hz : IdOutOfRange z <;> simp [hz, hs, h16, hq]
      · rw [ite_eq_right hq]
        by_cases hd : DeltaIdOverflow last (b.toNat / 16) <;> simp [hd, hs, h16, hq]

/-! ## Compact protocol: list/set header and length prefix -/

/-- The compact list/set header of `size` elements of compact type nibble `ety`: the byte
`size << 4 | ety` when `size < 15`, else the byte `0xF0 | ety` followed by the varint of `size`. -/
def listHeader (size ety : Nat) : Bytes :=
  if size < 15 then [UInt8.ofNat (size <<< 4 ||| ety)] else UInt8.ofNat (0xF0 ||| ety) :: varint size

theorem listHeader_short {size ety : Nat} (hs : size < 15) (he : ety < 16) :
    listHeader size ety = [UInt8.ofNat (16 * size + ety)] := by
  unfold listHeader
  rw [ite_eq_left hs, shl4_or _ he]

theorem listHeader_long {size ety : Nat} (hs : 15 ≤ size) (he : ety < 16) :
    listHeader size ety = UInt8.ofNat (0xF0 + ety) :: varint size := by
  have h : (0xF0 : Nat) ||| ety = 0xF0 + ety := shl4_or 15 he
  unfold listHeader
  rw [ite_eq_right (by omega), h]

/-- A size whose low 32 bits are a negative `i32`. -/
def NegSize (v : Nat) : Prop := 2 ^ 31 ≤ v % 2 ^ 32

instance (v : Nat) : Decidable (NegSize v) := inferInstanceAs (Decidable (2 ^ 31 ≤ v % 2 ^ 32))

/-- Fewer than `w` bytes left. -/
def Truncated (w : Nat) (bs : Bytes) : Prop := bs.length < w

instance (w : Nat) (bs : Bytes) : Decidable (Truncated w bs) := inferInstanceAs (Decidable (bs.length < w))

/-- Reads a compact list/set header: (size, element type nibble).  `none`: no byte (`Truncated 1`), or
a long-form size that is not a varint32 or is `NegSize`. -/
def readListHeader : Bytes → Option ((Nat × Nat) × Bytes)
  | [] => none
  | b :: bs =>
    if b.toNat / 16 < 15 then some ((b.toNat / 16, b.toNat % 16), bs)
    else (readVarint32 bs).bind fun p =>
      if NegSize p.1 then none else some ((p.1, b.toNat % 16), p.2)

theorem readListHeader_listHeader {size ety : Nat} (hs : size < 2 ^ 31) (he : ety < 16)
    (rest : Bytes) : readListHeader (listHeader size ety ++ rest) = some ((size, ety), rest) := by
  unfold listHeader
  by_cases h15 : size < 15
  · rw [ite_eq_left h15, shl4_or _ he, List.cons_append, List.nil_append]
    have hb : (UInt8.ofNat (16 * size + ety)).toNat = 16 * size + ety := by
      rw [UInt8.toNat_ofNat']; omega
    simp only [readListHeader]
    rw [hb, ite_eq_left (by omega), show (16 * size + ety) / 16 = size by omega,
      show (16 * size + ety) % 16 = ety by omega]
  · rw [ite_eq_right h15, show (0xF0 : Nat) = 15 <<< 4 by decide, shl4_or _ he, List.cons_append]
    have hb : (UInt8.ofNat (16 * 15 + ety)).toNat = 16 * 15 + ety := by
      rw [UInt8.toNat_ofNat']; omega
    have hn : ¬ NegSize size := by unfold NegSize; omega
    simp only [readListHeader]
    rw [hb, ite_eq_right (by omega), readVarint32_varint (by omega) rest, Option.bind_some]
    dsimp only
    rw [ite_eq_right hn, show (16 * 15 + ety) % 16 = ety by omega]

theorem readListHeader_nil : readListHeader [] = none := rfl

/-- (M) The list/set header cases (`readListHeader_nil`: no byte at all). -/
theorem readListHeader_eq_none_iff (b : UInt8) (bs : Bytes) :
    readListHeader (b :: bs) = none ↔
      b.toNat / 16 = 15 ∧
        (readVarint32 bs = none ∨ ∃ v r, readVarint32 bs = some (v, r) ∧ NegSize v) := by
  have hb := UInt8.toNat_lt b
  simp only [readListHeader]
  by_cases h15 : b.toNat / 16 < 15
  · rw [ite_eq_left h15]
    simp only [reduceCtorEq, false_iff, not_and]
    intro h; omega
  · rw [ite_eq_right h15]
    have e : b.toNat / 16 = 15 := by omega
    rcases h : readVarint32 bs with _ | ⟨v, r⟩
    · simp [e]
    · by_cases hv : NegSize v <;> simp [hv, e]

/-- The compact string/binary: the varint32 of the length, then the bytes. -/
def lenPrefix (bs : Bytes) : Bytes := varint bs.length ++ bs

/-- Reads a compact string/binary.  `none`: the length is not a varint32 or is `NegSize`, or fewer
bytes follow (`Truncated`). -/
def readLenPrefix (bs : Bytes) : Option (Bytes × Bytes) :=
  (readVarint32 bs).bind fun p =>
    if NegSize p.1 then none
    else if Truncated p.1 p.2 then none
    else some (p.2.take p.1, p.2.drop p.1)

theorem readLenPrefix_lenPrefix {bs : Bytes} (h : bs.length < 2 ^ 31) (rest : Bytes) :
    readLenPrefix (lenPrefix bs ++ rest) = some (bs, rest) := by
  unfold readLenPrefix lenPrefix
  have hn : ¬ NegSize bs.length := by unfold NegSize; omega
  have ht : ¬ Truncated bs.length (bs ++ rest) := by unfold Truncated; simp
  rw [List.append_assoc, readVarint32_varint (by omega) (bs ++ rest), Option.bind_some]
  dsimp only
  rw [ite_eq_right hn, ite_eq_right ht, List.take_left' rfl, List.drop_left' rfl]

/-- (M) The length prefix cases. -/
theorem readLenPrefix_eq_none_iff (bs : Bytes) :
    readLenPrefix bs = none ↔
      readVarint32 bs = none ∨ ∃ v r, readVarint32 bs = some (v, r) ∧ (NegSize v ∨ Truncated v r) := by
  unfold readLenPrefix
  rcases h : readVarint32 bs with _ | ⟨v, r⟩
  · simp
  · simp only [Option.bind_some, reduceCtorEq, false_or]
    constructor
    · intro hc
      refine ⟨v, r, rfl, ?_⟩
      by_cases hn : NegSize v
      · exact Or.inl hn
      · by_cases ht : Truncated v r
        · exact Or.inr ht
        · rw [ite_eq_right hn, ite_eq_right ht] at hc; cases hc
    · rintro ⟨v', r', he, hc⟩
      cases he
      rcases hc with hn | ht
      · rw [ite_eq_left hn]
      · by_cases hn : NegSize v
        · rw [ite_eq_left hn]
        · rw [ite_eq_right hn, ite_eq_left ht]

/-! ## Binary protocol -/

/-- The `w` low bytes of `n`, most significant first (big-endian `n mod 256^w`). -/
def be : Nat → Nat → Bytes
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n / 256 ^ w) :: be w n

/-- The big-endian value of bytes. -/
def beVal (bs : Bytes) : Nat := bs.foldl (fun acc b => 256 * acc + b.toNat) 0

/-- Binary `writeI16`: the two's complement pattern, big-endian. -/
def beI16 (n : Int) : Bytes := be 2 (toU 16 n)
/-- Binary `writeI32`. -/
def beI32 (n : Int) : Bytes := be 4 (toU 32 n)
/-- Binary `writeI64`. -/
def beI64 (n : Int) : Bytes := be 8 (toU 64 n)

/-- Binary string/binary: the length as a big-endian `i32`, then the bytes. -/
def binLenPrefix (bs : Bytes) : Bytes := beI32 bs.length ++ bs

/-- Reads `w` bytes as a big-endian unsigned value; `none` when fewer are left (`Truncated w`). -/
def readBE (w : Nat) (bs : Bytes) : Option (Nat × Bytes) :=
  if Truncated w bs then none else some (beVal (bs.take w), bs.drop w)

/-- Binary `readI16`. -/
def readI16 (bs : Bytes) : Option (Int × Bytes) := (readBE 2 bs).map fun p => (toS 16 p.1, p.2)
/-- Binary `readI32`. -/
def readI32 (bs : Bytes) : Option (Int × Bytes) := (readBE 4 bs).map fun p => (toS 32 p.1, p.2)
/-- Binary `readI64`. -/
def readI64 (bs : Bytes) : Option (Int × Bytes) := (readBE 8 bs).map fun p => (toS 64 p.1, p.2)

/-- Reads a binary string/binary.  `none`: fewer than 4 bytes (`Truncated 4`), a negative length, or
fewer bytes than the length (`Truncated`). -/
def readBinLenPrefix (bs : Bytes) : Option (Bytes × Bytes) :=
  (readI32 bs).bind fun p =>
    if p.1 < 0 then none
    else if Truncated p.1.toNat p.2 then none
    else some (p.2.take p.1.toNat, p.2.drop p.1.toNat)

theorem be_length : ∀ (w n : Nat), (be w n).length = w
  | 0, _ => rfl
  | w + 1, n => by simp [be, be_length w n]

theorem be_two (n : Nat) : be 2 n = [UInt8.ofNat (n / 2 ^ 8), UInt8.ofNat n] := by
  simp [be]

theorem be_four (n : Nat) : be 4 n =
    [UInt8.ofNat (n / 2 ^ 24), UInt8.ofNat (n / 2 ^ 16), UInt8.ofNat (n / 2 ^ 8), UInt8.ofNat n] := by
  simp [be]

theorem be_eight (n : Nat) : be 8 n =
    [UInt8.ofNat (n / 2 ^ 56), UInt8.ofNat (n / 2 ^ 48), UInt8.ofNat (n / 2 ^ 40),
      UInt8.ofNat (n / 2 ^ 32), UInt8.ofNat (n / 2 ^ 24), UInt8.ofNat (n / 2 ^ 16),
      UInt8.ofNat (n / 2 ^ 8), UInt8.ofNat n] := by
  simp [be]

theorem foldl_be : ∀ (w n acc : Nat),
    (be w n).foldl (fun acc b => 256 * acc + b.toNat) acc = acc * 256 ^ w + n % 256 ^ w
  | 0, n, acc => by simp [be, Nat.mod_one]
  | w + 1, n, acc => by
    simp only [be, List.foldl_cons]
    rw [foldl_be w n, UInt8.toNat_ofNat', show (2 : Nat) ^ 8 = 256 by decide,
      Nat.mod_pow_succ (b := 256) (k := w), show 256 ^ (w + 1) = 256 ^ w * 256 from Nat.pow_succ 256 w]
    generalize 256 ^ w = P
    generalize n / P % 256 = q
    generalize n % P = r
    have e1 : (256 * acc + q) * P = 256 * (acc * P) + q * P := by
      rw [Nat.add_mul, Nat.mul_assoc]
    have e2 : acc * (P * 256) = 256 * (acc * P) := by
      rw [Nat.mul_comm P 256, ← Nat.mul_assoc, Nat.mul_comm acc 256, Nat.mul_assoc]
    have e3 : P * q = q * P := Nat.mul_comm _ _
    omega

theorem readBE_be (w n : Nat) (rest : Bytes) :
    readBE w (be w n ++ rest) = some (n % 256 ^ w, rest) := by
  have ht : ¬ Truncated w (be w n ++ rest) := by unfold Truncated; simp [be_length]
  unfold readBE beVal
  rw [ite_eq_right ht, List.take_left' (be_length w n), List.drop_left' (be_length w n), foldl_be]
  simp

theorem readI16_beI16 {n : Int} (h : InI16 n) (rest : Bytes) :
    readI16 (beI16 n ++ rest) = some (n, rest) := by
  unfold readI16 beI16
  simp only [readBE_be, Option.map_some]
  rw [Nat.mod_eq_of_lt (by have := toU_lt 16 n; omega), toS_toU16 h]

theorem readI32_beI32 {n : Int} (h : InI32 n) (rest : Bytes) :
    readI32 (beI32 n ++ rest) = some (n, rest) := by
  unfold readI32 beI32
  simp only [readBE_be, Option.map_some]
  rw [Nat.mod_eq_of_lt (by have := toU_lt 32 n; omega), toS_toU32 h]

theorem readI64_beI64 {n : Int} (h : InI64 n) (rest : Bytes) :
    readI64 (beI64 n ++ rest) = some (n, rest) := by
  unfold readI64 beI64
  simp only [readBE_be, Option.map_some]
  rw [Nat.mod_eq_of_lt (by have := toU_lt 64 n; omega), toS_toU64 h]

theorem readBinLenPrefix_binLenPrefix {bs : Bytes} (h : bs.length < 2 ^ 31) (rest : Bytes) :
    readBinLenPrefix (binLenPrefix bs ++ rest) = some (bs, rest) := by
  unfold readBinLenPrefix binLenPrefix
  have hn : ¬ ((bs.length : Nat) : Int) < 0 := by omega
  have ht : ¬ Truncated ((bs.length : Nat) : Int).toNat (bs ++ rest) := by
    unfold Truncated; simp
  rw [List.append_assoc, readI32_beI32 (by unfold InI32; omega) (bs ++ rest), Option.bind_some]
  dsimp only
  rw [ite_eq_right hn, ite_eq_right ht, Int.toNat_natCast, List.take_left' rfl, List.drop_left' rfl]

/-- (M) Binary fixed-width reads fail exactly on truncated input. -/
theorem readBE_eq_none_iff (w : Nat) (bs : Bytes) : readBE w bs = none ↔ Truncated w bs := by
  unfold readBE
  by_cases h : Truncated w bs <;> simp [h]

theorem readI16_eq_none_iff (bs : Bytes) : readI16 bs = none ↔ Truncated 2 bs := by
  unfold readI16; rw [Option.map_eq_none_iff, readBE_eq_none_iff]
theorem readI32_eq_none_iff (bs : Bytes) : readI32 bs = none ↔ Truncated 4 bs := by
  unfold readI32; rw [Option.map_eq_none_iff, readBE_eq_none_iff]
theorem readI64_eq_none_iff (bs : Bytes) : readI64 bs = none ↔ Truncated 8 bs := by
  unfold readI64; rw [Option.map_eq_none_iff, readBE_eq_none_iff]

/-- (M) The binary length prefix cases. -/
theorem readBinLenPrefix_eq_none_iff (bs : Bytes) :
    readBinLenPrefix bs = none ↔
      Truncated 4 bs ∨ ∃ n r, readI32 bs = some (n, r) ∧ (n < 0 ∨ Truncated n.toNat r) := by
  rw [← readI32_eq_none_iff]
  unfold readBinLenPrefix
  rcases h : readI32 bs with _ | ⟨n, r⟩
  · simp
  · simp only [Option.bind_some, reduceCtorEq, false_or]
    constructor
    · intro hc
      refine ⟨n, r, rfl, ?_⟩
      by_cases hn : n < 0
      · exact Or.inl hn
      · by_cases ht : Truncated n.toNat r
        · exact Or.inr ht
        · rw [ite_eq_right hn, ite_eq_right ht] at hc; cases hc
    · rintro ⟨n', r', he, hc⟩
      cases he
      rcases hc with hn | ht
      · rw [ite_eq_left hn]
      · by_cases hn : n < 0
        · rw [ite_eq_left hn]
        · rw [ite_eq_right hn, ite_eq_left ht]

/-! ## Type codes

TType codes (C++ `TEnum.h`, Java `TType`, Rust `TType`): STOP 0, VOID 1, BOOL 2, BYTE 3, DOUBLE 4,
I16 6, I32 8, I64 10, STRING 11, STRUCT 12, MAP 13, SET 14, LIST 15, UUID 16. -/

/-- The compact type nibble of a TType (C++ `TTypeToCType`, Java `ttypeToCompactType`, Rust
`collection_type_to_u8`); `none` off the table.  BOOL gives 1 (`CT_BOOLEAN_TRUE`), as for a collection
element type; the header of a bool field carries 1 (true) or 2 (false) instead. -/
def compactType : Nat → Option Nat
  | 0 => some 0 | 2 => some 1 | 3 => some 3 | 4 => some 7 | 6 => some 4 | 8 => some 5
  | 10 => some 6 | 11 => some 8 | 12 => some 12 | 13 => some 11 | 14 => some 10 | 15 => some 9
  | 16 => some 13 | _ => none

/-- The TType of a compact type nibble (C++ and Java `getTType`, Rust `u8_to_type` with the bool
nibbles 1 and 2 of `read_field_begin` and `collection_u8_to_type`); `none` for unknown nibbles. -/
def ttypeOfCompact : Nat → Option Nat
  | 0 => some 0 | 1 => some 2 | 2 => some 2 | 3 => some 3 | 4 => some 6 | 5 => some 8 | 6 => some 10
  | 7 => some 4 | 8 => some 11 | 9 => some 15 | 10 => some 14 | 11 => some 13 | 12 => some 12
  | 13 => some 16 | _ => none

theorem ttypeOfCompact_compactType {t c : Nat} (h : compactType t = some c) :
    ttypeOfCompact c = some t := by
  unfold compactType at h
  split at h <;> cases h <;> rfl

theorem compactType_lt {t c : Nat} (h : compactType t = some c) : c < 16 := by
  unfold compactType at h
  split at h <;> cases h <;> decide

theorem compactType_pos {t c : Nat} (h : compactType t = some c) (ht : 0 < t) : 0 < c := by
  unfold compactType at h
  split at h <;> cases h <;> first | exact ht | decide

/-! ## Shift/mask forms

The libraries compute the encodings with shifts and masks on fixed-width integers; these are the
`Nat` forms of those steps. -/

theorem lo_nibble (b : Nat) : b &&& 0x0F = b % 16 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod b 4

theorem hi_nibble (b : Nat) : b >>> 4 = b / 16 := by
  rw [Nat.shiftRight_eq_div_pow]

set_option maxRecDepth 8192 in
theorem hi_nibble_mask {b : Nat} (h : b < 256) : (b &&& 0xF0) >>> 4 = b / 16 := by
  have : ∀ x, x < 256 → (x &&& 0xF0) >>> 4 = x / 16 := by decide
  exact this b h

theorem varint_group (n : Nat) : (n &&& 0x7F) ||| 0x80 = n % 128 + 128 := by
  have h1 : n &&& 0x7F = n % 128 := by simpa using Nat.and_two_pow_sub_one_eq_mod n 7
  rw [h1]
  have := Nat.or_two_pow_eq_add_of_lt (a := n % 128) (n := 7) (Nat.mod_lt _ (by decide))
  simpa using this

theorem varint_shr (n : Nat) : n >>> 7 = n / 128 := by
  rw [Nat.shiftRight_eq_div_pow]

theorem xor_two_pow_sub_one {x w : Nat} (h : x < 2 ^ w) : x ^^^ (2 ^ w - 1) = 2 ^ w - 1 - x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    show 2 ^ w - 1 - x = 2 ^ w - (x + 1) by omega, Nat.testBit_two_pow_sub_succ h]
  by_cases hi : i < w
  · simp [hi]
  · have : x.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi, this]

/-- Zigzag as `(n << 1) ^ (n >> 31)` on 32 bits. -/
theorem zigzag_xor32 {n : Int} (h : InI32 n) :
    zigzag n = (toU 32 n * 2 % 2 ^ 32) ^^^ (if n < 0 then 2 ^ 32 - 1 else 0) := by
  unfold InI32 at h
  by_cases hn : n < 0
  · rw [ite_eq_left hn, xor_two_pow_sub_one (Nat.mod_lt _ (by decide))]
    unfold zigzag toU
    rw [ite_eq_right (by omega)]
    omega
  · rw [ite_eq_right hn, Nat.xor_zero]
    unfold zigzag toU
    rw [ite_eq_left (by omega)]
    omega

/-- Zigzag as `(n << 1) ^ (n >> 63)` on 64 bits. -/
theorem zigzag_xor64 {n : Int} (h : InI64 n) :
    zigzag n = (toU 64 n * 2 % 2 ^ 64) ^^^ (if n < 0 then 2 ^ 64 - 1 else 0) := by
  unfold InI64 at h
  by_cases hn : n < 0
  · rw [ite_eq_left hn, xor_two_pow_sub_one (Nat.mod_lt _ (by decide))]
    unfold zigzag toU
    rw [ite_eq_right (by omega)]
    omega
  · rw [ite_eq_right hn, Nat.xor_zero]
    unfold zigzag toU
    rw [ite_eq_left (by omega)]
    omega

/-- Unzigzag as `(u >> 1) ^ -(u & 1)` on 32 bits. -/
theorem unzigzag_xor32 {u : Nat} (h : u < 2 ^ 32) :
    toU 32 (unzigzag u) = (u / 2) ^^^ (if u % 2 = 0 then 0 else 2 ^ 32 - 1) := by
  by_cases hu : u % 2 = 0
  · rw [ite_eq_left hu, Nat.xor_zero]
    unfold toU unzigzag
    rw [ite_eq_left hu]
    omega
  · rw [ite_eq_right hu, xor_two_pow_sub_one (by omega)]
    unfold toU unzigzag
    rw [ite_eq_right hu]
    omega

/-- Unzigzag as `(u >> 1) ^ -(u & 1)` on 64 bits. -/
theorem unzigzag_xor64 {u : Nat} (h : u < 2 ^ 64) :
    toU 64 (unzigzag u) = (u / 2) ^^^ (if u % 2 = 0 then 0 else 2 ^ 64 - 1) := by
  by_cases hu : u % 2 = 0
  · rw [ite_eq_left hu, Nat.xor_zero]
    unfold toU unzigzag
    rw [ite_eq_left hu]
    omega
  · rw [ite_eq_right hu, xor_two_pow_sub_one (by omega)]
    unfold toU unzigzag
    rw [ite_eq_right hu]
    omega

/-! ## Named inputs of the field-header writer

Rust's `write_field_header` (compact.rs:553) takes the short form only for `field_delta < 15`, and
computes `field_delta = field_id - self.last_write_field_id` in `i16`.  These two inputs are where it
can differ from the specification; each language states its writer and reader on them. -/

/-- An input of the field-header writer: the previous field id, the field id, the compact type. -/
structure FieldHeaderInput where
  last : Int
  id : Int
  ty : Nat
  deriving DecidableEq, Repr

/-- Delta 15, the largest delta of the short form: previous id 0, id 15, type I32 (5). -/
def exDelta15 : FieldHeaderInput := ⟨0, 15, 5⟩

/-- A delta that overflows `i16`: previous id 32767, id -32768, type I32 (5).  `id - last = -65535`,
which wraps to 1 in `i16`. -/
def exI16Overflow : FieldHeaderInput := ⟨32767, -32768, 5⟩

/-- The specified bytes of `exDelta15`: the one byte `15 << 4 | 5`. -/
theorem fieldHeader_exDelta15 :
    fieldHeader exDelta15.last exDelta15.id exDelta15.ty = [0xF5] := by decide

/-- The specified bytes of `exI16Overflow`: the long form, type 5 then the varint of
`zigzag (-32768) = 65535`. -/
theorem fieldHeader_exI16Overflow :
    fieldHeader exI16Overflow.last exI16Overflow.id exI16Overflow.ty = [0x05, 0xFF, 0xFF, 0x03] := by
  decide

/-- The long form of `exDelta15`, `[0x05, 0x1E]`, reads back as the same field. -/
theorem readFieldHeader_exDelta15_long :
    readFieldHeader exDelta15.last [0x05, 0x1E] = some (.field 5 15, []) := by decide

/-- The one-byte header `1 << 4 | 5` after id 32767 (what a writer that wraps the `i16` delta gives
for `exI16Overflow`) is malformed: `DeltaIdOverflow`. -/
theorem readFieldHeader_exI16Overflow_short :
    readFieldHeader exI16Overflow.last [0x15] = none := by decide

/-! ## Named malformed inputs

Six inputs on which each language states its M theorem, so that the languages can be compared input
by input.  The specification rejects all six; each verdict names the malformed case. -/

/-- A varint32 of 5 bytes whose value is `2^32 + 5`. -/
def exVarint32Exceeds : Bytes := [0x85, 0x80, 0x80, 0x80, 0x10]

/-- A varint64 of 10 bytes whose value is `2^64`. -/
def exVarint64Exceeds : Bytes := [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02]

/-- Five bytes with the high bit set: a varint32 longer than 5 bytes, and nothing after them. -/
def exVarint32Overlong : Bytes := [0x80, 0x80, 0x80, 0x80, 0x80]

/-- A field header, read after id 0, with type nibble 0 and delta 1. -/
def exStopNibble : Bytes := [0x10]

/-- A long-form field header of type I32, read after id 0, whose id is 32768 (zigzag value 65536). -/
def exIdOutOfRange : Bytes := [0x05, 0x80, 0x80, 0x04]

/-- A long-form list header of element type I32 whose size is `2^31`. -/
def exNegSize : Bytes := [0xF5, 0x80, 0x80, 0x80, 0x80, 0x08]

theorem readVarint_exVarint32Exceeds : readVarint 5 exVarint32Exceeds = some (2 ^ 32 + 5, []) := by
  decide

/-- The verdict on `exVarint32Exceeds`: `VarintExceeds`, malformed. -/
theorem exVarint32Exceeds_malformed :
    VarintExceeds 5 (2 ^ 32) exVarint32Exceeds ∧ readVarint32 exVarint32Exceeds = none :=
  ⟨⟨_, _, readVarint_exVarint32Exceeds, by decide⟩, by decide⟩

theorem readVarint_exVarint64Exceeds : readVarint 10 exVarint64Exceeds = some (2 ^ 64, []) := by
  decide

/-- The verdict on `exVarint64Exceeds`: `VarintExceeds`, malformed. -/
theorem exVarint64Exceeds_malformed :
    VarintExceeds 10 (2 ^ 64) exVarint64Exceeds ∧ readVarint64 exVarint64Exceeds = none :=
  ⟨⟨_, _, readVarint_exVarint64Exceeds, by decide⟩, by decide⟩

/-- The verdict on `exVarint32Overlong`: `VarintOverlong 5`, malformed. -/
theorem exVarint32Overlong_malformed :
    VarintOverlong 5 exVarint32Overlong ∧ readVarint32 exVarint32Overlong = none := by
  refine ⟨?_, by decide⟩
  unfold VarintOverlong
  decide

/-- Read as a varint of at most 10 bytes (C++'s `readVarint32` goes through its varint64 reader), the
same bytes end inside the varint: `VarintTruncated 10`. -/
theorem exVarint32Overlong_truncated10 : VarintTruncated 10 exVarint32Overlong := by
  unfold VarintTruncated
  decide

/-- The verdict on `exStopNibble` after id 0: `StopNibble`, malformed. -/
theorem exStopNibble_malformed : StopNibble 0x10 ∧ readFieldHeader 0 exStopNibble = none := by
  refine ⟨?_, by decide⟩
  unfold StopNibble
  decide

/-- The verdict on `exIdOutOfRange` after id 0: the id 32768 is `IdOutOfRange`, malformed. -/
theorem exIdOutOfRange_malformed :
    readVarint32 [0x80, 0x80, 0x04] = some (65536, []) ∧ unzigzag 65536 = 32768 ∧
      IdOutOfRange 65536 ∧ readFieldHeader 0 exIdOutOfRange = none := by
  refine ⟨by decide, by decide, ?_, by decide⟩
  unfold IdOutOfRange
  decide

/-- The verdict on `exNegSize`: the size `2^31` is `NegSize`, malformed. -/
theorem exNegSize_malformed :
    readVarint32 [0x80, 0x80, 0x80, 0x80, 0x08] = some (2 ^ 31, []) ∧ NegSize (2 ^ 31) ∧
      readListHeader exNegSize = none := by
  decide

/-! Check values. -/
example : varint 300 = [0xAC, 0x02] := by decide
example : varint (2 ^ 32 - 1) = [0xFF, 0xFF, 0xFF, 0xFF, 0x0F] := by decide
example : zigzag (-1) = 1 ∧ zigzag 1 = 2 ∧ zigzag (-2147483648) = 4294967295 := by decide
example : fieldHeader 0 1 5 = [0x15] := by decide
example : fieldHeader 0 16 5 = [0x05, 0x20] := by decide
example : fieldHeader 3 3 5 = [0x05, 0x06] := by decide
example : listHeader 3 5 = [0x35] := by decide
example : listHeader 15 8 = [0xF8, 0x0F] := by decide
example : beI32 (-2) = [0xFF, 0xFF, 0xFF, 0xFE] := by decide
example : readVarint32 [0x80, 0x80, 0x80, 0x80, 0x80, 0x00] = none := by decide
example : readVarint 10 [0x80, 0x80, 0x80, 0x80, 0x80, 0x00] = some (0, []) := by decide
example : readFieldHeader 0 [0x10] = none := by decide
example : readFieldHeader 0 [0x15, 0x00] = some (.field 5 1, [0x00]) := by decide

end EquivLean.Demo.Thrift.Spec
