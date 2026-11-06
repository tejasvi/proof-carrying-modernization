import EquivLean.Bridge.Aeneas.Digits
import EquivLean.Bridge.Aeneas.SpecAuto
import EquivLean.Modernize.Cbstm03a.RustSpec
import EquivLean.Modernize.Cbstm03a.StmBridge

/-!
# CBSTM03A → Rust: shared definitions and CP037/Latin-1 bridge for `RustRun1`–`RustRun5`

Every byte buffer in `cbstm03a.run` holds the Latin-1 bytes (`latL bs = bs.map (byteOf ∘ cp037Code)`)
of the corresponding EBCDIC byte list `bs : List UInt8` in `Cobol.StmCore`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol Cobol.StmCore EquivLean.Cobol.Rec
open EquivLean.Modernize.Cbstm03a.StmBridge EquivLean.Modernize.Cbstm03a.Model

namespace EquivLean.Modernize.Cbstm03a.Rust

/-! ## 1. CP037 ↔ Latin-1 byte round trips -/

theorem cp037Code_lt_fin : ∀ n : Fin 256, cp037Code (UInt8.ofNat n.val) < 256 := by
  decide +kernel

theorem cp037Code_lt (b : UInt8) : cp037Code b < 256 := by
  have h := cp037Code_lt_fin ⟨b.toNat, b.toNat_lt⟩
  simpa only [UInt8.ofNat_toNat] using h

/-- The Rust `U8` (Latin-1 code point) of an EBCDIC byte `b`. -/
def lat (b : UInt8) : U8 := byteOf (cp037Code b)

/-- The Rust `List U8` (Latin-1 bytes) of a list of EBCDIC bytes `bs`. -/
def latL (bs : List UInt8) : List U8 := bs.map lat

/-- A line of CP037 code points `l : List Nat` as `List U8`. -/
def u8Line (l : List Nat) : List U8 := l.map byteOf

theorem lat_val (b : UInt8) : (lat b).val = cp037Code b :=
  byteOf_val (cp037Code b) (cp037Code_lt b)

@[simp] theorem length_latL (bs : List UInt8) : (latL bs).length = bs.length := by
  simp [latL]

theorem latL_val (bs : List UInt8) : (latL bs).map (·.val) = bs.map cp037Code := by
  simp only [latL, List.map_map, Function.comp_def, lat_val]

theorem latL_append (a b : List UInt8) : latL (a ++ b) = latL a ++ latL b := by
  simp [latL]

theorem latL_take (n : Nat) (bs : List UInt8) : latL (bs.take n) = (latL bs).take n := by
  simp [latL, List.map_take]

theorem latL_drop (n : Nat) (bs : List UInt8) : latL (bs.drop n) = (latL bs).drop n := by
  simp [latL, List.map_drop]

theorem latL_replicate (n : Nat) (b : UInt8) :
    latL (List.replicate n b) = List.replicate n (lat b) := by
  simp [latL, List.map_replicate]

@[simp] theorem lat_space : lat 64 = 32#u8 := by decide +kernel
@[simp] theorem lat_zero_char : lat 240 = 48#u8 := by decide +kernel
@[simp] theorem lat_star : lat 92 = 42#u8 := by decide +kernel
@[simp] theorem lat_dash : lat 96 = 45#u8 := by decide +kernel
@[simp] theorem lat_dollar : lat 91 = 36#u8 := by decide +kernel
@[simp] theorem lat_dot : lat 75 = 46#u8 := by decide +kernel

theorem cp037Code_inj_fin : ∀ a b : Fin 256,
    cp037Code (UInt8.ofNat a.val) = cp037Code (UInt8.ofNat b.val) → a.val = b.val := by
  decide +kernel

theorem cp037Code_inj {a b : UInt8} (h : cp037Code a = cp037Code b) : a = b := by
  apply UInt8.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
  exact cp037Code_inj_fin ⟨a.toNat, a.toNat_lt⟩ ⟨b.toNat, b.toNat_lt⟩
    (by simpa only [UInt8.ofNat_toNat] using h)

theorem lat_inj {a b : UInt8} (h : lat a = lat b) : a = b := by
  have hv : (lat a).val = (lat b).val := congrArg UScalar.val h
  rw [lat_val, lat_val] at hv
  exact cp037Code_inj hv

theorem latL_inj {a b : List UInt8} : latL a = latL b ↔ a = b :=
  ⟨fun h => List.map_injective_iff.2 (fun _ _ => lat_inj) h, fun h => h ▸ rfl⟩

theorem u8Line_val {l : List Nat} (hl : ∀ c ∈ l, c < 256) :
    (u8Line l).map (·.val) = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [u8Line, List.map_cons, byteOf_val c (hl c (List.mem_cons_self ..))]
    exact congrArg (c :: ·) (ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)))

theorem latL_eq_u8Line (bs : List UInt8) : latL bs = u8Line (bs.map cp037Code) := by
  simp [latL, u8Line, lat, List.map_map, Function.comp_def]

/-! ## 2. Pure-Lean models of `put`, `fill`, and `Mem` -/

/-- Pure-Lean model of `put(dst, off, len, src)`. -/
def putL (dst : List U8) (off len : Nat) (src : List U8) : List U8 :=
  dst.take off ++ (src.take len ++ List.replicate (len - src.length) 32#u8) ++ dst.drop (off + len)

/-- Pure-Lean model of `fill(dst, off, len, ch)`. -/
def fillL (dst : List U8) (off len : Nat) (ch : U8) : List U8 :=
  dst.take off ++ List.replicate len ch ++ dst.drop (off + len)

@[simp] theorem length_putL (dst : List U8) (off len : Nat) (src : List U8)
    (h : off + len ≤ dst.length) : (putL dst off len src).length = dst.length := by
  simp [putL]; omega

@[simp] theorem length_fillL (dst : List U8) (off len : Nat) (ch : U8)
    (h : off + len ≤ dst.length) : (fillL dst off len ch).length = dst.length := by
  simp [fillL]; omega

/-- Contract of the sparse table memory `mem` after `8500-READTRNX-READ` on `gs = grp (trs.map TrnxRecord.encode)`. -/
def MemLoaded (mem : cbstm03a.Mem) (gs : List (List (List UInt8))) : Prop :=
  gs.length ≤ 50 ∧
  (∀ g ∈ gs, 1 ≤ g.length ∧ g.length ≤ 10 ∧ ∀ r ∈ g, r.length = 350) ∧
  (∀ (c : Std.I64), 1 ≤ c.val → c.val ≤ gs.length →
    let g := gs.getD (c.val.toNat - 1) []
    (∀ (off : Std.I64) (dst : Slice U8), off.val = (c.val - 1) * 3356 → dst.val.length = 16 →
      ∃ s' : Slice U8, cbstm03a.mem_get mem off dst = .ok s' ∧ s'.val = latL (gCard g)) ∧
    (∃ cnt : Std.I64, cbstm03a.read_trct mem c = .ok cnt ∧ cnt.val = g.length) ∧
    (∀ (t : Std.I64), 1 ≤ t.val → t.val ≤ g.length →
      let r := g.getD (t.val.toNat - 1) []
      (∀ (off : Std.I64) (dst : Slice U8),
        off.val = (c.val - 1) * 3356 + 16 + (t.val - 1) * 334 → dst.val.length = 16 →
        ∃ s' : Slice U8, cbstm03a.mem_get mem off dst = .ok s' ∧ s'.val = latL (tId r)) ∧
      (∀ (off : Std.I64) (dst : Slice U8),
        off.val = (c.val - 1) * 3356 + 16 + (t.val - 1) * 334 + 16 → dst.val.length = 318 →
        ∃ s' : Slice U8, cbstm03a.mem_get mem off dst = .ok s' ∧ s'.val = latL (tRest r))))

end EquivLean.Modernize.Cbstm03a.Rust
