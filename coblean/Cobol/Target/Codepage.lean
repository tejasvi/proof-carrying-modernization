/-
# EBCDIC code page 037

CP037 maps the 256 bytes bijectively onto the Latin-1 code points 0-255 (tables generated
from Python's `cp037` codec).  Used to relate COBOL alphanumeric bytes to Java / Rust
strings in equivalence statements.
-/
namespace Cobol.Codepage

/-- Unicode code point of each CP037 byte. -/
def cp037 : Array Nat := #[
    0, 1, 2, 3, 156, 9, 134, 127, 151, 141, 142, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 157, 133, 8, 135, 24, 25, 146, 143, 28, 29, 30, 31,
    128, 129, 130, 131, 132, 10, 23, 27, 136, 137, 138, 139, 140, 5, 6, 7,
    144, 145, 22, 147, 148, 149, 150, 4, 152, 153, 154, 155, 20, 21, 158, 26,
    32, 160, 226, 228, 224, 225, 227, 229, 231, 241, 162, 46, 60, 40, 43, 124,
    38, 233, 234, 235, 232, 237, 238, 239, 236, 223, 33, 36, 42, 41, 59, 172,
    45, 47, 194, 196, 192, 193, 195, 197, 199, 209, 166, 44, 37, 95, 62, 63,
    248, 201, 202, 203, 200, 205, 206, 207, 204, 96, 58, 35, 64, 39, 61, 34,
    216, 97, 98, 99, 100, 101, 102, 103, 104, 105, 171, 187, 240, 253, 254, 177,
    176, 106, 107, 108, 109, 110, 111, 112, 113, 114, 170, 186, 230, 184, 198, 164,
    181, 126, 115, 116, 117, 118, 119, 120, 121, 122, 161, 191, 208, 221, 222, 174,
    94, 163, 165, 183, 169, 167, 182, 188, 189, 190, 91, 93, 175, 168, 180, 215,
    123, 65, 66, 67, 68, 69, 70, 71, 72, 73, 173, 244, 246, 242, 243, 245,
    125, 74, 75, 76, 77, 78, 79, 80, 81, 82, 185, 251, 252, 249, 250, 255,
    92, 247, 83, 84, 85, 86, 87, 88, 89, 90, 178, 212, 214, 210, 211, 213,
    48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 179, 219, 220, 217, 218, 159
]

/-- CP037 byte of each Latin-1 code point. -/
def cp037Inv : Array Nat := #[
    0, 1, 2, 3, 55, 45, 46, 47, 22, 5, 37, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 60, 61, 50, 38, 24, 25, 63, 39, 28, 29, 30, 31,
    64, 90, 127, 123, 91, 108, 80, 125, 77, 93, 92, 78, 107, 96, 75, 97,
    240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 122, 94, 76, 126, 110, 111,
    124, 193, 194, 195, 196, 197, 198, 199, 200, 201, 209, 210, 211, 212, 213, 214,
    215, 216, 217, 226, 227, 228, 229, 230, 231, 232, 233, 186, 224, 187, 176, 109,
    121, 129, 130, 131, 132, 133, 134, 135, 136, 137, 145, 146, 147, 148, 149, 150,
    151, 152, 153, 162, 163, 164, 165, 166, 167, 168, 169, 192, 79, 208, 161, 7,
    32, 33, 34, 35, 36, 21, 6, 23, 40, 41, 42, 43, 44, 9, 10, 27,
    48, 49, 26, 51, 52, 53, 54, 8, 56, 57, 58, 59, 4, 20, 62, 255,
    65, 170, 74, 177, 159, 178, 106, 181, 189, 180, 154, 138, 95, 202, 175, 188,
    144, 143, 234, 250, 190, 160, 182, 179, 157, 218, 155, 139, 183, 184, 185, 171,
    100, 101, 98, 102, 99, 103, 158, 104, 116, 113, 114, 115, 120, 117, 118, 119,
    172, 105, 237, 238, 235, 239, 236, 191, 128, 253, 254, 251, 252, 173, 174, 89,
    68, 69, 66, 70, 67, 71, 156, 72, 84, 81, 82, 83, 88, 85, 86, 87,
    140, 73, 205, 206, 203, 207, 204, 225, 112, 221, 222, 219, 220, 141, 142, 223
]

/-- Character of a CP037 byte. -/
def cp037Char (b : UInt8) : Char := Char.ofNat (cp037.getD b.toNat 0)

/-- CP037 byte of a character (`none` outside Latin-1). -/
def cp037Byte (ch : Char) : Option UInt8 :=
  if ch.toNat < 256 then some (UInt8.ofNat (cp037Inv.getD ch.toNat 0)) else none

/-- Decode CP037 bytes to a string. -/
def decode037 (bs : List UInt8) : String := String.ofList (bs.map cp037Char)

/-- Encode a string in CP037 (`none` if a character is not representable). -/
def encode037 (s : String) : Option (List UInt8) := s.toList.mapM cp037Byte

set_option maxRecDepth 100000 in
/-- Exhaustive checks of the tables (kernel evaluation over the 256 entries). -/
theorem cp037_checks :
    (List.range 256).all (fun b => cp037Inv.getD (cp037.getD b 0) 0 == b &&
      cp037.getD (cp037Inv.getD b 0) 0 == b && decide (cp037.getD b 0 < 256) &&
      decide (cp037Inv.getD b 0 < 256)) = true := by
  decide +kernel

theorem cp037_check (b : Nat) (hb : b < 256) :
    cp037Inv.getD (cp037.getD b 0) 0 = b ∧ cp037.getD (cp037Inv.getD b 0) 0 = b ∧
      cp037.getD b 0 < 256 ∧ cp037Inv.getD b 0 < 256 := by
  have h := List.all_eq_true.mp cp037_checks b (List.mem_range.mpr hb)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem Char.toNat_ofNat_lt256 (n : Nat) (h : n < 256) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := Or.inl (by omega)
  simp only [Char.ofNat, hv, ↓reduceDIte, Char.ofNatAux, Char.toNat]
  simp [UInt32.toNat_ofNatLT]

/-- `cp037Byte` is a left inverse of `cp037Char`. -/
theorem cp037Byte_cp037Char (b : UInt8) : cp037Byte (cp037Char b) = some b := by
  have hb := b.toNat_lt
  obtain ⟨h2, -, h1, -⟩ := cp037_check b.toNat hb
  unfold cp037Byte cp037Char
  rw [Char.toNat_ofNat_lt256 _ h1]
  simp only [h1, ↓reduceIte, h2, Option.some.injEq]
  exact UInt8.ofNat_toNat

/-- Characters of a CP037 byte are determined by the byte. -/
theorem cp037Char_eq_iff (b : UInt8) (ch : Char) (x : UInt8) (h : cp037Byte ch = some x) :
    cp037Char b = ch ↔ b = x := by
  constructor
  · intro hb
    subst hb
    rw [cp037Byte_cp037Char] at h
    exact Option.some.inj h
  · intro hb
    subst hb
    unfold cp037Byte at h
    split at h
    · rename_i hlt
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨-, h2, -, h1⟩ := cp037_check ch.toNat hlt
      unfold cp037Char
      have : (UInt8.ofNat (cp037Inv.getD ch.toNat 0)).toNat = cp037Inv.getD ch.toNat 0 := by
        simp only [UInt8.toNat_ofNat']; omega
      rw [this, h2]
      exact Char.ofNat_toNat ch
    · simp at h

end Cobol.Codepage
