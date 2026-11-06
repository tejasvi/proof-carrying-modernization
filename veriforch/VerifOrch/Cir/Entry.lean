import CIR

/-!
# Calling conventions of test entry points (mechanical preconditions)

A test entry point that takes arbitrary input (a property test, a fuzz harness, a test program reading its
command line) is stated for every input that its C calling convention allows. The precondition depends only on
the entry point's signature. These definitions are fixed here once, and no model writes them.

The memory is any memory that extends the module's initial memory:
* the globals keep their initial values;
* the argument objects live in fresh blocks after the globals.

* `InitExt M m`: `m` is well formed (no block at or above `m.next`, as in every memory a run reaches) and agrees
  with `Module.initMem M` on every block of the initial memory. Without well-formedness the argument objects could
  sit at `m.next`, where the entry point's first local would overwrite them.
* `CStrAt lo m p`: `p` points to the start of a writable, NUL-terminated string (cirlean's `readCStr`
  succeeds) in a block numbered at least `lo`.
* `MainArgs lo m argc argv`: the arguments of `int main(int argc, char **argv)`. `argv` points to the first of
  `argc + 1` pointers in a writable block: `argc` pointers to distinct strings, then a null pointer.
* `ReadableBuf lo m p n`: `p` points to the start of a `uint8_t` array of exactly `n` elements, as libFuzzer
  passes its input to `int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)` (a copy of `size` bytes).
  `n < 2^63`: no object is larger than `PTRDIFF_MAX` bytes (glibc's `malloc`, GCC and Clang refuse larger ones),
  so pointer differences within the buffer are defined.
-/

namespace VerifOrch.Cir

open CIR

/-- `m` is a well-formed extension of the module's initial memory: the same blocks below its `next`, more blocks
after, none at or above `m.next`. -/
def InitExt (M : Module) (m : Mem) : Prop :=
  m.WF ∧ M.initMem.next ≤ m.next ∧ ∀ b, b < M.initMem.next → m.blocks b = M.initMem.blocks b

/-- `p` points to the start of a writable NUL-terminated string in a block numbered at least `lo`. -/
def CStrAt (lo : Nat) (m : Mem) (p : Ptr) : Prop :=
  ∃ b blk cs, p = .loc b [.idx 0] ∧ lo ≤ b ∧ m.live? b = some blk ∧ blk.kind ≠ .readonly ∧
    CIR.Std.readCStr m p = .ok cs

/-- The C calling convention of `int main(int argc, char **argv)`. -/
def MainArgs (lo : Nat) (m : Mem) (argc : Int) (argv : Ptr) : Prop :=
  0 ≤ argc ∧ ∃ (b : Nat) (blk : MemBlock) (xs : List Val) (bs : Nat → Nat),
    argv = .loc b [.idx 0] ∧ lo ≤ b ∧ m.live? b = some blk ∧ blk.kind ≠ .readonly ∧ blk.val = .arr xs ∧
    xs.length = argc.toNat + 1 ∧ xs[argc.toNat]? = some (.ptr .null) ∧
    (∀ i, i < argc.toNat → xs[i]? = some (.ptr (.loc (bs i) [.idx 0])) ∧ bs i ≠ b ∧
      CStrAt lo m (.loc (bs i) [.idx 0])) ∧
    (∀ i j, i < j → j < argc.toNat → bs i ≠ bs j)

/-- `p` points to the start of a `uint8_t` array of exactly `n` elements (`const uint8_t *data, size_t size`),
`n < 2^63`. -/
def ReadableBuf (lo : Nat) (m : Mem) (p : Ptr) (n : Int) : Prop :=
  0 ≤ n ∧ n < 2 ^ 63 ∧ ∃ (b : Nat) (blk : MemBlock) (xs : List Val),
    p = .loc b [.idx 0] ∧ lo ≤ b ∧ m.live? b = some blk ∧ blk.ty = .array (.int false 8) xs.length ∧
    blk.val = .arr xs ∧ xs.length = n.toNat ∧
    ∀ j, j < n.toNat → ∃ k : Int, xs[j]? = some (.int k) ∧ 0 ≤ k ∧ k ≤ 255

end VerifOrch.Cir
