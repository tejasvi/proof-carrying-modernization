import EquivLean.Modernize.Cbstm03a.Java.Mw.Lem
import EquivLean.Modernize.Cbstm03a.Java.Iface1
import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03A → Java: `memWrite`, the loop invariant and the segments' weakest precondition

One cut point, the loop head (statement 5: `if pos >= n goto label5`). Locals: `slots` 0, `off` 1, `o` 2, `$l4` 3,
`$b1` 4, `n` 5, `idx` 6, `len` 7, `within` 8, `$i6` 9, `pos` 10, `take` 11, `s` 12, `cur` 13, `$r1` 14, `cur#7` 15.
At the loop head the slots hold every entry memory with the first `pos` characters of `s` written (`MemK`, kept
folded across the symbolic executor); `pos` ranges as cbA-mem planned: `0 ≤ pos`, and `pos = 0` or `off < MEM_SZ`
(`pos ≤ n` is not needed: past the end `t.take pos = t`).

`bodyWP_cut_insert` (virtual cut points) and the fuel lemmas are cbA-thin3's (`CbAThin3/Cut.lean`), for `callWP`
at depth 0 (`callWP0_mono`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space keeps_refl)

namespace EquivLean.Modernize.Cbstm03a.Java

/-- The callees of `memWrite`: `spaces` and the slot geometry (the interface contracts). -/
def mwCallees : Contracts :=
  [(spacesSig, spacesSpecI), (slotIndexSig, slotIndexSpec), (slotLenSig, slotLenSpec), (slotStartSig, slotStartSpec)]

namespace Mw

/-- What the closers need at the loop head: every memory the slots held at entry, with the first `p` characters
of `t` written, is held now; only the slots array changed; inits/statics kept. -/
@[irreducible] def MemK (σ0 σ : State) (a : Addr) (off : I64) (t : JStr) (p : Nat) : Prop :=
  (∀ m, SlotsAt σ0 a m → SlotsAt σ a (memWr m off.toInt (t.take p))) ∧ Keeps (· = a) σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics

theorem memK_init (σ0 : State) (a : Addr) (off : I64) (t : JStr) : MemK σ0 σ0 a off t 0 := by
  unfold MemK
  exact ⟨fun m h => by rw [memWr_take_zero]; exact h, keeps_refl _ _, rfl, rfl⟩

/-- The facts at the loop head. -/
def MwAt (σ0 : State) (fr : Frame) (σ : State) (a : Addr) (off : I64) (x : Addr) (t : JStr) (pos n : I32) :
    Prop :=
  fr.get 0 = some (.ref a) ∧ fr.get 1 = some (.long off) ∧ fr.get 12 = some (.ref x) ∧
  fr.get 10 = some (.int pos) ∧ fr.get 5 = some (.int n) ∧
  σ.heap x = some (.str t) ∧ σ0.heap x = some (.str t) ∧ n.toInt = t.length ∧ t.length < 2147483648 ∧
  -2147483648 < off.toInt ∧ 0 ≤ pos.toInt ∧ (pos.toInt = 0 ∨ off.toInt < 171156) ∧
  σ.initOf "Cbstm03a" = .done ∧ MemK σ0 σ a off t pos.toInt.toNat

def mwInv5 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (a : Addr) (off : I64) (x : Addr), args = [.ref a, .long off, .ref x] →
    ∃ t pos n, MwAt σ0 fr σ a off x t pos n

def memWriteInv : Invariants := [(5, mwInv5)]

/-- The paths of `memWrite` from statement `pc`, with extra (virtual) cut points `C`. -/
@[irreducible] def mwWPc (args : List Value) (σ0 : State) (C : Cuts) (fuel pc : Nat) (fr : Frame) (σ : State) :
    Prop :=
  bodyWP Gen.prog (callWP Gen.prog mwCallees.env 0) Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)»
    (C ++ memWriteInv.inst args σ0) (memWriteSpec.post args σ0) fuel pc fr σ

/-! ## Virtual cut points (cbA-thin3's `Cut.lean`, for `callWP` at depth 0) -/

/-- A handler monotone in its continuation. -/
abbrev HMono (H : Handler) : Prop :=
  ∀ sig c args σ (K K' : Outcome → Prop), (∀ o, K o → K' o) → H sig c args σ K → H sig c args σ K'

theorem callWP0_mono (P : Program) (Γ : SpecEnv) : HMono (callWP P Γ 0) := by
  intro sig c args σ K K' hK h
  unfold callWP at h ⊢
  cases hΓ : Γ sig <;> cases c <;> simp only [hΓ] at h ⊢
  all_goals first
    | exact h.elim
    | exact ⟨h.1, h.2.1, fun o ho => hK o (h.2.2 o ho)⟩
    | exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun o ho => hK o (h.2.2.2.2 o ho)⟩

theorem bodyWP_fuel_succ {P : Program} {H : Handler} (hH : HMono H) (b : Body) (I : Cuts)
    (Post : Outcome → Prop) :
    ∀ n pc fr σ, bodyWP P H b I Post n pc fr σ → bodyWP P H b I Post (n + 1) pc fr σ
  | 0, _, _, _, h => by rw [bodyWP_eq_false] at h; exact h.elim
  | n + 1, pc, fr, σ, h => by
    rw [bodyWP_succ] at h ⊢
    refine wpR_le hH _ _ _ (fun r hr => ?_) h
    revert hr
    cases afterStep P b pc fr r with
    | done o => exact id
    | cont pc' fr' σ' =>
      simp only
      cases I.lookup pc' with
      | some A => exact id
      | none => exact bodyWP_fuel_succ hH b I Post n pc' fr' σ'

theorem bodyWP_fuel_le {P : Program} {H : Handler} (hH : HMono H) (b : Body) (I : Cuts)
    (Post : Outcome → Prop) {n m : Nat} (hnm : n ≤ m) :
    ∀ pc fr σ, bodyWP P H b I Post n pc fr σ → bodyWP P H b I Post m pc fr σ := by
  induction hnm with
  | refl => exact fun _ _ _ h => h
  | step _ ih => exact fun pc fr σ h => bodyWP_fuel_succ hH b I Post _ pc fr σ (ih pc fr σ h)

/-- A virtual cut point `k` with assertion `A`: the paths to `k` establish `A`, the paths from `k` continue. -/
theorem bodyWP_cut_insert {P : Program} {H : Handler} (hH : HMono H) (b : Body) (I : Cuts)
    (Post : Outcome → Prop) (k : Nat) (hk : I.lookup k = none) (A : Frame → State → Prop) (n0 : Nat)
    (hA : ∀ fr σ, A fr σ → bodyWP P H b I Post n0 k fr σ) :
    ∀ n pc fr σ, bodyWP P H b ((k, A) :: I) Post n pc fr σ → bodyWP P H b I Post (n + n0) pc fr σ
  | 0, _, _, _, h => by rw [bodyWP_eq_false] at h; exact h.elim
  | n + 1, pc, fr, σ, h => by
    rw [show n + 1 + n0 = (n + n0) + 1 by omega, bodyWP_succ]
    rw [bodyWP_succ] at h
    refine wpR_le hH _ _ _ (fun r hr => ?_) h
    revert hr
    cases afterStep P b pc fr r with
    | done o => exact id
    | cont pc' fr' σ' =>
      simp only [List.lookup_cons]
      by_cases hp : pc' = k
      · subst hp
        simp only [beq_self_eq_true, hk]
        intro hA'
        exact bodyWP_fuel_le hH b I Post (Nat.le_add_left n0 n) _ _ _ (hA fr' σ' hA')
      · have hb : (pc' == k) = false := by simpa using hp
        simp only [hb]
        cases I.lookup pc' with
        | some A' => exact id
        | none => exact bodyWP_cut_insert hH b I Post k hk A n0 hA n pc' fr' σ'

/-- `mwWPc` with a virtual cut point `k ≠ 5`. -/
theorem mwWPc_cut (args : List Value) (σ0 : State) (k : Nat) (hk : k ≠ 5) (A : Frame → State → Prop) (n0 : Nat)
    (hA : ∀ fr σ, A fr σ → mwWPc args σ0 [] n0 k fr σ) (n pc : Nat) (fr : Frame) (σ : State)
    (h : mwWPc args σ0 [(k, A)] n pc fr σ) : mwWPc args σ0 [] (n + n0) pc fr σ := by
  unfold mwWPc at hA h ⊢
  have hk' : (memWriteInv.inst args σ0).lookup k = none := by
    simp only [memWriteInv, Invariants.inst, List.map_cons, List.map_nil, List.lookup_cons, List.lookup_nil]
    have : (k == 5) = false := by simpa using hk
    simp only [this]
  exact bodyWP_cut_insert (callWP0_mono _ _) _ _ _ k hk' A n0 hA n pc fr σ h

/-- `mwWPc` at a larger fuel. -/
theorem mwWPc_fuel (args : List Value) (σ0 : State) (C : Cuts) {n m : Nat} (hnm : n ≤ m) (pc : Nat) (fr : Frame)
    (σ : State) (h : mwWPc args σ0 C n pc fr σ) : mwWPc args σ0 C m pc fr σ := by
  unfold mwWPc at h ⊢
  exact bodyWP_fuel_le (callWP0_mono _ _) _ _ _ hnm pc fr σ h

end Mw

end EquivLean.Modernize.Cbstm03a.Java
