import EquivLean.Modernize.Cbstm03a.Java.Thin3.CS.Step
import EquivLean.Modernize.Cbstm03a.Java.RunPure

/-!
# CBSTM03A → Java, termination of `createStatement`: the segments' shared definitions

* `WPT n pc fr σ`: the termination paths from `pc` (irreducible: destructuring hypotheses next to an unfolded
  `bodyWP` at a successor fuel unfolds it by `whnf`); `WPT_eq` unfolds it.
* `SLoc σ fr i n`: local `i` holds a string of at most `n` characters.
* `VA res σA ks X`: the assertion at a virtual cut point after a computation from `σA`: `res` in its local, the
  heap only grown, the class state kept, the string locals `ks`, an extra fact `X`.
* The lengths of the texts the callees return (`paraStr`, `starStr`, `currStr`), and `currBal`'s bound.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space zpadStr zpadStr_length fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

open EquivLean.Modernize.Cbstm03a.Java

theorem nat_self_ne_add_one (n : Nat) : (n = n + 1) ↔ False := ⟨fun h => by omega, False.elim⟩
theorem nat_self_ne_add_succ (n k : Nat) : (n = n + k + 1) ↔ False := ⟨fun h => by omega, False.elim⟩

@[irreducible] def WPT (n pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog HT csBody [] (fun _ => True) n pc fr σ

theorem WPT_eq (n pc : Nat) (fr : Frame) (σ : State) :
    WPT n pc fr σ = bodyWP Gen.prog HT csBody [] (fun _ => True) n pc fr σ := by
  unfold WPT; rfl

/-- Local `i` holds a string of at most `n` characters. -/
def SLoc (σ : State) (fr : Frame) (i n : Nat) : Prop :=
  ∃ x s, fr.get i = some (.ref x) ∧ σ.heap x = some (.str s) ∧ s.length ≤ n

/-- At a virtual cut point after a computation from `σA`: `res` in its local, the `Result` object and its lists
unchanged, the class state kept, the string locals `ks` (index, bound), the extra fact `X`. -/
def VA (res ls lh : Addr) (σA : State) (ks : List (Nat × Nat)) (X : Frame → State → Prop) (fr : Frame)
    (σ : State) : Prop :=
  fr.get 22 = some (.ref res) ∧ σ.heap res = σA.heap res ∧ σ.heap ls = σA.heap ls ∧ σ.heap lh = σA.heap lh ∧
  σ.inits = σA.inits ∧ (∀ p ∈ ks, SLoc σ fr p.1 p.2) ∧ X fr σ

/-- `RJ` at a virtual cut point after a computation. -/
theorem rj_va {res ls lh : Addr} {σS σA σ : State} {ks : List (Nat × Nat)} {X : Frame → State → Prop} {fr : Frame}
    (h : RJ res ls lh σS σA) (hv : VA res ls lh σA ks X fr σ) : RJ res ls lh σ σ := by
  obtain ⟨⟨fs, h1, h2, h3⟩, ⟨xs, m, h4⟩, ⟨xs2, m2, h5⟩, h6, -⟩ := h
  obtain ⟨-, e1, e2, e3, e4, -, -⟩ := hv
  exact ⟨⟨fs, by rw [e1, h1], h2, h3⟩, ⟨xs, m, by rw [e2, h4]⟩, ⟨xs2, m2, by rw [e3, h5]⟩,
    by rw [initOf_of_inits e4]; exact h6, fun _ _ hx => hx⟩

theorem rj_restart {res ls lh : Addr} {σS σ : State} (h : RJ res ls lh σS σ) : RJ res ls lh σ σ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun _ _ hx => hx⟩

theorem sloc_mono {σ σ' : State} {fr : Frame} {i n : Nat} (h : SLoc σ fr i n) (hm : StrMono σ σ') :
    SLoc σ' fr i n := by
  obtain ⟨x, s, h1, h2, h3⟩ := h
  exact ⟨x, s, h1, hm x s h2, h3⟩

theorem paraStr_length (p f : JStr) : (paraStr p f).length = 100 := by
  unfold paraStr; exact fixStr_length _ 100

theorem starStr_length (p f : JStr) : (starStr p f).length = 100 := by
  unfold starStr; exact fixStr_length _ 100

theorem currStr_length (v : Int) : (currStr v).length = 13 := by
  have hdot : (JStr.ofString ".").length = 1 := by decide +kernel
  have hs : (signStr v).length = 1 := by
    unfold signStr
    split
    · decide +kernel
    · decide +kernel
  simp only [currStr, List.length_append, zpadStr_length, hdot, hs]

/-- `currBal` from a 12-character zoned text is not `Long.MIN_VALUE`. -/
theorem zoned12_gt {t : JStr} (h : t.length = 12) : -9223372036854775808 < (BitVec.ofInt 64 (zonedVal t)).toInt := by
  have hb := zonedVal_bound t
  rw [h] at hb
  have e : ((10 ^ 12 : Nat) : Int) = 1000000000000 := by decide
  rw [e] at hb
  rw [i64_ofInt_toInt_small (by omega) (by omega)]
  omega

/-- `currBal` (local 0): the value of a 12-character zoned text. -/
def Bal (fr : Frame) : Prop :=
  ∃ t : JStr, t.length = 12 ∧ fr.get 0 = some (.long (BitVec.ofInt 64 (zonedVal t)))

end EquivLean.Modernize.Cbstm03a.Java.Thin3
