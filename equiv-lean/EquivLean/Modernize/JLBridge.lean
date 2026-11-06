import EquivLean.Bridge.Jimple.CobolRec
import EquivLean.Modernize.JL.Cbact02cLemmas

/-!
# From JimpleLean's contracts to ours: the shared lemmas

JimpleLean's session states the contracts of the CardDemo translations (`JL/`) with the strings of
a list (`StrsAt`) and the texts the Java code builds (`fixStr`, `zpadStr`); ours are stated with
references to strings (`JStrAt`, `Forall2`) and the field values of the records.  The lemmas the
bridges (`<Prog>/JavaRun.lean`) share.
-/

open EquivLean.Cobol.Rec Jimple

namespace EquivLean.Modernize.JLBridge

open JL

/-! ## Lists -/

theorem forall2_map_eq {α β γ : Type} {f : α → γ} {g : β → γ} :
    ∀ {xs : List α} {vs : List β}, Forall2 (fun x v => f x = g v) xs vs → xs.map f = vs.map g
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by simp [h, forall2_map_eq hs]

theorem forall2_flatMap_eq {α β γ : Type} {f : α → List γ} {g : β → List γ} :
    ∀ {xs : List α} {vs : List β}, Forall2 (fun x v => f x = g v) xs vs →
      xs.flatMap f = vs.flatMap g
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by simp [h, forall2_flatMap_eq hs]

theorem forall2_mem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {vs : List β}, Forall2 R xs vs → ∀ x ∈ xs, ∃ v ∈ vs, R x v
  | [], [], .nil, _, h => by simp at h
  | _ :: _, v :: _, .cons h hs, x, hx => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨v, by simp, h⟩
    · obtain ⟨w, hw, hr⟩ := forall2_mem hs x hx
      exact ⟨w, by simp [hw], hr⟩

theorem forall2_imp {α β : Type} {R S : α → β → Prop} (hRS : ∀ x v, R x v → S x v) :
    ∀ {xs : List α} {vs : List β}, Forall2 R xs vs → Forall2 S xs vs
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (hRS _ _ h) (forall2_imp hRS hs)

theorem forall2_and_mem {α β : Type} {R : α → β → Prop} {P : β → Prop} :
    ∀ {xs : List α} {vs : List β}, Forall2 R xs vs → (∀ v ∈ vs, P v) →
      Forall2 (fun x v => R x v ∧ P v) xs vs
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons h hs, hp =>
    .cons ⟨h, hp _ (by simp)⟩ (forall2_and_mem hs (fun v hv => hp v (by simp [hv])))

/-! ## Strings -/

theorem strsAt_forall2 {σ : Jimple.State} : ∀ {ys : List Jimple.Value} {ss : List JStr},
    StrsAt σ ys ss → Forall2 (EquivLean.Cobol.Rec.JStrAt σ) ys ss
  | [], [], _ => .nil
  | [], _ :: _, h => by simp [StrsAt] at h
  | _ :: _, [], h => by simp [StrsAt] at h
  | y :: ys, s :: ss, h => by
    simp only [StrsAt, List.map_cons, List.cons.injEq] at h
    refine .cons ?_ (strsAt_forall2 h.2)
    cases y with
    | ref x =>
      simp only [strOf] at h
      cases hx : σ.heap x with
      | none => rw [hx] at h; cases h.1
      | some o =>
        rw [hx] at h
        cases o <;> simp at h
        exact ⟨x, rfl, by rw [hx, h.1]⟩
    | _ => simp [strOf] at h

theorem cp037Str_length (bs : List UInt8) : (cp037Str bs).length = bs.length := by
  simp [cp037Str]

/-- A string field holding the CP037 text of `bs` shows that text, cut or padded to its length. -/
theorem fixStr_argText {σ : Jimple.State} {x : Addr} {bs : List UInt8}
    (hx : σ.heap x = some (.str (cp037Str bs))) :
    fixStr (argText σ (.ref x)) bs.length = cp037Str bs := by
  have e : argText σ (.ref x) = cp037Str bs := by simp [argText, strOf, hx]
  rw [e]
  exact fixStr_eq_self (cp037Str_length bs)

/-! ## Numbers -/

theorem zpadStr_eq (n c : Nat) : zpadStr c n = (zpad n c).map (BitVec.ofNat 16) := by
  induction n generalizing c with
  | zero => rfl
  | succ m ih =>
    rw [zpadStr, ih, zpad, zpad, toDigits_succ]
    simp [digitChar]

theorem toInt_ofInt64 {v : Int} (h0 : 0 ≤ v) (h1 : v < 2 ^ 63) : (BitVec.ofInt 64 v).toInt = v := by
  rw [BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le] <;> omega

/-- A `long` field holding `0 ≤ v < 2 ^ 63` shows `v`'s digits. -/
theorem zpadStr_ofInt64 {v : Int} (d : Nat) (h0 : 0 ≤ v) (h1 : v < 2 ^ 63) :
    zpadStr (BitVec.ofInt 64 v).toNat d = (zpad d v.natAbs).map (BitVec.ofNat 16) := by
  have e : v.toNat = v.natAbs := by omega
  rw [ofInt64_toNat h0 h1, zpadStr_eq, e]

end EquivLean.Modernize.JLBridge
