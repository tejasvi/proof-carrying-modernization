import EquivLean.Modernize.Cbtrn03c.JavaTop.CalEbc
import EquivLean.Modernize.Cbtrn03c.JavaTop.RunW

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `compareEbcdic` on the model's `cmpB`

`compareEbcdicSpecT` does not hold as stated: for a character outside Latin-1 (code point ≥ 256)
`ebcdic` returns `0x6F` (the character is not in the constant CP037), while the model's `ebc` (of
`ebcBytes`) gives 0 (`cp037Byte` is `none` there).  On `"Ā"` and `"?"` (equal lengths)
`compareEbcdic` returns 0 (`ebcdic` gives `0x6F` for both), the postcondition asks for -1
(`cmpB [0] [0x6F] = .lt`): `cmpFrom_counterexample`.

`compareEbcdicSpecL`: the contract with Latin-1 strings (every character below 256, as the
CP037 texts `cp037Str bs` of the callers: `forall_mem_cp037Str_lt`), the same postcondition.
For a Latin-1 character `ebcdic` is the model's `ebc` (`ebcFrom_lt256`, CP037 is a bijection of
`0 ..= 255`), and the loop's tests are `cmpB`'s (`cmpFrom_drop`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

set_option maxRecDepth 100000 in
theorem ebcFrom_lt256_fin : ∀ n : Fin 256,
    ebcFrom (BitVec.ofNat 16 n) 0 = ((Model.ebc n).toNat : Int) := by
  decide +kernel

/-- `ebcdic` of a Latin-1 character is the model's `ebc`. -/
theorem ebcFrom_lt256 (u : JChar) (h : u.toNat < 256) :
    ebcFrom u 0 = ((Model.ebc u.toNat).toNat : Int) := by
  have e := ebcFrom_lt256_fin ⟨u.toNat, h⟩
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at e
  exact e

theorem ofNat32_toInt_u8 (p : UInt8) : (BitVec.ofNat 32 p.toNat).toInt = (p.toNat : Int) := by
  have hp : p.toNat < 256 := by have := p.toNat_lt; simp at this; omega
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  have h1 : p.toNat % 2 ^ 32 = p.toNat := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  split <;> omega

theorem ebcV_lt256 (u : JChar) (h : u.toNat < 256) :
    ebcV u = BitVec.ofNat 32 (Model.ebc u.toNat).toNat := by
  unfold ebcV
  rw [ebcFrom_lt256 u h]
  rfl

theorem ebcBytes_cons (u : JChar) (s : JStr) :
    ebcBytes (u :: s) = Model.ebc u.toNat :: ebcBytes s := rfl

theorem cmpB_cons (p q : UInt8) (ps qs : List UInt8) :
    Model.cmpB (p :: ps) (q :: qs) =
      if p < q then .lt else if q < p then .gt else Model.cmpB ps qs := rfl

/-- The loop's tests on Latin-1 strings of equal length are `cmpB`'s on their EBCDIC bytes. -/
theorem cmpFrom_drop (a b : JStr) (hl : a.length = b.length) (ha : ∀ u ∈ a, u.toNat < 256)
    (hb : ∀ u ∈ b, u.toNat < 256) (i : Nat) :
    cmpFrom a b i = ordI (Model.cmpB (ebcBytes (a.drop i)) (ebcBytes (b.drop i))) := by
  rw [cmpFrom]
  by_cases h : i < a.length
  · have hb' : i < b.length := hl ▸ h
    rw [if_pos h, List.drop_eq_getElem_cons h, List.drop_eq_getElem_cons hb', ebcBytes_cons,
      ebcBytes_cons, cmpB_cons, cmpFrom_drop a b hl ha hb (i + 1)]
    have hai := ha _ (List.getElem_mem h)
    have hbi := hb _ (List.getElem_mem hb')
    have ga : a.getD i 0 = a[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
    have gb : b.getD i 0 = b[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb', Option.getD_some]
    rw [ga, gb, ebcV_lt256 _ hai, ebcV_lt256 _ hbi, ofNat32_toInt_u8, ofNat32_toInt_u8]
    generalize Model.ebc a[i].toNat = p
    generalize Model.ebc b[i].toNat = q
    have hp : p.toNat < 256 := by have := p.toNat_lt; simp at this; omega
    have hq : q.toNat < 256 := by have := q.toNat_lt; simp at this; omega
    by_cases hpq : p = q
    · subst hpq
      simp
    · have hne : BitVec.ofNat 32 p.toNat ≠ BitVec.ofNat 32 q.toNat := by
        intro e
        apply hpq
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        exact UInt8.toNat_inj.mp (by omega)
      have hne' : p.toNat ≠ q.toNat := fun e => hpq (UInt8.toNat_inj.mp e)
      rw [if_neg hne]
      by_cases hlt : p < q
      · have hlt' : p.toNat < q.toNat := UInt8.lt_iff_toNat_lt.mp hlt
        rw [if_neg (by omega), if_pos hlt]
        rfl
      · have hgt : q < p := by
          rw [UInt8.lt_iff_toNat_lt] at hlt ⊢
          omega
        have hgt' : q.toNat < p.toNat := UInt8.lt_iff_toNat_lt.mp hgt
        rw [if_pos (by omega), if_neg hlt, if_pos hgt]
        rfl
  · rw [if_neg h, List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
    rfl
termination_by a.length - i
decreasing_by omega

/-! ## The counterexample to `compareEbcdicSpecT` -/

set_option maxRecDepth 100000 in
theorem ebcFrom_256 : ebcFrom (BitVec.ofNat 16 256) 0 = 111 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ebcFrom_63 : ebcFrom (BitVec.ofNat 16 63) 0 = 111 := by decide +kernel

/-- `compareEbcdic("Ā", "?")` returns 0 (the proved `compareEbcdic_sat`: `cmpFrom`), where
`compareEbcdicSpecT` asks for -1. -/
theorem cmpFrom_counterexample :
    cmpFrom [BitVec.ofNat 16 256] [BitVec.ofNat 16 63] 0 = 0 ∧
    ordI (Model.cmpB (ebcBytes [BitVec.ofNat 16 256]) (ebcBytes [BitVec.ofNat 16 63])) = -1 := by
  constructor
  · rw [cmpFrom_eq (by decide) (by simp [ebcV, ebcFrom_256, ebcFrom_63]), cmpFrom_ge (by decide)]
  · decide +kernel

/-! ## The contract with Latin-1 strings -/

/-- The characters of a CP037 text are Latin-1. -/
theorem forall_mem_cp037Str_lt (bs : List UInt8) : ∀ u ∈ cp037Str bs, u.toNat < 256 := by
  intro u hu
  simp only [cp037Str, List.mem_map] at hu
  obtain ⟨b, -, rfl⟩ := hu
  have := cp037Code_lt b
  simp only [cp037Unit, BitVec.toNat_ofNat]
  simp only [cp037Code] at this
  omega

/-- The same, as a rewrite rule (for `jvc` at a call). -/
theorem forall_mem_cp037Str_lt_iff (bs : List UInt8) :
    (∀ u ∈ cp037Str bs, u.toNat < 256) ↔ True :=
  iff_true_intro (forall_mem_cp037Str_lt bs)

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

/-- **`compareEbcdicSpecT` for Latin-1 strings** (the corrected contract: `compareEbcdicSpecT`'s
precondition with `∀ u ∈ sa, u.toNat < 256` and the same for `sb`; the same postcondition). -/
def compareEbcdicSpecL : Spec := Spec.of
  (fun args σ => ∃ (xa xb : Addr) (sa sb : JStr), args = [.ref xa, .ref xb] ∧
     σ.heap xa = some (.str sa) ∧ σ.heap xb = some (.str sb) ∧ sa.length = sb.length ∧
     sa.length < 2147483648 ∧ (∀ u ∈ sa, u.toNat < 256) ∧ (∀ u ∈ sb, u.toNat < 256) ∧
     σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ (xa xb : Addr), args = [.ref xa, .ref xb] →
     r = some (.int (ordI (Model.cmpB (ebcBytes (argText σ (.ref xa)))
       (ebcBytes (argText σ (.ref xb)))))) ∧
     σ.next ≤ σ'.next ∧ Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

theorem Cal.compareEbcdicL_sat : Sat Gen.prog Cal.compareEbcdicRef compareEbcdicSpecL := by
  intro args σ o hp hx
  obtain ⟨xa, xb, sa, sb, rfl, ha, hb, hl, hlen, hla, hlb, hi⟩ := hp
  have ho := Cal.compareEbcdic_sat _ σ o ⟨xa, xb, sa, sb, rfl, ha, hb, hl, hlen, hi⟩ hx
  cases o with
  | normal r σ' =>
    intro xa' xb' heq
    obtain ⟨hr, h1, h2, h3, h4⟩ := ho xa' xb' heq
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    refine ⟨?_, h1, h2, h3, h4⟩
    rw [hr]
    simp only [argText, strOf, ha, hb, Option.getD_some]
    rw [Cal.cmpFrom_drop sa sb hl hla hlb 0]
    rfl
  | exc e σ' => exact ho
  | wrong m => exact ho

set_option maxHeartbeats 0 in
theorem compareEbcdicL_ok : ContractOK Gen.prog compareEbcdicSig compareEbcdicSpecL := by
  jcontract_ok [Cal.compareEbcdicL_sat]

theorem Cal.compareEbcdicC_sat : Sat Gen.prog Cal.compareEbcdicRef compareEbcdicSpecC := by
  intro args σ o hp hx
  obtain ⟨xa, xb, ba, bb, rfl, ha, hb, hl, hlen, hi⟩ := hp
  exact Cal.compareEbcdicL_sat _ σ o ⟨xa, xb, cp037Str ba, cp037Str bb, rfl, ha, hb,
    by rw [cp037Str_length, cp037Str_length, hl], by rw [cp037Str_length]; exact hlen,
    Cal.forall_mem_cp037Str_lt ba, Cal.forall_mem_cp037Str_lt bb, hi⟩ hx

set_option maxHeartbeats 0 in
theorem compareEbcdicC_ok : ContractOK Gen.prog compareEbcdicSig compareEbcdicSpecC := by
  jcontract_ok [Cal.compareEbcdicC_sat]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.cmpFrom_counterexample
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.forall_mem_cp037Str_lt_iff
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.compareEbcdicL_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.compareEbcdicC_ok
