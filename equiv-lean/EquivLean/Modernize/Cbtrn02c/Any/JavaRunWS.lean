import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWR

/-!
# CBTRN02C → Java: `W` after `postTransaction` fills `tranWs`

Only `tranWs` changes; it keeps all its fields and its `FILLER` of spaces.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem W_setT {σ σ' : State} {A : Addrs} {s : Model.St} (hW : W σ A s)
    (hf : FrameS σ σ' [A.wT])
    (hT' : WSObj σ' A.wT "Cbtrn02c$TranRecord" (keysOf TranRecord "Cbtrn02c$TranRecord"))
    (hFT' : WSFill σ' A.wT "Cbtrn02c$TranRecord" (Model.sp 20)) :
    W σ' A s := by
  obtain ⟨hR, hD, hT, hRj, hCW, hAR, hCR, hA, hC, hK, hwX, hwA, hwC, hwT, hfC, hfT, hnd⟩ := hW
  obtain ⟨fsT, hto, -⟩ := hwT
  have hS : NoStr σ [A.wT] := noStr_plain (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact ⟨_, _, hto⟩)
  have hN : NoRec σ A.ws [A.wT] := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    left
    subst ha
    simp [Addrs.ws]
  have nl : ∀ {l : Addr} {xs m}, σ.heap l = some (.list .arrayList xs m) → l ∉ [A.wT] := by
    intro l xs m hl hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    rw [hto] at hl; cases hl
  have lr : ∀ {l s cls ws vals}, LRec σ l s cls ws vals → l ∉ [A.wT] := by
    intro l s cls ws vals h
    obtain ⟨xs, m, hl, -⟩ := h
    exact nl hl
  have ls : ∀ {l strs}, LStr σ l strs → l ∉ [A.wT] := by
    intro l strs h
    obtain ⟨xs, m, hl, -⟩ := h
    exact nl hl
  have pl : ∀ {w c fs}, σ.heap w = some (.plain c fs) → c ≠ "Cbtrn02c$TranRecord" →
      w ∉ [A.wT] := by
    intro w c fs hw h1 hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    exact ne_of_plain_cls hw hto h1 rfl
  refine ⟨hR.frame hf (by obtain ⟨fs, h, -⟩ := hR; exact pl h (by decide)),
    hD.frame hf hS (ls hD), hT.frame hf hS hN (lr hT), hRj.frame hf hS hN (lr hRj),
    hCW.frame hf hS hN (lr hCW), hAR.frame hf hS hN (lr hAR), hCR.frame hf hS hN (lr hCR),
    hA.frame hf hS hN ?_, hC.frame hf hS hN (lr hC), hK.frame hf hS (ls hK),
    hwX.frame hf (by obtain ⟨fs, h, -⟩ := hwX; exact pl h (by decide)),
    hwA.frame hf (by obtain ⟨fs, h, -⟩ := hwA; exact pl h (by decide)),
    hwC.frame hf (by obtain ⟨fs, h, -⟩ := hwC; exact pl h (by decide)), hT',
    hfC.frame hf hS (by obtain ⟨fs, sv, h, -⟩ := hfC; exact pl h (by decide)), hFT', hnd⟩
  obtain ⟨et, xs, hl, -⟩ := hA
  intro hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rw [hm, hto] at hl; cases hl

end EquivLean.Modernize.Cbtrn02c.Java
