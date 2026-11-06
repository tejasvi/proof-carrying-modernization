import EquivLean.Modernize.Cbtrn02c.Any.JavaRunMS
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWAb
import EquivLean.Modernize.Cbtrn02c.Glue

/-!
# CBTRN02C → Java: the model keeps its records valid (`MV`) through a posting

`MV_postCat`, `MV_postAcc`, `MV_postTr`, `MV_dupSt`, `MV_reject`: validity of the account and
category records and the length of the category `FILLER` after each update of a posting.
-/

open EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem mem_replaceFirst {α : Type} {p : α → Bool} {x b : α} :
    ∀ {l : List α}, b ∈ Model.replaceFirst p x l → b ∈ l ∨ b = x
  | [], h => by simp [Model.replaceFirst] at h
  | y :: ys, h => by
    simp only [Model.replaceFirst] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inr rfl
      · exact .inl (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inl List.mem_cons_self
      · rcases mem_replaceFirst h with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h

theorem MV_postAcc {s : Model.St} {t a : List FVal} (hMV : MV s) (hav : AccountRecord.Valid a) :
    MV (postAcc s t a) := by
  obtain ⟨h1, h2, h3⟩ := hMV
  refine ⟨?_, h2, h3⟩
  intro b hb
  rcases mem_replaceFirst hb with hb | rfl
  · exact h1 b hb
  · exact Glue.postAcct_valid hav _

theorem MV_postCat {s : Model.St} {t x : List FVal} (hMV : MV s) (htv : DalytranRecord.Valid t)
    (hxv : CardXrefRecord.Valid x) : MV (postCat s t x) := by
  obtain ⟨h1, h2, h3⟩ := hMV
  obtain ⟨-, htyl, hcatb, hcat0, -, -, hamtb, -⟩ := Glue.tranOf_valid htv
  obtain ⟨-, -, hxab, hxa0, -⟩ := Glue.xrefOf_valid hxv
  unfold postCat
  split
  · refine ⟨h1, ?_, h3⟩
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact h2 c hc
    · simp only [List.mem_singleton] at hc
      subst hc
      exact Glue.newCat_valid hxab hxa0 htyl hcatb hcat0 hamtb h3
  · rename_i c hfc
    have hcm : c ∈ s.cats := List.mem_of_find?_eq_some hfc
    have hcv := h2 c hcm
    refine ⟨h1, ?_, ?_⟩
    · intro c' hc'
      rcases mem_replaceFirst hc' with hc' | rfl
      · exact h2 _ hc'
      · exact (Glue.tcatOf_setBal hcv _).2 (CardDemo.Cbtrn02c.fitNum_catBal _)
    · obtain ⟨acct, ty, cd, bal, fill, rfl, -, -, -, -, -, -, hfill⟩ := Glue.tcat_shape hcv
      exact hfill

theorem MV_postTr {s : Model.St} {t : List FVal} {clk : List UInt8} (hMV : MV s) :
    MV (postTr s t clk) := hMV

theorem MV_dupSt {s : Model.St} {t x a : List FVal} (hMV : MV s) (htv : DalytranRecord.Valid t)
    (hxv : CardXrefRecord.Valid x) (hav : AccountRecord.Valid a) : MV (dupSt s t x a) :=
  MV_postAcc (MV_postCat hMV htv hxv) hav

theorem MV_reject {s : Model.St} {t : List FVal} {code : Int} {desc : List UInt8} (hMV : MV s) :
    MV (s.reject t code desc) := hMV

end EquivLean.Modernize.Cbtrn02c.Java
