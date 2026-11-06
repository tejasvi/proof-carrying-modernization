import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5b
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWC
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWA

/-!
# CBTRN02C → Java: the searches of `updateTcatbal` and `updateAccount` are the model's

`utIdx_eq`: `updateTcatbal`'s search over the category list is `Model.catKey`'s first index over
the model's category records; `firstIdx_neg_iff`: no index exactly when `find?` finds nothing.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem firstIdx_neg_iff {α : Type} {p : α → Bool} {l : List α} :
    firstIdx p l < 0 ↔ l.find? p = none := by
  unfold firstIdx
  constructor
  · intro h
    cases hf : l.findIdx? p with
    | none =>
      rw [List.findIdx?_eq_none_iff] at hf
      exact List.find?_eq_none.2 (fun x hx => by simp [hf x hx])
    | some j => rw [hf] at h; simp only at h; omega
  · intro h
    have hn : l.findIdx? p = none := by
      rw [List.findIdx?_eq_none_iff]
      intro x hx
      have := List.find?_eq_none.1 h x hx
      simpa using this
    rw [hn]
    decide

/-- `updateTcatbal`'s search is the model's. -/
theorem utIdx_eq {σ : State} {A : Addrs} {s : Model.St} {d : Addr}
    {t x : List EquivLean.Cobol.Rec.FVal}
    (hW : W σ A s) (hMV : MV s) (hd : JRecAt DalytranRecord dalCls σ (.ref d) t)
    (htv : DalytranRecord.Valid t) (hx : JRecAt CardXrefRecord xrCls σ (.ref A.wX) x)
    (hxv : CardXrefRecord.Valid x) :
    utIdx σ d A.wX A.lC =
      firstIdx (Model.catKey (Model.xAcct x) (Model.tType t) (Model.tCat t)) s.cats := by
  obtain ⟨-, -, -, -, -, -, -, -, hC, -⟩ := hW
  obtain ⟨xs, m, hlC, hfC0, -, -⟩ := hC
  obtain ⟨⟨a, fsd, s0, s1, s3, s4, s7, s8, s9, s10, s11, s12, s13, hae, hdo, -, -, g1, t1, g2, -,
    -, -, -, -, -⟩, b0, b1, n2, b3, b4, n5, n6, b7, b8, b9, b10, b11, b12, b13, rfl, h2, -, -⟩ :=
    dalobj_of_rec hd htv
  cases hae
  obtain ⟨⟨a', fsX, -, -, hxe, hxo, -, -, -, gx2, -⟩, xb0, xn1, xn2, xb3, rfl, -, hx2, -⟩ :=
    xobj_of_rec hx hxv
  cases hxe
  have e1 : lng σ A.wX xAcctKey = BitVec.ofInt 64 xn2 := by simp [lng, fld, fieldsOf, hxo, gx2, nAt, Model.numOf]
  have e2 : argText σ (fld σ d dTypeKey) = cp037Str b1 := by
    simp [argText, strOfV, fld, fieldsOf, hdo, g1, t1, bAt, Model.strOf]
  have e3 : lng σ d dCatKey = BitVec.ofInt 64 n2 := by simp [lng, fld, fieldsOf, hdo, g2, nAt, Model.numOf]
  unfold utIdx
  rw [e1, e2, e3, listOf_of hlC]
  exact tcat_first hfC0 hMV.2.1 xn2 n2 b1 hx2 h2

end EquivLean.Modernize.Cbtrn02c.Java
