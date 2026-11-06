import EquivLean.Modernize.Cbstm03b.Java.TrnxModel

/-! # CBSTM03B: the model's XREFFILE call, case by case -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

variable {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}

set_option maxHeartbeats 400000

theorem ddXref_ne_ddTrnx : ddXref ≠ ddTrnx := by decide

theorem callX_open41 (hd : Model.aDd a = ddXref) (ho : Model.aOp a = opOpen) (hb : s.xref.isOpen = true) :
    Model.call oeM s a = ({ s with xrefSt := Model.stCp 41 }, Model.setRc a (stBytes 41)) := by
  simp only [Model.call, hd, ddXref_ne_ddTrnx, ho, ↓reduceIte, Model.seqStep, Model.openM, hb]

theorem callX_openErr {c : Nat} (hd : Model.aDd a = ddXref) (ho : Model.aOp a = opOpen) (hb : s.xref.isOpen = false)
    (he : oeM 2 = some c) :
    Model.call oeM s a = ({ s with xrefSt := Model.stCp c }, Model.setRc a (stBytes c)) := by
  simp only [Model.call, hd, ddXref_ne_ddTrnx, ho, ↓reduceIte, Model.seqStep, Model.openM, hb, he,
    Bool.false_eq_true]

theorem callX_open00 (hd : Model.aDd a = ddXref) (ho : Model.aOp a = opOpen) (hb : s.xref.isOpen = false)
    (he : oeM 2 = none) :
    Model.call oeM s a = ({ s with xref := openedF s.xref, xrefSt := Model.stCp 0 }, Model.setRc a (stBytes 0)) := by
  simp only [Model.call, hd, ddXref_ne_ddTrnx, ho, ↓reduceIte, Model.seqStep, Model.openM, hb, he,
    Bool.false_eq_true, openedF]

theorem callX_read47 (hd : Model.aDd a = ddXref) (ho : Model.aOp a = opRead) (hb : s.xref.isOpen = false) :
    Model.call oeM s a = ({ s with xrefSt := Model.stCp 47 }, Model.setRc a (stBytes 47)) := by
  simp only [Model.call, hd, ddXref_ne_ddTrnx, ho, ↓reduceIte, Model.seqStep, Model.seqReadM, hb, opRead, opOpen,
    Bool.not_false]
  rfl

theorem callX_read46 (hd : Model.aDd a = ddXref) (ho : Model.aOp a = opRead) (hb : s.xref.isOpen = true)
    (he : s.xref.eof = true) :
    Model.call oeM s a = ({ s with xrefSt := Model.stCp 46 }, Model.setRc a (stBytes 46)) := by
  simp only [Model.call, hd, ddXref_ne_ddTrnx, ho, ↓reduceIte, Model.seqStep, Model.seqReadM, hb, he, opRead, opOpen,
    Bool.not_true]
  rfl

theorem callX_read10 (hd : Model.aDd a = ddXref) (ho : Model.aOp a = opRead) (hb : s.xref.isOpen = true)
    (he : s.xref.eof = false) (hp : s.xref.recs.length ≤ s.xref.pos) :
    Model.call oeM s a = ({ s with xref := atEofF s.xref, xrefSt := Model.stCp 10 }, Model.setRc a (stBytes 10)) := by
  have h : s.xref.recs[s.xref.pos]? = none := List.getElem?_eq_none hp
  simp only [Model.call, hd, ddXref_ne_ddTrnx, ho, ↓reduceIte, Model.seqStep, Model.seqReadM, hb, he, h, opRead,
    opOpen, Bool.not_true, atEofF]
  rfl

theorem callX_read00 {r : List EquivLean.Cobol.Rec.FVal} (hd : Model.aDd a = ddXref) (ho : Model.aOp a = opRead)
    (hb : s.xref.isOpen = true) (he : s.xref.eof = false) (hr : s.xref.recs[s.xref.pos]? = some r) :
    Model.call oeM s a = ({ s with xref := nextF s.xref, xrefRec := r, xrefSt := Model.stCp 0 },
      Model.setFldt (Model.setRc a (stBytes 0)) (Model.FdXreffileRec.encode r)) := by
  simp only [Model.call, hd, ddXref_ne_ddTrnx, ho, ↓reduceIte, Model.seqStep, Model.seqReadM, hb, he, hr, opRead,
    opOpen, Bool.not_true, nextF]
  rfl

theorem callX_close42 (hd : Model.aDd a = ddXref) (ho : Model.aOp a = opClose) (hb : s.xref.isOpen = false) :
    Model.call oeM s a = ({ s with xrefSt := Model.stCp 42 }, Model.setRc a (stBytes 42)) := by
  simp only [Model.call, hd, ddXref_ne_ddTrnx, ho, ↓reduceIte, Model.seqStep, Model.closeM, hb, opClose, opRead,
    opOpen]
  rfl

theorem callX_close00 (hd : Model.aDd a = ddXref) (ho : Model.aOp a = opClose) (hb : s.xref.isOpen = true) :
    Model.call oeM s a = ({ s with xref := closedF s.xref, xrefSt := Model.stCp 0 }, Model.setRc a (stBytes 0)) := by
  simp only [Model.call, hd, ddXref_ne_ddTrnx, ho, ↓reduceIte, Model.seqStep, Model.closeM, hb, opClose, opRead,
    opOpen, closedF]
  rfl

theorem callX_other (hd : Model.aDd a = ddXref) (h1 : Model.aOp a ≠ opOpen) (h2 : Model.aOp a ≠ opRead)
    (h3 : Model.aOp a ≠ opClose) :
    Model.call oeM s a = (s, Model.setRc a (s.xrefSt.map ebcdicOfLatin1)) := by
  simp only [Model.call, hd, ddXref_ne_ddTrnx, ↓reduceIte, Model.seqStep, h1, h2, h3]

end EquivLean.Modernize.Cbstm03b.Java
