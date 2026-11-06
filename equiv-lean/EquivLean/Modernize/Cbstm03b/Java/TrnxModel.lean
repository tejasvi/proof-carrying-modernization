import EquivLean.Modernize.Cbstm03b.Java.Base

/-! # CBSTM03B: the model's TRNXFILE call, case by case -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

variable {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}

set_option maxHeartbeats 400000

theorem callT_open41 (hd : Model.aDd a = ddTrnx) (ho : Model.aOp a = opOpen) (hb : s.trnx.isOpen = true) :
    Model.call oeM s a = ({ s with trnxSt := Model.stCp 41 }, Model.setRc a (stBytes 41)) := by
  simp only [Model.call, hd, ho, ↓reduceIte, Model.seqStep, Model.openM, hb]

theorem callT_openErr {c : Nat} (hd : Model.aDd a = ddTrnx) (ho : Model.aOp a = opOpen) (hb : s.trnx.isOpen = false)
    (he : oeM 1 = some c) :
    Model.call oeM s a = ({ s with trnxSt := Model.stCp c }, Model.setRc a (stBytes c)) := by
  simp only [Model.call, hd, ho, ↓reduceIte, Model.seqStep, Model.openM, hb, he, Bool.false_eq_true]

/-- A file just opened: at its first record, not at the end. -/
def openedF (f : Model.FileM) : Model.FileM := { f with isOpen := true, pos := 0, eof := false }

theorem callT_open00 (hd : Model.aDd a = ddTrnx) (ho : Model.aOp a = opOpen) (hb : s.trnx.isOpen = false)
    (he : oeM 1 = none) :
    Model.call oeM s a = ({ s with trnx := openedF s.trnx, trnxSt := Model.stCp 0 }, Model.setRc a (stBytes 0)) := by
  simp only [Model.call, hd, ho, ↓reduceIte, Model.seqStep, Model.openM, hb, he, Bool.false_eq_true, openedF]

theorem callT_read47 (hd : Model.aDd a = ddTrnx) (ho : Model.aOp a = opRead) (hb : s.trnx.isOpen = false) :
    Model.call oeM s a = ({ s with trnxSt := Model.stCp 47 }, Model.setRc a (stBytes 47)) := by
  simp only [Model.call, hd, ho, ↓reduceIte, Model.seqStep, Model.seqReadM, hb, opRead, opOpen, Bool.not_false]
  rfl

theorem callT_read46 (hd : Model.aDd a = ddTrnx) (ho : Model.aOp a = opRead) (hb : s.trnx.isOpen = true)
    (he : s.trnx.eof = true) :
    Model.call oeM s a = ({ s with trnxSt := Model.stCp 46 }, Model.setRc a (stBytes 46)) := by
  simp only [Model.call, hd, ho, ↓reduceIte, Model.seqStep, Model.seqReadM, hb, he, opRead, opOpen, Bool.not_true]
  rfl

/-- The file after reading its last record. -/
def atEofF (f : Model.FileM) : Model.FileM := { f with eof := true }

/-- The file after a record read. -/
def nextF (f : Model.FileM) : Model.FileM := { f with pos := f.pos + 1 }

theorem callT_read10 (hd : Model.aDd a = ddTrnx) (ho : Model.aOp a = opRead) (hb : s.trnx.isOpen = true)
    (he : s.trnx.eof = false) (hp : s.trnx.recs.length ≤ s.trnx.pos) :
    Model.call oeM s a = ({ s with trnx := atEofF s.trnx, trnxSt := Model.stCp 10 }, Model.setRc a (stBytes 10)) := by
  have h : s.trnx.recs[s.trnx.pos]? = none := List.getElem?_eq_none hp
  simp only [Model.call, hd, ho, ↓reduceIte, Model.seqStep, Model.seqReadM, hb, he, h, opRead, opOpen,
    Bool.not_true, atEofF]
  rfl

theorem callT_read00 {r : List EquivLean.Cobol.Rec.FVal} (hd : Model.aDd a = ddTrnx) (ho : Model.aOp a = opRead)
    (hb : s.trnx.isOpen = true) (he : s.trnx.eof = false) (hr : s.trnx.recs[s.trnx.pos]? = some r) :
    Model.call oeM s a = ({ s with trnx := nextF s.trnx, trnxRec := r, trnxSt := Model.stCp 0 },
      Model.setFldt (Model.setRc a (stBytes 0)) (Model.FdTrnxfileRec.encode r)) := by
  simp only [Model.call, hd, ho, ↓reduceIte, Model.seqStep, Model.seqReadM, hb, he, hr, opRead, opOpen,
    Bool.not_true, nextF]
  rfl

theorem callT_close42 (hd : Model.aDd a = ddTrnx) (ho : Model.aOp a = opClose) (hb : s.trnx.isOpen = false) :
    Model.call oeM s a = ({ s with trnxSt := Model.stCp 42 }, Model.setRc a (stBytes 42)) := by
  simp only [Model.call, hd, ho, ↓reduceIte, Model.seqStep, Model.closeM, hb, opClose, opRead, opOpen]
  rfl

/-- A closed file. -/
def closedF (f : Model.FileM) : Model.FileM := { f with isOpen := false }

theorem callT_close00 (hd : Model.aDd a = ddTrnx) (ho : Model.aOp a = opClose) (hb : s.trnx.isOpen = true) :
    Model.call oeM s a = ({ s with trnx := closedF s.trnx, trnxSt := Model.stCp 0 }, Model.setRc a (stBytes 0)) := by
  simp only [Model.call, hd, ho, ↓reduceIte, Model.seqStep, Model.closeM, hb, opClose, opRead, opOpen, closedF]
  rfl

theorem callT_other (hd : Model.aDd a = ddTrnx) (h1 : Model.aOp a ≠ opOpen) (h2 : Model.aOp a ≠ opRead)
    (h3 : Model.aOp a ≠ opClose) :
    Model.call oeM s a = (s, Model.setRc a (s.trnxSt.map ebcdicOfLatin1)) := by
  simp only [Model.call, hd, ↓reduceIte, Model.seqStep, h1, h2, h3]

end EquivLean.Modernize.Cbstm03b.Java
