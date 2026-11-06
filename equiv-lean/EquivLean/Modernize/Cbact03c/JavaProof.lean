import EquivLean.Modernize.Cbact03c.JavaStatement

/-!
# CBACT03C → Java: from the contract of `run` to the generated statement

The proof has three parts:
* the COBOL side: coblean's `cbact03c_lists` (the DISPLAY lines are the start message, the records
  in file order, the end message), for the records built from the field values;
* the Java side: the contract `runSpec` of `Cbact03c.run` (the `displays` list holds the start
  line, each record's line, the end line; `abended` is 0), stated with the field texts the
  translation builds (`recLine`: an alphanumeric field's text, a numeric field's zero-padded
  digits);
* the glue: a record's line is the CP037 text of its bytes (`recLine_eq`: `text_unsigned` for the
  `PIC 9(n)` fields), and the start and end lines are the CP037 texts of coblean's messages.

`statement_of_sat`: the contract implies the generated `Statement`.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbact03c.Java

/-- The text a field value shows: an alphanumeric field's CP037 text, a numeric field's value
zero-padded to the field's length. -/
def fieldText (f : Field) : EquivLean.Cobol.Rec.FVal → JStr
  | .str bs => cp037Str bs
  | .num v => (zpad f.desc.len v.natAbs).map (BitVec.ofNat 16)

/-- A record's line: its fields' texts, in order. -/
def recLine (vals : List EquivLean.Cobol.Rec.FVal) : JStr :=
  ((CardXrefRecord.fields.zip vals).map fun p => fieldText p.1 p.2).flatten

def startLine : JStr := cp037Str CardDemo.Cbact03c.startMsg
def endLine : JStr := cp037Str CardDemo.Cbact03c.endMsg

/-- The contract of `Cbact03c.run` (partial correctness). -/
def runSpec : Spec := Spec.of
  (fun args σ => ∃ a vals, args = [.ref a] ∧ XreffileFileAt σ a vals ∧
     (∀ v ∈ vals, CardXrefRecord.Valid v) ∧ σ.initOf "Cbact03c" = .done ∧
     σ.initOf "Cbact03c$Result" = .done ∧ σ.initOf "Cbact03c$CardXrefRecord" = .done ∧
     σ.initOf "Cbact03c$State" = .done)
  (fun args σ r σ' => ∀ a vals, args = [.ref a] → XreffileFileAt σ a vals →
     (∀ v ∈ vals, CardXrefRecord.Valid v) →
     ∃ res fs l k xs mods, r = some (.ref res) ∧
       σ'.heap res = some (.plain "Cbact03c$Result" fs) ∧
       Fields.get fs ("Cbact03c$Result", "displays") = some (.ref l) ∧
       σ'.heap l = some (.list k xs mods) ∧
       Forall2 (JStrAt σ') xs (startLine :: vals.flatMap (fun v => [recLine v, recLine v]) ++ [endLine]) ∧
       Fields.get fs ("Cbact03c$Result", "abended") = some (.int 0))

/-! ## Glue: a record's line is the CP037 text of its bytes -/

theorem cp037Str_eq_map (bs : List UInt8) :
    cp037Str bs = (bs.map cp037Code).map (BitVec.ofNat 16) := by
  simp [cp037Str, cp037Unit, cp037Code, List.map_map, Function.comp_def]

/-- The fields of `CARD-RECORD`: every numeric one is an unsigned DISPLAY item (`PIC 9(n)`). -/
def UnsignedDisplay (f : Field) : Prop :=
  ∀ fmt, f.desc.kind = .num fmt → fmt.usage = .display ∧ fmt.signed = false

instance (f : Field) : Decidable (UnsignedDisplay f) := by
  unfold UnsignedDisplay
  cases h : f.desc.kind with
  | num fmt =>
    exact decidable_of_iff (fmt.usage = .display ∧ fmt.signed = false)
      ⟨fun h' g hg => by cases hg; exact h', fun h' => h' fmt rfl⟩
  | group => exact isTrue (fun _ h => by cases h)
  | alnum j => exact isTrue (fun _ h => by cases h)
  | numEdited p b => exact isTrue (fun _ h => by cases h)

theorem cardXrefRecord_unsigned : ∀ f ∈ CardXrefRecord.fields, UnsignedDisplay f := by decide

theorem fieldText_eq {f : Field} (hu : UnsignedDisplay f) {v : EquivLean.Cobol.Rec.FVal}
    (hv : f.Valid v) : fieldText f v = cp037Str (f.encode v) := by
  cases v with
  | num n =>
    obtain ⟨fmt, hk, hd, -, -, hl⟩ := hv
    obtain ⟨hdisp, hs⟩ := hu fmt hk
    have hbl : fmt.byteLen {} = fmt.digits := by
      unfold NumFmt.byteLen; rw [hdisp]; simp [hs]
    simp only [fieldText, Field.encode, hk]
    rw [cp037Str_eq_map, text_unsigned hdisp hs hd, ← hl, hbl]
  | str bs => rfl

theorem recLine_flatten : ∀ {fs : List Field} {vals : List EquivLean.Cobol.Rec.FVal},
    (∀ f ∈ fs, UnsignedDisplay f) → Forall2 Field.Valid fs vals →
      ((fs.zip vals).map fun p => fieldText p.1 p.2).flatten =
        cp037Str ((fs.zip vals).flatMap fun p => p.1.encode p.2)
  | [], [], _, .nil => rfl
  | f :: fs, v :: vals, hu, .cons h hs => by
    simp only [List.zip_cons_cons, List.map_cons, List.flatten_cons, List.flatMap_cons]
    rw [fieldText_eq (hu f (List.mem_cons_self ..)) h,
      recLine_flatten (fun g hg => hu g (List.mem_cons_of_mem _ hg)) hs]
    simp [cp037Str]

/-- **A record's line is the CP037 text of the record's bytes.** -/
theorem recLine_eq {vals : List EquivLean.Cobol.Rec.FVal} (hv : CardXrefRecord.Valid vals) :
    recLine vals = cp037Str (CardXrefRecord.encode vals) :=
  recLine_flatten cardXrefRecord_unsigned hv

/-! ## The statement from the contract -/

theorem forall2_of_map {α β γ : Type} {R : α → γ → Prop} {f : β → γ} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs (ys.map f) → Forall2 (fun x y => R x (f y)) xs ys
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: _, _ :: _, .cons h hs => .cons h (forall2_of_map hs)

theorem displays_eq : CardDemo.Cbact03c.displays = EquivLean.Cobol.Rec.displays := rfl

/-- **The contract of `run` implies the generated statement.** -/
theorem statement_of_sat (hrun : Sat Gen.prog runRef runSpec) : Statement := by
  intro vals1 hv _hjb n hn σ a1 hin hi1 hi2 hi3 hi4
  have hm : initMem.size = 123 := by rw [initMem_size, CardDemo.Cbact03c.memSize_eq]
  have hlen : ∀ r ∈ vals1.map CardXrefRecord.encode, r.length = 50 := by
    intro r hr
    obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hr
    exact Schema.length_encode cardXrefRecord_contig (hv v hv')
  obtain ⟨hstop, hdisp⟩ := CardDemo.Cbact03c.cbact03c_lists initMem hm
    (vals1.map CardXrefRecord.encode) n hlen (by simpa using hn)
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbact03c.run {} (n + 20)
      (CardDemo.Cbact03c.initState initMem [(1, vals1.map CardXrefRecord.encode)])) := by
    rw [EquivLean.Cobol.Ok, hstop]; rfl
  rw [EquivLean.Cobol.run]
  refine sim_of_sat ((EquivLean.Cobol.safe_exec_iff _).2 hok)
    ((EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩) hrun
    ⟨a1, vals1, rfl, hin, hv, hi1, hi2, hi3, hi4⟩ ?_
  intro o ho
  cases o with
  | normal r σ' =>
    obtain ⟨res, fs, l, k, xs, mods, hr, hres, hl, hlist, hpairs, hab⟩ := ho a1 vals1 rfl hin hv
    refine ⟨σ', res, fs, l, k, xs, mods, by rw [hr], hres, hl, hlist, ?_, ?_⟩
    · rw [← displays_eq, hdisp]
      have e : startLine :: vals1.flatMap (fun v => [recLine v, recLine v]) ++ [endLine] =
          ([CardDemo.Cbact03c.startMsg] ++ (vals1.map CardXrefRecord.encode).flatMap (fun r => [r, r]) ++
            [CardDemo.Cbact03c.endMsg]).map cp037Str := by
        simp only [List.map_append, List.map_cons, List.map_nil, startLine, endLine,
          List.cons_append, List.nil_append, List.cons.injEq, List.append_cancel_right_eq, true_and,
          List.flatMap_map, List.map_flatMap]
        exact flatMap_congr_mem fun v hv' => by simp [recLine_eq (hv v hv')]
      rw [e] at hpairs
      exact forall2_of_map (R := JStrAt σ') (f := cp037Str) hpairs
    · rw [hab, hstop]
      rfl
  | exc e σ' => simp [runSpec, Spec.of] at ho
  | wrong msg => simp [runSpec, Spec.of] at ho

end EquivLean.Modernize.Cbact03c.Java
