import Cobol
open Cobol

/-! M-editpoint and M-editlead: the editing of the theorem pictures is the same before and after
the fixes (`scripts/lean1.sh tests/EditPoint.lean`).

`OldEdit.editOpt` and `OldEdit.edit` are `Edit.editOpt` and `Edit.edit` of snapshot
coblean-20261028T0551Z, copied verbatim (its `Cobol/Edit.lean` lines 132-194 and 202-205); they
differ from the fixed ones only in the condition for an insertion character (`j ≤ k0 ∧ j < i`).
`editOpt_eq`: the two agree on every configuration, `BLANK WHEN ZERO`, value and scale for every
picture with no insertion character right before the decimal point after all of its (one or more)
integer digit positions (M-editpoint) and, when it has integer digit positions, none before the
first of them (M-editlead; the conditions can differ there only); the four pictures of the theorem
IRs are such pictures (`minus_all`, `plus_all`, `z_all`, `nine_all`). -/

namespace Cobol.OldEdit
open Cobol.Edit

def editOpt (c : Config) (pic : List ESym) (bwz : Bool) (v s : Int) : Option (List UInt8) := do
  let ps ← classify pic
  if !floatBeforePoint ps then none
  let n := numDigitPos ps
  let f := fracDigits ps
  let i := n - f
  let mag := (rescale .truncation v s f).natAbs % 10 ^ n
  let ds := Digits.toDigits 10 n mag
  let neg := decide (v < 0)
  let zero := mag = 0
  let allSupp := ps.all (fun p => p != .digit none)
  let suppKind : Option ESym :=
    ps.findSome? (fun p => match p with | .digit (some k) => some k | _ => none)
  if bwz && zero then return List.replicate (picWidth pic) c.space
  if zero && allSupp then
    -- all positions suppressed
    if suppKind == some .star then
      -- the whole item, fixed insertion symbols included, except the decimal point
      return (ps.flatMap (fun p => match p with
        | .point => [c.chr 0x2E] | .implied => [] | .fixed k => List.replicate (width k) (c.chr 0x2A)
        | _ => [c.chr 0x2A]))
    else return List.replicate (picWidth pic) c.space
  -- index of the first significant digit
  let firstNine := (ps.filter (fun p => match p with | .digit _ => true | _ => false)).findIdx?
    (· == .digit none)
  let firstNZ := ds.findIdx? (· != 0)
  let k0 := min i (min (firstNine.getD n) (firstNZ.getD n))
  -- produce (byte, isSuppressedFloatPosition), consuming digits left to right
  let rec gen (j : Nat) : List Pos → List (UInt8 × Bool)
    | [] => []
    | p :: rest =>
      match p with
      | .digit k =>
        let b : UInt8 × Bool :=
          if j < k0 then
            match k with
            | some .star => (c.chr 0x2A, false)
            | some .z => (c.space, false)
            | _ => (c.space, true)
          else (c.digitByte (ds.getD j 0), false)
        b :: gen (j + 1) rest
      | .floatHead => (c.space, true) :: gen j rest
      | .insert sym =>
        let b : UInt8 × Bool :=
          if j ≤ k0 ∧ j < i then
            match suppKind with
            | some .star => (c.chr 0x2A, false)
            | some .z => (c.space, false)
            | some _ => (c.space, true)
            | none => (symChar c sym, false)
          else (symChar c sym, false)
        b :: gen j rest
      | .point => (symChar c .dot, false) :: gen j rest
      | .implied => gen j rest
      | .fixed sym => (fixedBytes c sym neg).map (·, false) ++ gen j rest
  let out := gen 0 ps
  match floatSym pic with
  | none => return out.map (·.1)
  | some fsym =>
    -- the floating symbol replaces the last suppressed floating position
    let lastIdx := (out.zipIdx.filter (fun (x, _) => x.2)).getLast?.map (·.2)
    let symB := if fsym == .cs then c.chr 0x24 else signChar c fsym neg
    return out.zipIdx.map (fun (x, idx) => if some idx == lastIdx then symB else x.1)

def edit (c : Config) (pic : List ESym) (bwz : Bool) (v s : Int) : Option (List UInt8) :=
  match pic with
  | .chars d m cs :: rest => (editOpt c rest bwz v s).map (List.map (mapChar c d m cs))
  | _ => editOpt c pic bwz v s

end Cobol.OldEdit

namespace EditPoint

/-- `unchanged i j ps`: no insertion position of `ps` (with `j` digit positions before it) is right
before the decimal point (`.` or `V`) after all `i > 0` integer digit positions, and, when `i > 0`,
none has no digit position before it. Elsewhere the old and the fixed conditions agree. -/
def unchanged (i : Nat) : Nat → List Edit.Pos → Bool
  | _, [] => true
  | j, p :: rest =>
    match p with
    | .insert _ =>
      !(j == i && 0 < i && rest.any (fun p => p == .point || p == .implied)) && (0 < j || i == 0) &&
        unchanged i j rest
    | .digit _ => unchanged i (j + 1) rest
    | _ => unchanged i j rest

theorem gen_eq (c : Config) (i : Nat) (ds : List Nat) (neg : Bool) (sk : Option ESym) (k0 : Nat) :
    ∀ (ps : List Edit.Pos) (j : Nat), unchanged i j ps = true →
      Edit.editOpt.gen c i ds neg sk k0 j ps = OldEdit.editOpt.gen c i ds neg sk k0 j ps
  | [], _, _ => by simp only [Edit.editOpt.gen, OldEdit.editOpt.gen]
  | p :: rest, j, h => by
    cases p with
    | digit k =>
      simp only [unchanged] at h
      simp only [Edit.editOpt.gen, OldEdit.editOpt.gen, gen_eq c i ds neg sk k0 rest (j + 1) h]
      all_goals rfl
    | floatHead =>
      simp only [unchanged] at h
      simp only [Edit.editOpt.gen, OldEdit.editOpt.gen, gen_eq c i ds neg sk k0 rest j h]
    | insert sym =>
      simp only [unchanged, Bool.and_eq_true] at h
      obtain ⟨⟨h1, h3⟩, h2⟩ := h
      have h1' : ¬ (j = i ∧ 0 < i ∧ rest.any (fun p => p == .point || p == .implied) = true) := by
        rintro ⟨rfl, e2, e3⟩
        simp [e2, e3] at h1
      simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h3
      have hiff : (j ≤ k0 ∧ (0 < j ∨ ([some .cs, some .plus, some .minus].contains sk = true ∧
            rest.all (· != .floatHead) = true)) ∧
          (j < i ∨ (j = i ∧ 0 < i ∧ rest.any (fun p => p == .point || p == .implied) = true))) ↔
          (j ≤ k0 ∧ j < i) := by
        constructor
        · rintro ⟨hk, _, hp | hp⟩
          · exact ⟨hk, hp⟩
          · exact absurd hp h1'
        · rintro ⟨hk, hji⟩
          refine ⟨hk, ?_, Or.inl hji⟩
          rcases h3 with h3 | h3
          · exact Or.inl h3
          · omega
      simp only [Edit.editOpt.gen, OldEdit.editOpt.gen, gen_eq c i ds neg sk k0 rest j h2]
      by_cases hc : j ≤ k0 ∧ j < i
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (hiff.mpr hc)), ite_eq_left_of_eq_true _ _ (eq_true hc)]
        all_goals rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hc (hiff.mp h))),
          ite_eq_right_of_eq_false _ _ (eq_false hc)]
    | point =>
      simp only [unchanged] at h
      simp only [Edit.editOpt.gen, OldEdit.editOpt.gen, gen_eq c i ds neg sk k0 rest j h]
    | implied =>
      simp only [unchanged] at h
      simp only [Edit.editOpt.gen, OldEdit.editOpt.gen, gen_eq c i ds neg sk k0 rest j h]
    | fixed sym =>
      simp only [unchanged] at h
      simp only [Edit.editOpt.gen, OldEdit.editOpt.gen, gen_eq c i ds neg sk k0 rest j h]

/-- Old and new editing agree on every configuration, `BLANK WHEN ZERO`, value and scale for a
picture without the changed cases. -/
theorem editOpt_eq (c : Config) (pic : List ESym) (bwz : Bool) (v s : Int)
    (h : ((Edit.classify pic).map (fun ps =>
      unchanged (Edit.numDigitPos ps - Edit.fracDigits ps) 0 ps)).getD true = true) :
    Edit.editOpt c pic bwz v s = OldEdit.editOpt c pic bwz v s := by
  unfold Edit.editOpt OldEdit.editOpt
  cases hc : Edit.classify pic with
  | none => rfl
  | some ps =>
    have hu : unchanged (Edit.numDigitPos ps - Edit.fracDigits ps) 0 ps = true := by
      simpa [hc] using h
    simp only [Option.bind_eq_bind, Option.bind_some, gen_eq _ _ _ _ _ _ ps 0 hu]
    all_goals rfl

/-- The numeric-edited pictures of the theorem IRs (examples/carddemo/*.ir.json): CBTRN03C's
`-ZZZ,ZZZ,ZZZ.ZZ` and `+ZZZ,ZZZ,ZZZ.ZZ`, CBSTM03A's `Z(9).99-` and `9(9).99-`. -/
def minusPic : List ESym := [.minus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z]
def plusPic : List ESym := [.plus, .z, .z, .z, .comma, .z, .z, .z, .comma, .z, .z, .z, .dot, .z, .z]
def zPic : List ESym := [.z, .z, .z, .z, .z, .z, .z, .z, .z, .dot, .nine, .nine, .minus]
def ninePic : List ESym := [.nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine, .nine, .dot, .nine, .nine, .minus]

theorem minus_all (c : Config) (bwz : Bool) (v s : Int) :
    Edit.edit c minusPic bwz v s = OldEdit.edit c minusPic bwz v s :=
  editOpt_eq c minusPic bwz v s (by decide)

theorem plus_all (c : Config) (bwz : Bool) (v s : Int) :
    Edit.edit c plusPic bwz v s = OldEdit.edit c plusPic bwz v s :=
  editOpt_eq c plusPic bwz v s (by decide)

theorem z_all (c : Config) (bwz : Bool) (v s : Int) :
    Edit.edit c zPic bwz v s = OldEdit.edit c zPic bwz v s :=
  editOpt_eq c zPic bwz v s (by decide)

theorem nine_all (c : Config) (bwz : Bool) (v s : Int) :
    Edit.edit c ninePic bwz v s = OldEdit.edit c ninePic bwz v s :=
  editOpt_eq c ninePic bwz v s (by decide)

/-- The changed cases are excluded: `PIC $$,.99` and `PIC 0ZZ.99` do not satisfy the hypothesis. -/
example : ((Edit.classify [.cs, .cs, .comma, .dot, .nine, .nine]).map (fun ps =>
    unchanged (Edit.numDigitPos ps - Edit.fracDigits ps) 0 ps)).getD true = false := by decide

example : ((Edit.classify [.zero, .z, .z, .dot, .nine, .nine]).map (fun ps =>
    unchanged (Edit.numDigitPos ps - Edit.fracDigits ps) 0 ps)).getD true = false := by decide

def thmPics : List (String × List ESym) :=
  [("-ZZZ,ZZZ,ZZZ.ZZ", minusPic), ("+ZZZ,ZZZ,ZZZ.ZZ", plusPic), ("Z(9).99-", zPic), ("9(9).99-", ninePic)]

/-- Direct comparison of old and new editing on every value of `vs` at scales 0 to 4, with and
without `BLANK WHEN ZERO`, in both configurations: (comparisons, disagreements). -/
def compare (pic : List ESym) (vs : List Int) : Nat × Nat := Id.run do
  let mut n := 0
  let mut bad := 0
  for c in [({} : Config), Config.gnucobol] do
    for bwz in [false, true] do
      for s in [0, 1, 2, 3, 4] do
        for v in vs do
          n := n + 1
          if Edit.edit c pic bwz v s != OldEdit.edit c pic bwz v s then bad := bad + 1
  return (n, bad)

/-- Every value from -20000 to 20000, and 4001 values spread over ±2·10^13 (past the 11 digit
positions, so high-order truncation too). -/
def values : List Int :=
  (List.range 40001).map (fun (k : Nat) => (k : Int) - 20000) ++
    (List.range 4001).map (fun (k : Nat) => ((k : Int) - 2000) * 9999999967)

#eval thmPics.map (fun (nm, p) => (nm, compare p values))

/-! The fixed cases (IBM's results): an insertion character right before the decimal point,
after a suppression or floating string with no 9, with a zero integer part. -/

theorem cs_comma_zero :
    Edit.edit Config.gnucobol [.cs, .cs, .comma, .dot, .nine, .nine] false 0 2 =
      some (Config.gnucobol.encodeAscii "  $.00") := by
  decide +kernel

theorem star_comma :
    Edit.edit Config.gnucobol [.star, .star, .comma, .dot, .nine, .nine] false 86 2 =
      some (Config.gnucobol.encodeAscii "***.86") := by
  decide +kernel

theorem z_slash_implied :
    Edit.edit Config.gnucobol [.z, .z, .slash, .v, .nine, .nine] false 5 2 =
      some (Config.gnucobol.encodeAscii "   05") := by
  decide +kernel

/-! M-editlead fixed: an insertion character left of the string is written; one inside a floating
string, after its first symbol, is still part of it. -/

theorem zero_lead :
    Edit.edit Config.gnucobol [.zero, .z, .z, .dot, .nine, .nine] false 550 2 =
      some (Config.gnucobol.encodeAscii "0 5.50") := by
  decide +kernel

theorem zero_lead_cs :
    Edit.edit Config.gnucobol [.zero, .cs, .cs, .dot, .nine, .nine] false 550 2 =
      some (Config.gnucobol.encodeAscii "0$5.50") := by
  decide +kernel

theorem comma_after_head :
    Edit.edit Config.gnucobol [.cs, .comma, .cs, .cs, .dot, .nine, .nine] false 5 2 =
      some (Config.gnucobol.encodeAscii "   $.05") := by
  decide +kernel

/-- De-editing follows: IBM's content de-edits to 0 (it was `invalidData` before the fix). -/
theorem cs_comma_zero_deedit :
    (match Sem.deEdit Config.gnucobol [.cs, .cs, .comma, .dot, .nine, .nine] false
        (Config.gnucobol.encodeAscii "  $.00") with
      | .ok (0, 2) => true
      | _ => false) = true := by
  decide +kernel

end EditPoint

#print axioms EditPoint.gen_eq
#print axioms EditPoint.editOpt_eq
#print axioms EditPoint.minus_all
#print axioms EditPoint.plus_all
#print axioms EditPoint.z_all
#print axioms EditPoint.nine_all
#print axioms EditPoint.cs_comma_zero
#print axioms EditPoint.star_comma
#print axioms EditPoint.z_slash_implied
#print axioms EditPoint.zero_lead
#print axioms EditPoint.zero_lead_cs
#print axioms EditPoint.comma_after_head
#print axioms EditPoint.cs_comma_zero_deedit
