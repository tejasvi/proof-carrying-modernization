import EquivLean.Modernize.Cbtrn02c.Any.JavaRunS3
import EquivLean.Modernize.Cbtrn02c.Any.JavaSpec

/-!
# CBTRN02C → Java: the heap determines the inputs

`runIn_det`: two readings of the same arguments and heap as `run`'s inputs (`Any.Java.RunIn`) have
the same records and clock: a numeric field's `long` and a text field's string determine the field
value (every numeric field of the four record layouts is DISPLAY, not full binary).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The field is not a full-binary numeric field. -/
def noBinB (f : Field) : Bool :=
  match f.desc.kind with
  | .num fmt => !fmt.fullBinary {}
  | _ => true

/-- No numeric field of the layout is full binary. -/
def NoBin (s : Schema) : Prop := ∀ f ∈ s.fields, noBinB f = true

instance (s : Schema) : Decidable (NoBin s) := by unfold NoBin; exact inferInstance

theorem jFieldAt_det {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)} {f : Field}
    {v v' : EquivLean.Cobol.Rec.FVal}
    (hnb : noBinB f = true)
    (h : jFieldAt σ cls fs f v) (h' : jFieldAt σ cls fs f v') (hv : f.Valid v) (hv' : f.Valid v') :
    v = v' := by
  cases v with
  | num n =>
    cases v' with
    | num n' =>
      obtain ⟨fmt, hk, -, hd, hh, -⟩ := hv
      obtain ⟨fmt', hk', -, hd', hh', -⟩ := hv'
      rw [hk] at hk'
      cases hk'
      simp only [noBinB, hk, Bool.not_eq_true'] at hnb
      simp only [jFieldAt] at h h'
      rw [h] at h'
      simp only [Option.some.injEq, Value.long.injEq] at h'
      unfold Cobol.NumFmt.Holds at hh hh'
      simp only [hnb, Bool.false_eq_true, ↓reduceIte] at hh hh'
      have h18 : (10 : Nat) ^ fmt.digits ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) hd
      have e := ofInt_inj (by omega) (by omega) h'
      rw [e]
    | str bs' =>
      obtain ⟨fmt, hk, -⟩ := hv
      obtain ⟨⟨j, hj⟩, -⟩ := hv'
      rw [hk] at hj
      cases hj
  | str bs =>
    cases v' with
    | num n' =>
      obtain ⟨⟨j, hj⟩, -⟩ := hv
      obtain ⟨fmt, hk, -⟩ := hv'
      rw [hk] at hj
      cases hj
    | str bs' =>
      obtain ⟨s, hs, x, rfl, hx⟩ := h
      obtain ⟨s', hs', x', rfl, hx'⟩ := h'
      rw [hs] at hs'
      simp only [Option.some.injEq, Value.ref.injEq] at hs'
      subst hs'
      rw [hx] at hx'
      simp only [Option.some.injEq, Obj.str.injEq] at hx'
      rw [cp037Str_inj hx']

theorem jfields_det {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)} :
    ∀ {fields : List Field} {xs xs' : List EquivLean.Cobol.Rec.FVal},
      (∀ f ∈ fields, noBinB f = true) →
      Forall2 (fun f val => jFieldAt σ cls fs f val) fields xs →
      Forall2 (fun f val => jFieldAt σ cls fs f val) fields xs' →
      Forall2 Field.Valid fields xs → Forall2 Field.Valid fields xs' → xs = xs'
  | _, _, _, _, .nil, .nil, _, _ => rfl
  | f :: fields, _, _, hnb, .cons h hs, .cons h' hs', .cons hv hvs, .cons hv' hvs' => by
    rw [jFieldAt_det (hnb f List.mem_cons_self) h h' hv hv',
      jfields_det (fun g hg => hnb g (List.mem_cons_of_mem _ hg)) hs hs' hvs hvs']

theorem jrecAt_det {s : Schema} {cls : ClassName} {σ : State} {v : Value} {x x' : List EquivLean.Cobol.Rec.FVal}
    (hnb : NoBin s) (h : JRecAt s cls σ v x) (h' : JRecAt s cls σ v x') (hv : s.Valid x)
    (hv' : s.Valid x') : x = x' := by
  obtain ⟨a, fs, rfl, ha, hf⟩ := h
  obtain ⟨a', fs', ha'e, ha', hf'⟩ := h'
  cases ha'e
  rw [ha] at ha'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at ha'
  subst ha'
  exact jfields_det hnb hf hf' hv hv'

theorem forall2_jrec_det {s : Schema} {cls : ClassName} {σ : State} (hnb : NoBin s) :
    ∀ {xs : List Value} {vals vals' : List (List EquivLean.Cobol.Rec.FVal)},
      Forall2 (JRecAt s cls σ) xs vals → Forall2 (JRecAt s cls σ) xs vals' →
      (∀ v ∈ vals, s.Valid v) → (∀ v ∈ vals', s.Valid v) → vals = vals'
  | _, _, _, .nil, .nil, _, _ => rfl
  | _, x :: vals, x' :: vals', .cons h hs, .cons h' hs', hv, hv' => by
    rw [jrecAt_det hnb h h' (hv x List.mem_cons_self) (hv' x' List.mem_cons_self),
      forall2_jrec_det hnb hs hs' (fun v hm => hv v (List.mem_cons_of_mem _ hm))
        (fun v hm => hv' v (List.mem_cons_of_mem _ hm))]

theorem file_det {s : Schema} {cls : ClassName} {σ : State} {a : Addr}
    {vals vals' : List (List EquivLean.Cobol.Rec.FVal)} (hnb : NoBin s)
    (h : ∃ et xs, σ.heap a = some (.array et xs) ∧ xs.length < 2147483648 ∧
      Forall2 (JRecAt s cls σ) xs vals)
    (h' : ∃ et xs, σ.heap a = some (.array et xs) ∧ xs.length < 2147483648 ∧
      Forall2 (JRecAt s cls σ) xs vals')
    (hv : ∀ v ∈ vals, s.Valid v) (hv' : ∀ v ∈ vals', s.Valid v) : vals = vals' := by
  obtain ⟨et, xs, ha, -, hf⟩ := h
  obtain ⟨et', xs', ha', -, hf'⟩ := h'
  rw [ha] at ha'
  simp only [Option.some.injEq, Obj.array.injEq] at ha'
  obtain ⟨-, rfl⟩ := ha'
  exact forall2_jrec_det hnb hf hf' hv hv'

theorem noBin_dal : NoBin DalytranRecord := by decide
theorem noBin_xref : NoBin CardXrefRecord := by decide
theorem noBin_acct : NoBin AccountRecord := by decide
theorem noBin_tcat : NoBin TranCatBalRecord := by decide

/-- **The heap determines `run`'s inputs.** -/
theorem runIn_det {args : List Value} {σ : State}
    {v1 v2 v3 v4 v1' v2' v3' v4' : List (List EquivLean.Cobol.Rec.FVal)} {clk clk' : List UInt8}
    (h : Any.Java.RunIn args σ v1 v2 v3 v4 clk) (h' : Any.Java.RunIn args σ v1' v2' v3' v4' clk') :
    v1 = v1' ∧ v2 = v2' ∧ v3 = v3' ∧ v4 = v4' ∧ clk = clk' := by
  obtain ⟨a1, a2, a3, a4, cs, hargs, h1, h2, h3, h4, hc, -, hv1, hv2, hv3, hv4, -⟩ := h
  obtain ⟨a1', a2', a3', a4', cs', hargs', h1', h2', h3', h4', hc', -, hv1', hv2', hv3', hv4', -⟩ := h'
  rw [hargs] at hargs'
  simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs'
  refine ⟨file_det noBin_dal h1 h1' hv1 hv1', file_det noBin_xref h2 h2' hv2 hv2',
    file_det noBin_acct h3 h3' hv3 hv3', file_det noBin_tcat h4 h4' hv4 hv4', ?_⟩
  obtain ⟨x, hx, hxs⟩ := hc
  obtain ⟨x', hx', hxs'⟩ := hc'
  rw [hx] at hx'
  simp only [Value.ref.injEq] at hx'
  subst hx'
  rw [hxs] at hxs'
  simp only [Option.some.injEq, Obj.str.injEq] at hxs'
  exact cp037Str_inj hxs'

end EquivLean.Modernize.Cbtrn02c.Java
