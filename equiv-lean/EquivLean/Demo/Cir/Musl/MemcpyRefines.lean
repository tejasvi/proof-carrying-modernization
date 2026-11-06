import EquivLean.Demo.Cir.Musl.Memcpy

/-!
# musl `memcpy` refines cirlean's `memcpy` model where its word paths do not run

`musl_memcpy_refines` covers copying `n` characters from a `char` array into a `char` array in
another block. Suppose cirlean's `memcpy` model returns `r`, and:
- musl's word paths do not run (`WordFree`);
- every source character is a `char` value (`-128 .. 255`);
- if the destination is `signed char`, every source character is in `0 .. 127`.

Then musl's `memcpy`, if it returns, returns the model's value, and the caller's blocks are as
the model leaves them.

Each excluded input is a model-vs-implementation difference, stated as its own theorem:
- the word paths, `musl_memcpy_ne_model` (`MemcpyCex`). This is cirlean's lack of byte-level
  memory, not a musl bug: GCC defines musl's word accesses through `__may_alias__`; up to 28e2380
  cirlean read or wrote one element there, and under punning2 they are undefined behaviour in
  cirlean, so musl has no outcome there and the refinement covers the byte paths only;
- a byte ≥ 0x80 copied into a `signed char` destination, `memcpy_diff_signed`;
- an indeterminate source character, `memcpy_diff_indeterminate`;
- overlapping ranges, `memcpy_diff_overlap`. Here the two blocks differ.

The bounds and the writable destination are conditions of the model itself: for `n > 0`, the
model is undefined without them.
-/

open CIR EquivLean.Cir

set_option maxHeartbeats 4000000

namespace EquivLean.Demo.Cir.Musl

/-- The model's conversion of a copied value to the destination's character type. -/
def mval (sd : Bool) : Val → Val
  | .int x => .int (wrap sd 8 x)
  | v => v

/-- cirlean's `memcpy` model on `n > 0` characters between two `char` arrays: the `n` source
values, converted to the destination's type, replace `n` destination elements. -/
theorem memcpy_model_ok (ctx' : Ctx) (bs bd is id n ls ld : Nat) (ss sd : Bool) (ks kd : BlockKind)
    (ys zs : List Val) (m : Mem)
    (hs : m.blocks bs = some ⟨ks, true, .array (.int ss 8) ls, .arr ys⟩)
    (hd : m.blocks bd = some ⟨kd, true, .array (.int sd 8) ld, .arr zs⟩) (hkd : kd ≠ .readonly)
    (hsd : bs ≠ bd) (hn : 0 < n) (hns : is + n ≤ ys.length) (hnd : id + n ≤ zs.length) :
    Std.runModel ctx' .memcpy [.ptr (.loc bd [.idx id]), .ptr (.loc bs [.idx is]), .int n] m =
      .ok (.ret (some (.ptr (.loc bd [.idx id]))),
        m.setBlock bd ⟨kd, true, .array (.int sd 8) ld,
          .arr (zs.take id ++ ((ys.drop is).take n).map (mval sd) ++ zs.drop (id + n))⟩) := by
  have h' : Std.runModel ctx' .memcpy [.ptr (.loc bd [.idx id]), .ptr (.loc bs [.idx is]), .int n] m =
      Std.memcpyModel ctx' m (.loc bd [.idx id]) (.loc bs [.idx is]) n := runModel_memcpy_of_ne ctx' m bd bs [.idx id] [.idx is] n hsd
  rw [h']
  have hn0 : n ≠ 0 := by omega
  have hmin : min n (ys.length - is) = n := by omega
  simp [Std.memcpyModel, Std.typedRange?, splitLast, Ctx.typeAt, Ctx.sizeAlign, Mem.read?, Mem.live?, hs, hd,
    Val.get?, Std.rangeVals, Std.rangeWrite, Mem.write?, Val.set?, hkd, Std.retv, hn0, hns, hnd, hmin]
  rfl

/-- cirlean's `memcpy` model with `n = 0` returns `d` and changes nothing. -/
theorem memcpy_model_zero (ctx' : Ctx) (d s : Ptr) (m : Mem)
    (hd : Std.validMemArg m true d = true) (hs : Std.validMemArg m false s = true) :
    Std.runModel ctx' .memcpy [.ptr d, .ptr s, .int ((0 : Nat) : Int)] m = .ok (.ret (some (.ptr d)), m) := by
  change (if Std.memcpyOverlap ctx' m d s ((0 : Nat) : Int) then _ else _) = _
  simp [Std.memcpyOverlap, Std.memcpyModel, Std.retv, hd, hs]

theorem wrap_s8_eq_u8 (x : Int) (h1 : 0 ≤ x) (h2 : x ≤ 127) : wrap true 8 x = wrap false 8 x := by
  rw [wrap_of_bounds (by decide) (by simp only [intMin_s8, intMax_s8]; omega),
    wrap_of_bounds (by decide) (by simp only [intMin_u, intMax_u8]; omega)]

/-- musl's copied bytes are the model's values when each source character converts to the same
value in the destination's type as in `unsigned char`. -/
theorem cpy_eq_model (ysf : Nat → Int) (ys : List Val) (is n : Nat) (sd : Bool)
    (hns : is + n ≤ ys.length)
    (hys : ∀ j, is ≤ j → j < is + n → ys[j]? = some (.int (ysf j)))
    (hsd : ∀ j, is ≤ j → j < is + n → wrap sd 8 (ysf j) = wysf ysf j) :
    cpy (wysf ysf) is n = ((ys.drop is).take n).map (mval sd) := by
  apply List.ext_getElem
  · simp [cpy_length]; omega
  · intro j h1 h2
    rw [cpy_length] at h1
    simp only [cpy, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    have hy := hys (is + j) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega)] at hy
    rw [Option.some.inj hy, mval, hsd (is + j) (by omega) (by omega)]

/-- **musl `memcpy` refines cirlean's `memcpy` model** off its word paths. The arguments are
`n` characters from element `is` of the `char` array `bs` to element `id` of the `char` array
`bd`, in another block. Assume the model returns `r`, musl's word paths do not run, every source
character is a `char` value, and for a `signed char` destination every source character is in
`0 .. 127`. Then musl's `memcpy`, if it returns, returns the model's value, and the caller's
blocks are as the model leaves them. -/
theorem musl_memcpy_refines (ctx' : Ctx) (bs bd is id n ls ld : Nat) (ss sd : Bool) (ks kd : BlockKind)
    (ys zs : List Val) (m : Mem) (r : Exit × Mem)
    (hs : m.blocks bs = some ⟨ks, true, .array (.int ss 8) ls, .arr ys⟩)
    (hd : m.blocks bd = some ⟨kd, true, .array (.int sd 8) ld, .arr zs⟩) (hkd : kd ≠ .readonly)
    (hbs : bs < m.next) (hbd : bd < m.next) (hsd : bs ≠ bd)
    (hns : is + n ≤ ys.length) (hnd : id + n ≤ zs.length)
    (hlens : ys.length < 2 ^ 62) (hlend : zs.length < 2 ^ 62)
    (hmodel : Std.runModel ctx' .memcpy [.ptr (.loc bd [.idx id]), .ptr (.loc bs [.idx is]), .int n] m = .ok r)
    (hchar : ∀ j, is ≤ j → j < is + n → ∃ c : Int, ys[j]? = some (.int c) ∧ -128 ≤ c ∧ c ≤ 255 ∧
      (sd = true → 0 ≤ c ∧ c ≤ 127))
    (hfree : WordFree is id n) :
    pholds (evalCall Gen.Memcpy.ctx "musl_memcpy" [.ptr (.loc bd [.idx id]), .ptr (.loc bs [.idx is]), .int n] m)
      (fun r' => r'.1 = r.1 ∧ (∀ b', b' < m.next → r'.2.blocks b' = r.2.blocks b') ∧ m.next ≤ r'.2.next) := by
  -- the characters as integers
  let ysf : Nat → Int := fun j => match ys[j]? with | some (.int c) => c | _ => 0
  have hys : ∀ j, is ≤ j → j < is + n → ys[j]? = some (.int (ysf j)) := fun j h1 h2 => by
    obtain ⟨c, hc, -⟩ := hchar j h1 h2; simp only [ysf, hc]
  have hyr : ∀ j, is ≤ j → j < is + n → -128 ≤ ysf j ∧ ysf j ≤ 255 := fun j h1 h2 => by
    obtain ⟨c, hc, h3, h4, -⟩ := hchar j h1 h2; simp only [ysf, hc]; exact ⟨h3, h4⟩
  have hp := musl_memcpy_pspec ysf ys zs bs bd is id n ks kd _ _ m hs hd ⟨ss, ls, rfl⟩ ⟨sd, ld, rfl⟩ hkd hbs hbd hsd
    hns hnd hlend hlens hys
    hyr hfree
  intro r' hr'
  obtain ⟨h1, h2, h3, h4⟩ := hp r' hr'
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hvd : Std.validMemArg m true (.loc bd [.idx id]) = true := by
      simp [Std.validMemArg, Mem.live?, hd, hkd]
    have hvs : Std.validMemArg m false (.loc bs [.idx is]) = true := by
      simp [Std.validMemArg, Mem.live?, hs]
    rw [memcpy_model_zero ctx' _ _ m hvd hvs] at hmodel
    obtain rfl := Res.ok.inj hmodel
    refine ⟨h1, fun b' hb' => ?_, h4⟩
    by_cases hb : b' = bd
    · subst hb; rw [h2, hd]; simp [copyList, cpy]
    · exact h3 b' hb' hb
  · rw [memcpy_model_ok ctx' bs bd is id n ls ld ss sd ks kd ys zs m hs hd hkd hsd hn hns hnd] at hmodel
    obtain rfl := Res.ok.inj hmodel
    refine ⟨h1, fun b' hb' => ?_, h4⟩
    by_cases hb : b' = bd
    · subst hb
      have hsd' : ∀ j, is ≤ j → j < is + n → wrap sd 8 (ysf j) = wysf ysf j := fun j h1 h2 => by
        obtain ⟨c, hc, -, -, h5⟩ := hchar j h1 h2
        cases sd
        · rfl
        · obtain ⟨h6, h7⟩ := h5 rfl
          simp only [ysf, hc, wysf]
          exact wrap_s8_eq_u8 c h6 h7
      rw [h2, copyList, cpy_length, cpy_eq_model ysf ys is n sd hns hys hsd']
      simp only [Mem.setBlock, upd_apply_same]
    · rw [h3 b' hb' hb]
      simp only [Mem.setBlock, upd_apply_ne hb]

/-- The counterexample's input (`n = 7`, both pointers at index 0) takes a word path; one byte
fewer does not. -/
example : ¬ WordFree 0 0 7 ∧ WordFree 0 0 6 := by
  unfold WordFree hcount; decide

end EquivLean.Demo.Cir.Musl
