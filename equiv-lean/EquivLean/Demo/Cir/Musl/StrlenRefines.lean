import EquivLean.Demo.Cir.Musl.Strlen

/-!
# musl `strlen` refines cirlean's `strlen` model

`musl_strlen_refines`: wherever cirlean's `strlen` model returns on a C string in an array
block, and every character it reads is a `char` value, musl's `strlen` (if it returns) returns
the model's result with the model's memory effect (none).

`musl_strlen_nonchar_ub` is the gap: the model's `readCStr` takes any `int` elements, musl
reads them with `char` loads, which are undefined in cirlean outside `-128..255`.

cirlean has no byte-level memory. Up to 28e2380 a `size_t` load at a `char` element read that
one element, so musl's word loop saw one character per "word". Under punning2 (cirlean `next`, where
this file is checked) musl's word path is undefined behaviour in cirlean: GCC defines the word loop's
`size_t` reads of a `char` array through `__may_alias__`, cirlean treats them as type-punned accesses.
A run that reaches the word loop has no outcome (`musl_strlen_aligned_ub`), so `musl_strlen_refines`
covers the byte path only: the runs that find the NUL in the alignment loop. The string must be a
`char` array (`hty`).
-/

open CIR EquivLean.Cir

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace EquivLean.Demo.Cir.Musl

open EquivLean.Demo.Cir.Musl.Gen.Strlen (ctx)

/-- The `strlen` model on a pointer into an array block: the string is the elements up to the
first NUL, all of them `int`s, and the model returns its length with the memory unchanged. -/
theorem strlen_model_ok {ctx' : Ctx} {b i : Nat} {kd : BlockKind} {ty : Ty} {xs : List Val} {m : Mem}
    {r : Exit × Mem} (hblk : m.blocks b = some ⟨kd, true, ty, .arr xs⟩)
    (h : Std.runModel ctx' .strlen [.ptr (.loc b [.idx i])] m = .ok r) :
    ∃ k, (xs.drop i).findIdx? Std.isNulVal = some k ∧ ((xs.drop i).take k).all Std.isIntVal = true ∧
      Std.readCStr m (.loc b [.idx i]) = .ok ((xs.drop i).take k) ∧
      r = (.ret (some (.int ((xs.drop i).take k).length)), m) := by
  have h' : (Std.readCStr m (.loc b [.idx i]) >>= fun cs => Std.retv (.int cs.length) m) = .ok r := h
  have hep : m.elemPos? (.loc b [.idx i]) = some (b, [], .idx i, xs.length) := by
    simp [Mem.elemPos?, splitLast, Mem.read?, Mem.live?, hblk, Val.get?]
  have hrd : m.read? (.loc b []) = some (.arr xs) := by simp [Mem.read?, Mem.live?, hblk, Val.get?]
  have hrc : Std.readCStr m (.loc b [.idx i]) =
      match (xs.drop i).findIdx? Std.isNulVal with
      | some k => if ((xs.drop i).take k).all Std.isIntVal then pure ((xs.drop i).take k)
          else .ub "indeterminate character in C string"
      | none => .ub "unterminated C string" := by
    (simp only [Std.readCStr, hep, Std.readVal, hrd, Res.ofOption, Res.ok_bind]) <;> rfl
  rw [hrc] at h'
  cases hk : List.findIdx? Std.isNulVal (List.drop i xs) with
  | none => simp [hk, bind, Res.bind] at h'
  | some k =>
    by_cases ha : (List.take k (List.drop i xs)).all Std.isIntVal = true
    · simp only [hk, ha, Res.ok_bind, ite_true, Std.retv, pure, Res.ok.injEq] at h'
      refine ⟨k, rfl, ha, ?_, h'.symm⟩
      rw [hrc]; simp only [hk, ha, ite_true]; rfl
    · simp only [hk, ha, Bool.false_eq_true, ite_false] at h'
      exact absurd h' (by simp [bind, Res.bind])

/-- **musl `strlen` refines cirlean's `strlen` model** on a C string at element `i` of an array
block `b`: if the model returns `r`, and every character it reads is a `char` value
(`-128 ≤ c ≤ 255`), then if musl's `strlen` returns, it returns the model's value, and the
caller's blocks are as the model leaves them (unchanged). -/
theorem musl_strlen_refines (ctx' : Ctx) (b i : Nat) (kd : BlockKind) (ty : Ty) (xs : List Val) (m : Mem)
    (r : Exit × Mem) (hblk : m.blocks b = some ⟨kd, true, ty, .arr xs⟩)
    (hty : ∃ es tlen, ty = .array (.int es 8) tlen) (hb : b < m.next) (hwf : m.WF)
    (hlen : xs.length < 2 ^ 62) (hmodel : Std.runModel ctx' .strlen [.ptr (.loc b [.idx i])] m = .ok r)
    (hchar : ∀ cs, Std.readCStr m (.loc b [.idx i]) = .ok cs →
      ∀ v ∈ cs, ∃ c : Int, v = .int c ∧ -128 ≤ c ∧ c ≤ 255) :
    pholds (evalCall ctx "musl_strlen" [.ptr (.loc b [.idx i])] m)
      (fun r' => r'.1 = r.1 ∧ (∀ b', b' < m.next → r'.2.blocks b' = r.2.blocks b') ∧ m.next ≤ r'.2.next) := by
  obtain ⟨k, hk, ha, hrc, hr⟩ := strlen_model_ok hblk hmodel
  obtain ⟨hkl, hnul, hbefore⟩ := List.findIdx?_eq_some_iff_getElem.1 hk
  have hkx : i + k < xs.length := by simp at hkl; omega
  have hall := List.all_eq_true.1 ha
  have hch := hchar _ hrc
  -- the characters as integers
  let csf : Nat → Int := fun j => match xs[j]? with | some (.int c) => c | _ => 0
  have hxe : xs[i + k]? = some (.int 0) := by
    rw [List.getElem_drop] at hnul
    rw [List.getElem?_eq_getElem hkx]
    revert hnul
    cases xs[i + k] <;> simp [Std.isNulVal]
  have hxj : ∀ j, i ≤ j → j < i + k → ∃ c : Int, xs[j]? = some (.int c) ∧ -128 ≤ c ∧ c ≤ 255 ∧ c ≠ 0 := by
    intro j hj1 hj2
    have hjl : j - i < (List.take k (List.drop i xs)).length := by simp; omega
    have hmem : (List.take k (List.drop i xs))[j - i] ∈ List.take k (List.drop i xs) := List.getElem_mem hjl
    have hv : (List.take k (List.drop i xs))[j - i] = xs[j] := by
      rw [List.getElem_take, List.getElem_drop]; congr 1; omega
    obtain ⟨c, hc, hc1, hc2⟩ := hch _ hmem
    have hnn := hbefore (j - i) (by omega)
    rw [hv] at hc
    rw [List.getElem_drop] at hnn
    have hji : i + (j - i) = j := by omega
    simp only [hji] at hnn
    refine ⟨c, ?_, hc1, hc2, ?_⟩
    · rw [List.getElem?_eq_getElem (by omega), hc]
    · intro h0; rw [hc, h0] at hnn; exact hnn (by simp [Std.isNulVal])
  have hp := musl_strlen_pspec xs csf b i (i + k) kd ty m hblk hty hb hwf (by omega) hkx hlen
    (fun j hj1 hj2 => by
      rcases Nat.lt_or_ge j (i + k) with h | h
      · obtain ⟨c, hc, -⟩ := hxj j hj1 h; simp only [csf, hc]
      · have : j = i + k := by omega
        subst this; simp only [csf, hxe])
    (fun j hj1 hj2 => by
      rcases Nat.lt_or_ge j (i + k) with h | h
      · obtain ⟨c, hc, hc1, hc2, -⟩ := hxj j hj1 h; simp only [csf, hc]; exact ⟨hc1, hc2⟩
      · have : j = i + k := by omega
        subst this; simp only [csf, hxe]; decide)
    (fun j hj1 hj2 => by
      obtain ⟨c, hc, -, -, hc0⟩ := hxj j hj1 hj2; simp only [csf, hc]; exact hc0)
    (by simp only [csf, hxe])
  intro r' hr'
  obtain ⟨h1, h2, h3⟩ := hp r' hr'
  subst hr
  refine ⟨?_, h2, h3⟩
  rw [h1]
  have hlk : (List.take k (List.drop i xs)).length = k := by simp; omega
  rw [hlk]
  congr 3
  omega

/-- **Finding (strlen):** cirlean's `readCStr` takes any `int` elements as characters, but musl's
`strlen` reads them with `char` loads, which cirlean makes undefined outside `-128..255`. So
where the model returns a length, musl can have undefined behaviour: here, a first element
outside the `char` range at an unaligned position (`(i + 1) % 8 ≠ 0`, cirlean's pointer
encoding), which musl's alignment loop reads with `*s`. (Elements that musl's word loop
passes, negative values without a zero byte as a 64-bit word, are not read as `char`s.) -/
theorem musl_strlen_nonchar_ub (xs : List Val) (b i : Nat) (kd : BlockKind) (ty : Ty) (m : Mem) (c : Int)
    (hblk : m.blocks b = some ⟨kd, true, ty, .arr xs⟩) (hty : ∃ es tlen, ty = .array (.int es 8) tlen)
    (hb : b < m.next) (hi : i < xs.length)
    (hx : xs[i]? = some (.int c)) (hc : c < -128 ∨ 255 < c) (_hal : (i + 1) % 8 ≠ 0) :
    pholds (evalCall ctx "musl_strlen" [.ptr (.loc b [.idx i])] m) (fun _ => False) := by
  obtain ⟨es, tlen, cirH_ty⟩ := hty
  intro r hr
  have hs := holds_of_eq_ok hr
  have cirH_blk := hblk
  have cirH_x : xs[i]? = some (.int c) := hx
  have cirH_xg : xs[i] = .int c := by rw [List.getElem?_eq_getElem hi] at hx; exact Option.some.inj hx
  have cirH_c := hc
  cir_hstep hs
  cir_hrun_c hs
  rw [evalFor_unfold] at hs
  cir_hrun_c hs
  rw [evalFor_unfold] at hs
  cir_hrun_c hs
  all_goals omega

/-- **Finding (strlen, cirlean `next`):** from an 8-aligned position of a `char` array, musl's `strlen`
leaves its alignment loop at once and reads `*w`, a `size_t` access to a `char` element, which punning2
makes undefined. So it has no outcome there, while the model returns the string's length. -/
theorem musl_strlen_aligned_ub (xs : List Val) (b i : Nat) (kd : BlockKind) (es : Bool) (tlen : Nat) (m : Mem)
    (hblk : m.blocks b = some ⟨kd, true, .array (.int es 8) tlen, .arr xs⟩) (hb : b < m.next)
    (hal : (if b + 1 < 2 ^ 29 ∧ i < 2 ^ 32 then i else i + 1) % 8 = 0) :
    pholds (evalCall ctx "musl_strlen" [.ptr (.loc b [.idx i])] m) (fun _ => False) := by
  intro r hr
  have hs := holds_of_eq_ok hr
  have cirH_blk := hblk
  have cirH_al : ((wrap false 64 (addrOfChar b i)).tmod 8 != 0) = false := by
    rw [tmod8_addrOfChar, bne_eq_false_iff_eq]; omega
  cir_hstep hs
  cir_hrun_c hs
  -- `for (; (uintptr_t)s % ALIGN; s++)`: `s` is aligned, the loop ends at once
  rw [evalFor_unfold] at hs
  cir_hrun_c hs
  -- `for (w = (const void *)s; !HASZERO(*w); w++)`: `*w` is a type-punned access
  rw [evalFor_unfold] at hs
  cir_hrun_c hs

end EquivLean.Demo.Cir.Musl
