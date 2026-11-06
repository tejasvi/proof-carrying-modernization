import EquivLean.Demo.Cir.Musl.MemcpyCex

/-!
# musl `memcpy` vs cirlean's `memcpy` model: three differences, each on a concrete input

Each theorem shows that musl's `memcpy` and cirlean's model have different outcomes. musl
copies byte by byte through `unsigned char` (on these inputs its word paths do not run).

* `memcpy_diff_signed`: a byte ≥ 0x80 into a `signed char` destination. musl stores the
  `unsigned char` value (200), while the model converts to the destination's type (-56). A later
  `char` load reads -56 from either (`loadTy` converts), but the memories differ.
* `memcpy_diff_indeterminate`: an indeterminate source byte. The model copies it, while musl's
  `unsigned char` load is undefined in cirlean.
* `memcpy_diff_overlap`: overlapping ranges in one array. musl copies forward, byte by byte,
  and re-reads what it wrote, while the model copies the original values. C makes overlapping
  `memcpy` undefined (`restrict`), so the model's missing overlap check is a gap in the model
  itself.
-/

open CIR EquivLean.Cir

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace EquivLean.Demo.Cir.Musl

open EquivLean.Demo.Cir.Musl.Gen.Memcpy (ctx)

/-! ### (i) The signedness of a copied byte ≥ 0x80 -/

/-- musl's `memcpy(d, s, 1)` from the `char` -56 (the byte 0xC8) into a `signed char` array: if it
returns, the destination holds 200. -/
theorem musl_memcpy_signed_run (bs bd : Nat) (ks kd : BlockKind) (m : Mem)
    (hs : m.blocks bs = some ⟨ks, true, .array (.int true 8) 1, .arr [.int (-56)]⟩)
    (hd : m.blocks bd = some ⟨kd, true, .array (.int true 8) 1, .arr [.int 0]⟩) (hkd : kd ≠ .readonly)
    (hbs : bs < m.next) (hbd : bd < m.next) (hsd : bs ≠ bd) :
    pholds (evalCall ctx "musl_memcpy" [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 1] m)
      (fun r => r.2.blocks bd = some ⟨kd, true, .array (.int true 8) 1, .arr [.int 200]⟩) := by
  intro r hr
  have hs0 := holds_of_eq_ok hr
  have cirH_bs := hs
  have cirH_bd := hd
  have cirH_sd : bs ≠ bd := hsd
  have cirH_m0 : (0 : Int) % 4 = 0 := by decide
  have cirH_m1 : (1 : Int) % 4 = 1 := by decide
  have cirH_m2 : (2 : Int) % 4 = 2 := by decide
  have cirH_n0 : ((0 : Int) != 0) = false := by decide
  have cirH_n1 : ((1 : Int) != 0) = true := by decide
  have cirH_n2 : ((2 : Int) != 0) = true := by decide
  have cirH_w : wrap false 8 (-56) = 200 := by decide
  have cirH_ir56 : inRange false 8 (-56) = false := by decide
  have cirH_irs56 : inRange true 8 (-56) = true := by decide
  have cirH_ir200 : inRange false 8 200 = true := by decide
  have cirH_b16_0 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 0 16 = 0 := by decide
  have cirH_b8_0 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 0 8 = 0 := by decide
  have cirH_b4_0 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 0 4 = 0 := by decide
  have cirH_b2_0 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 0 2 = 0 := by decide
  have cirH_b1_0 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 0 1 = 0 := by decide
  have cirH_b16_1 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 1 16 = 0 := by decide
  have cirH_b8_1 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 1 8 = 0 := by decide
  have cirH_b4_1 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 1 4 = 0 := by decide
  have cirH_b2_1 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 1 2 = 0 := by decide
  have cirH_b1_1 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 1 1 = 1 := by decide
  cir_hstep hs0
  cir_hrun_c hs0
  by_cases hbs29 : bs + 1 < 2 ^ 29
  · have cirH_p2s : (wrap false 64 (addrOfChar bs 0)).tmod 4 = 0 := tmod4_addrOfChar_flat hbs29 0
    rw [evalFor_unfold] at hs0
    cir_hrun_c hs0
    all_goals (try (rw [evalFor_unfold] at hs0; cir_hrun_c hs0))
    all_goals first
      | contradiction
      | omega
      | (subst hs0; simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same])
  · have cirH_p2s0 : (wrap false 64 (addrOfChar bs 0)).tmod 4 = 1 := tmod4_addrOfChar_other hbs29 0
    have cirH_p2s1 : (wrap false 64 (addrOfChar bs 1)).tmod 4 = 2 := tmod4_addrOfChar_other hbs29 1
    rw [evalFor_unfold] at hs0
    cir_hrun_c hs0
    rw [evalFor_unfold] at hs0
    cir_hrun_c hs0
    all_goals (try (rw [evalFor_unfold] at hs0; cir_hrun_c hs0))
    all_goals first
      | contradiction
      | omega
      | (subst hs0; simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same])

/-- **Difference (i), signedness:** copying the byte 0xC8 (the `char` -56) into a `signed char`
array, musl stores the `unsigned char` value 200, while cirlean's model stores -56 (it converts to
the destination's type). The memories differ. A later `char` load reads -56 from either. -/
theorem memcpy_diff_signed (ctx' : Ctx) (bs bd : Nat) (ks kd : BlockKind) (m : Mem)
    (hs : m.blocks bs = some ⟨ks, true, .array (.int true 8) 1, .arr [.int (-56)]⟩)
    (hd : m.blocks bd = some ⟨kd, true, .array (.int true 8) 1, .arr [.int 0]⟩) (hkd : kd ≠ .readonly)
    (hbs : bs < m.next) (hbd : bd < m.next) (hsd : bs ≠ bd) :
    evalCall ctx "musl_memcpy" [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 1] m ≠
      Std.runModel ctx' .memcpy [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 1] m := by
  have hmodel : Std.runModel ctx' .memcpy [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 1] m =
      .ok (.ret (some (.ptr (.loc bd [.idx 0]))),
        m.setBlock bd ⟨kd, true, .array (.int true 8) 1, .arr [.int (-56)]⟩) := by
    have h' : Std.runModel ctx' .memcpy [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 1] m =
        Std.memcpyModel ctx' m (.loc bd [.idx 0]) (.loc bs [.idx 0]) 1 := runModel_memcpy_of_ne ctx' m bd bs [.idx 0] [.idx 0] 1 hsd
    rw [h']
    simp [Std.memcpyModel, Std.typedRange?, splitLast, Ctx.typeAt, Ctx.sizeAlign, Mem.read?, Mem.live?, hs, hd,
      Val.get?, Std.rangeVals, Std.rangeWrite, Mem.write?, Val.set?, hkd, Std.retv, wrap]
  intro h
  rw [hmodel] at h
  have h2 := musl_memcpy_signed_run bs bd ks kd m hs hd hkd hbs hbd hsd _ h
  simp [Mem.setBlock, upd] at h2

/-! ### (ii) An indeterminate source byte -/

/-- musl's `memcpy(d, s, 1)` from an indeterminate byte never returns: its `unsigned char` load of
the indeterminate value is undefined in cirlean. -/
theorem musl_memcpy_undef_ub (bs bd : Nat) (ks kd : BlockKind) (m : Mem)
    (hs : m.blocks bs = some ⟨ks, true, .array (.int true 8) 1, .arr [.undef]⟩)
    (hd : m.blocks bd = some ⟨kd, true, .array (.int true 8) 1, .arr [.int 0]⟩) (_hkd : kd ≠ .readonly)
    (hbs : bs < m.next) (hbd : bd < m.next) (hsd : bs ≠ bd) :
    pholds (evalCall ctx "musl_memcpy" [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 1] m)
      (fun _ => False) := by
  intro r hr
  have hs0 := holds_of_eq_ok hr
  have cirH_bs := hs
  have cirH_bd := hd
  have cirH_sd : bs ≠ bd := hsd
  have cirH_m0 : (0 : Int) % 4 = 0 := by decide
  have cirH_m1 : (1 : Int) % 4 = 1 := by decide
  have cirH_n0 : ((0 : Int) != 0) = false := by decide
  have cirH_n1 : ((1 : Int) != 0) = true := by decide
  have cirH_b16 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 1 16 = 0 := by decide
  have cirH_b8 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 1 8 = 0 := by decide
  have cirH_b4 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 1 4 = 0 := by decide
  have cirH_b2 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 1 2 = 0 := by decide
  have cirH_b1 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 1 1 = 1 := by decide
  cir_hstep hs0
  cir_hrun_c hs0
  by_cases hbs29 : bs + 1 < 2 ^ 29
  · have cirH_p2s : (wrap false 64 (addrOfChar bs 0)).tmod 4 = 0 := tmod4_addrOfChar_flat hbs29 0
    rw [evalFor_unfold] at hs0
    cir_hrun_c hs0
    rw [evalFor_unfold] at hs0
    cir_hrun_c hs0
  · have cirH_p2s : (wrap false 64 (addrOfChar bs 0)).tmod 4 = 1 := tmod4_addrOfChar_other hbs29 0
    rw [evalFor_unfold] at hs0
    cir_hrun_c hs0

/-- **Difference (ii), indeterminate bytes:** cirlean's model copies an indeterminate source
byte (its value list passes non-`int` values through), while musl has undefined behaviour on
it. -/
theorem memcpy_diff_indeterminate (ctx' : Ctx) (bs bd : Nat) (ks kd : BlockKind) (m : Mem)
    (hs : m.blocks bs = some ⟨ks, true, .array (.int true 8) 1, .arr [.undef]⟩)
    (hd : m.blocks bd = some ⟨kd, true, .array (.int true 8) 1, .arr [.int 0]⟩) (hkd : kd ≠ .readonly)
    (hbs : bs < m.next) (hbd : bd < m.next) (hsd : bs ≠ bd) :
    evalCall ctx "musl_memcpy" [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 1] m ≠
      Std.runModel ctx' .memcpy [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 1] m := by
  have hmodel : Std.runModel ctx' .memcpy [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 1] m =
      .ok (.ret (some (.ptr (.loc bd [.idx 0]))),
        m.setBlock bd ⟨kd, true, .array (.int true 8) 1, .arr [.undef]⟩) := by
    have h' : Std.runModel ctx' .memcpy [.ptr (.loc bd [.idx 0]), .ptr (.loc bs [.idx 0]), .int 1] m =
        Std.memcpyModel ctx' m (.loc bd [.idx 0]) (.loc bs [.idx 0]) 1 := runModel_memcpy_of_ne ctx' m bd bs [.idx 0] [.idx 0] 1 hsd
    rw [h']
    simp [Std.memcpyModel, Std.typedRange?, splitLast, Ctx.typeAt, Ctx.sizeAlign, Mem.read?, Mem.live?, hs, hd,
      Val.get?, Std.rangeVals, Std.rangeWrite, Mem.write?, Val.set?, hkd, Std.retv]
  intro h
  rw [hmodel] at h
  exact musl_memcpy_undef_ub bs bd ks kd m hs hd hkd hbs hbd hsd _ h

/-! ### (iii) Overlapping ranges -/

/-- musl's `memcpy(&x[1], &x[0], 2)` on `x = 1 2 3`: if it returns, `x` is `1 1 1` (it copies
forward and re-reads the byte it has just written). -/
theorem musl_memcpy_overlap_run (b : Nat) (k : BlockKind) (m : Mem)
    (hx : m.blocks b = some ⟨k, true, .array (.int true 8) 3, .arr [.int 1, .int 2, .int 3]⟩) (hk : k ≠ .readonly)
    (hb : b < m.next) :
    pholds (evalCall ctx "musl_memcpy" [.ptr (.loc b [.idx 1]), .ptr (.loc b [.idx 0]), .int 2] m)
      (fun r => r.2.blocks b = some ⟨k, true, .array (.int true 8) 3, .arr [.int 1, .int 1, .int 1]⟩) := by
  intro r hr
  have hs0 := holds_of_eq_ok hr
  have cirH_x := hx
  have cirH_m0 : (0 : Int) % 4 = 0 := by decide
  have cirH_m1 : (1 : Int) % 4 = 1 := by decide
  have cirH_m2 : (2 : Int) % 4 = 2 := by decide
  have cirH_m3 : (3 : Int) % 4 = 3 := by decide
  have cirH_m4 : (4 : Int) % 4 = 0 := by decide
  have cirH_n0 : ((0 : Int) != 0) = false := by decide
  have cirH_n1 : ((1 : Int) != 0) = true := by decide
  have cirH_n2 : ((2 : Int) != 0) = true := by decide
  have cirH_n3 : ((3 : Int) != 0) = true := by decide
  have cirH_b16_0 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 0 16 = 0 := by decide
  have cirH_b8_0 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 0 8 = 0 := by decide
  have cirH_b4_0 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 0 4 = 0 := by decide
  have cirH_b2_0 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 0 2 = 0 := by decide
  have cirH_b1_0 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 0 1 = 0 := by decide
  have cirH_b16_2 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 2 16 = 0 := by decide
  have cirH_b8_2 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 2 8 = 0 := by decide
  have cirH_b4_2 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 2 4 = 0 := by decide
  have cirH_b2_2 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 2 2 = 2 := by decide
  have cirH_b1_2 : bitwise false 64 (fun x1 x2 => x1 &&& x2) 2 1 = 0 := by decide
  cir_hstep hs0
  cir_hrun_c hs0
  by_cases hb29 : b + 1 < 2 ^ 29
  · have cirH_p20 : (wrap false 64 (addrOfChar b 0)).tmod 4 = 0 := tmod4_addrOfChar_flat hb29 0
    have cirH_p21 : (wrap false 64 (addrOfChar b 1)).tmod 4 = 1 := tmod4_addrOfChar_flat hb29 1
    rw [evalFor_unfold] at hs0
    cir_hrun_c hs0
    subst hs0
    simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same]
  · have cirH_p20 : (wrap false 64 (addrOfChar b 0)).tmod 4 = 1 := tmod4_addrOfChar_other hb29 0
    have cirH_p21 : (wrap false 64 (addrOfChar b 1)).tmod 4 = 2 := tmod4_addrOfChar_other hb29 1
    have cirH_p22 : (wrap false 64 (addrOfChar b 2)).tmod 4 = 3 := tmod4_addrOfChar_other hb29 2
    have cirH_p23 : (wrap false 64 (addrOfChar b 3)).tmod 4 = 0 := tmod4_addrOfChar_other hb29 3
    rw [evalFor_unfold] at hs0
    cir_hrun_c hs0
    rw [evalFor_unfold] at hs0
    cir_hrun_c hs0
    rw [evalFor_unfold] at hs0
    cir_hrun_c hs0
    rw [evalFor_unfold] at hs0
    cir_hrun_c hs0
    subst hs0
    simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, upd_apply_same]

/-- **Difference (iii), overlapping ranges:** for `memcpy(&x[1], &x[0], 2)` on `x = 1 2 3`,
cirlean's model copies the original values (`1 1 2`), while musl copies forward byte by byte
(`1 1 1`). C makes an overlapping `memcpy` undefined (`restrict`); the model has no overlap
check, which is a gap in the model itself. -/
theorem memcpy_diff_overlap (ctx' : Ctx) (b : Nat) (k : BlockKind) (m : Mem)
    (hx : m.blocks b = some ⟨k, true, .array (.int true 8) 3, .arr [.int 1, .int 2, .int 3]⟩) (hk : k ≠ .readonly)
    (hb : b < m.next) :
    evalCall ctx "musl_memcpy" [.ptr (.loc b [.idx 1]), .ptr (.loc b [.idx 0]), .int 2] m ≠
      Std.memcpyModel ctx' m (.loc b [.idx 1]) (.loc b [.idx 0]) 2 := by
  have hmodel : Std.memcpyModel ctx' m (.loc b [.idx 1]) (.loc b [.idx 0]) 2 =
      .ok (.ret (some (.ptr (.loc b [.idx 1]))),
        m.setBlock b ⟨k, true, .array (.int true 8) 3, .arr [.int 1, .int 1, .int 2]⟩) := by

    simp [Std.memcpyModel, Std.typedRange?, splitLast, Ctx.typeAt, Ctx.sizeAlign, Mem.read?, Mem.live?, hx,
      Val.get?, Std.rangeVals, Std.rangeWrite, Mem.write?, Val.set?, hk, Std.retv, wrap]
  intro h
  rw [hmodel] at h
  have h2 := musl_memcpy_overlap_run b k m hx hk hb _ h
  simp [Mem.setBlock, upd] at h2

end EquivLean.Demo.Cir.Musl
