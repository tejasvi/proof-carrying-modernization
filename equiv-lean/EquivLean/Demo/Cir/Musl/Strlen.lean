import EquivLean.Demo.Cir.Musl.Partial
import EquivLean.Demo.Cir.Musl.Gen.Strlen

/-!
# musl `strlen` refines cirlean's `strlen` model

musl 1.2.5's generic C `strlen` (`src/string/strlen.c`, compiled as `musl_strlen`, see
`examples/cir/musl/README.md`) runs in a hypothesis (partial correctness).

Under punning2 (cirlean `next`), musl's word path is undefined behaviour in cirlean: the word loop
reads the `char` array through a `size_t` lvalue (`*w`), which GCC defines through `__may_alias__`
but cirlean's typed memory treats as a type-punned access. So this contract covers the byte path
only: the runs that find the NUL in the alignment loop (from an aligned position there is no outcome,
`musl_strlen_aligned_ub`). The string must be a `char` array (`hty`).
-/

open CIR EquivLean.Cir

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace EquivLean.Demo.Cir.Musl

open EquivLean.Demo.Cir.Musl.Gen.Strlen (ctx)

/-- What a state of `musl_strlen`'s body keeps fixed: the string's block, the caller's blocks,
the locals `__retval` (`m.next`) and `a` (`m.next + 2`), and the block counter. -/
abbrev SFix (m : Mem) (b i : Nat) (kd : BlockKind) (ty : Ty) (xs : List Val) (sm : Mem) : Prop :=
  sm.blocks b = some ⟨kd, true, ty, .arr xs⟩ ∧ m.next + 4 ≤ sm.next ∧
  (∀ b', b' < m.next → sm.blocks b' = m.blocks b') ∧
  sm.blocks m.next = some ⟨.stack, true, .int false 64, .undef⟩ ∧
  sm.blocks (m.next + 2) = some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc b [.idx i])⟩

theorem wrap8_hi {x : Int} (h1 : 128 ≤ x) (h2 : x ≤ 255) : wrap true 8 x = x - 256 := by
  unfold wrap
  simp only [Bool.true_and, decide_eq_true_eq]
  rw [show (2 : Int) ^ 8 = 256 from rfl, show (2 : Int) ^ (8 - 1) = 128 from rfl,
    Int.emod_eq_of_lt (by omega) (by omega)]
  split <;> omega

/-- `(uintptr_t)s % 8` for `s = &x[n]` in an array block `b`: cirlean encodes the pointer as
`(b + 1) * 2^32 + (n + 1)` (`evalCast .ptrToInt`), so only the index matters. -/
theorem p2i_mod8 (b n : Nat) :
    (wrap false 64 (((b : Int) + 1) * 4294967296 + (0 + ((n : Int) + 1)))).tmod 8 = ((n : Int) + 1) % 8 := by
  unfold wrap
  simp only [Bool.false_and, Bool.false_eq_true, ite_false]
  have h1 : 0 ≤ (((b : Int) + 1) * 4294967296 + (0 + ((n : Int) + 1))) % (2 : Int) ^ 64 :=
    Int.emod_nonneg _ (by decide)
  rw [Int.tmod_eq_emod_of_nonneg h1, Int.emod_emod_of_dvd _ (by decide : (8 : Int) ∣ 2 ^ 64)]
  omega

theorem musl_strlen_pspec (xs : List Val) (cs : Nat → Int) (b i e : Nat) (kd : BlockKind) (ty : Ty)
    (m : Mem) (hblk : m.blocks b = some ⟨kd, true, ty, .arr xs⟩) (hty : ∃ es tlen, ty = .array (.int es 8) tlen)
    (hb : b < m.next) (hwf : m.WF)
    (hie : i ≤ e) (he : e < xs.length) (hlen : xs.length < 2 ^ 62)
    (hxs : ∀ j, i ≤ j → j ≤ e → xs[j]? = some (.int (cs j)))
    (hrange : ∀ j, i ≤ j → j ≤ e → -128 ≤ cs j ∧ cs j ≤ 255)
    (hnz : ∀ j, i ≤ j → j < e → cs j ≠ 0) (hz : cs e = 0) :
    pholds (evalCall ctx "musl_strlen" [.ptr (.loc b [.idx i])] m)
      (fun r => r.1 = .ret (some (.int ((e : Int) - i))) ∧ (∀ b', b' < m.next → r.2.blocks b' = m.blocks b') ∧
        m.next ≤ r.2.next) := by
  obtain ⟨es, tlen, cirH_ty⟩ := hty
  intro r hr
  have hs := holds_of_eq_ok hr
  have cirH_t1 : ∀ n : Nat, ((n : Int) + 1).toNat = n + 1 := fun n => by omega
  have cirH_x : ∀ (j : Nat), i ≤ j → j ≤ e → xs[j]? = some (.int (cs j)) := hxs
  have cirH_xg : ∀ (j : Nat) (h : j < xs.length), i ≤ j → j ≤ e → xs[j] = .int (cs j) := fun j h h1 h2 => by
    have := hxs j h1 h2; rw [List.getElem?_eq_getElem h] at this; exact Option.some.inj this
  cir_hstep hs
  cir_hrun_c hs
  obtain ⟨s0, hs0, hs⟩ := holds_for_name hs
  -- `for (; (uintptr_t)s % ALIGN; s++) if (!*s) return s-a;`
  refine (fun hw => ?main1) (holds_for_inv hs
    (fun σ => σ.env = s0.env ∧ σ.names = s0.names ∧ SFix m b i kd ty xs σ.mem ∧
      σ.mem.blocks (m.next + 3) = some ⟨.stack, true, (Ty.int false 64).ptr, .undef⟩ ∧
      ∃ (j : Nat), σ.mem.blocks (m.next + 1) =
          some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc b [.idx j])⟩ ∧ i ≤ j ∧ j ≤ e)
    (fun a =>
      ((a.1 = .exit (.ret (some (.int ((e : Int) - i)))) ∧ (∀ b', b' < m.next → a.2.mem.blocks b' = m.blocks b') ∧
          m.next ≤ a.2.mem.next) ∨
       (a.1 = .next ∧ SFix m b i kd ty xs a.2.mem ∧ a.2.env = s0.env ∧ a.2.names = s0.names ∧
        a.2.mem.blocks (m.next + 3) = some ⟨.stack, true, (Ty.int false 64).ptr, .undef⟩ ∧
        ∃ (j : Nat), a.2.mem.blocks (m.next + 1) =
          some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc b [.idx j])⟩ ∧ i ≤ j ∧ j ≤ e)))
    ?init1 ?step1)
  case init1 =>
    subst hs0
    refine ⟨rfl, rfl, ⟨?_, by dsimp only; omega, fun b' hb' => ?_, ?_, ?_⟩, ?_, i, ?_, Nat.le_refl _, hie⟩
    · simp (disch := omega) only [upd_apply_ne, hblk]
    · simp (disch := omega) only [upd_apply_ne]
    all_goals simp (disch := omega) only [upd_apply_ne, upd_apply_same]
  case step1 =>
    intro σ ⟨cirH_env, cirH_names, ⟨cirH_blk, cirH_nx, cirH_old, cirH_rv, cirH_al⟩, cirH_wl, j, cirH_sl, hj1, hj2⟩
      r2 hr2
    have hs2 := holds_of_eq_ok hr2
    subst hs0
    dsimp only at cirH_env cirH_names
    have cirH_rg := hrange j hj1 hj2
    have cirH_p2i := p2i_mod8 b
    unfold forIter at hs2
    cir_hrun_c hs2
    all_goals (try subst hs2)
    all_goals first
      | -- the pointer is aligned: the loop ends
        exact Or.inr ⟨rfl, ⟨cirH_blk, cirH_nx, cirH_old, cirH_rv, cirH_al⟩, rfl, rfl, cirH_wl, j, cirH_sl, hj1, hj2⟩
      | -- a NUL: return s - a
        exfalso; simp only [bne_eq_false_iff_eq, bne_iff_ne, ne_eq] at *; rw [wrap8_hi (by omega) (by omega)] at *; omega
      | -- a NUL: return s - a
        have hc : cs j = 0 := by simp only [bne_eq_false_iff_eq] at cirH_br1; exact cirH_br1
        have hje : j = e := by
          rcases Nat.lt_or_ge j e with h | h
          · exact absurd hc (hnz j hj1 h)
          · omega
        subst hje
        refine Or.inl ⟨rfl, fun b' hb' => ?_, by dsimp only [Mem.endScope]; omega⟩
        simp (disch := omega) only [Mem.endScope, killRange_of_lt, killRange_self, upd_apply_ne, cirH_old]
      | -- a character: next position
        have hc : cs j ≠ 0 := by
          first
            | (simp only [bne_iff_ne, ne_eq] at cirA_br1; exact cirA_br1)
            | omega
        have hje : j < e := by
          rcases Nat.lt_or_ge j e with h | h
          · exact h
          · have hje' : j = e := by omega
            subst hje'
            exact absurd hz hc
        refine ⟨rfl, rfl, ⟨?_, ?_, fun b' hb' => ?_, ?_, ?_⟩, ?_, j + 1, ?_, by omega, by omega⟩
        all_goals first
          | (dsimp only [Mem.endScope]; omega)
          | simp (disch := omega) only [Mem.endScope, killRange_of_lt, killRange_self, upd_apply_ne, upd_apply_same,
              cirH_blk, cirH_old, cirH_rv, cirH_al, cirH_wl]
  case main1 =>
    obtain ⟨⟨st1, σ1⟩, hpost1, hk1⟩ := hw
    subst hs0
    rcases hpost1 with ⟨hst1, hfr1, hnx1⟩ |
      ⟨hst1, ⟨cirH_blk1, cirH_nx1, cirH_old1, cirH_rv1, cirH_al1⟩, cirH_env1, cirH_names1, cirH_wl1, j1, cirH_sl1,
        hj11, hj12⟩
    · -- returned from inside the loop
      dsimp only at hst1 hfr1 hnx1
      subst hst1
      cir_hrun_c hk1
      subst hk1
      exact ⟨rfl, fun b' hb' => by simp (disch := omega) only [Mem.endScope, killRange_of_lt, hfr1 b' hb'],
        by dsimp only [Mem.endScope]; omega⟩
    · dsimp only at hst1 cirH_env1 cirH_names1 cirH_wl1 cirH_sl1 cirH_blk1 cirH_nx1 cirH_old1 cirH_rv1 cirH_al1
      subst hst1
      cir_hrun_c hk1
      -- `for (w = (const void *)s; !HASZERO(*w); w++);`
      obtain ⟨s1, hs1, hk1⟩ := holds_for_name hk1
      refine (fun hw2 => ?main2) (holds_for_inv hk1
        (fun σ => σ.env = s1.env ∧ σ.names = s1.names ∧ SFix m b i kd ty xs σ.mem ∧
          σ.mem.blocks (m.next + 1) = some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc b [.idx j1])⟩ ∧
          ∃ (j : Nat), σ.mem.blocks (m.next + 3) =
              some ⟨.stack, true, (Ty.int false 64).ptr, .ptr (.loc b [.idx j])⟩ ∧ i ≤ j ∧ j ≤ e)
        (fun a => a.1 = .next ∧ a.2.env = s1.env ∧ a.2.names = s1.names ∧ SFix m b i kd ty xs a.2.mem ∧
          a.2.mem.blocks (m.next + 1) = some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc b [.idx j1])⟩ ∧
          ∃ (j : Nat), a.2.mem.blocks (m.next + 3) =
              some ⟨.stack, true, (Ty.int false 64).ptr, .ptr (.loc b [.idx j])⟩ ∧ i ≤ j ∧ j ≤ e)
        ?init2 ?step2)
      case init2 =>
        subst hs1
        refine ⟨rfl, rfl, ⟨?_, ?_, fun b' hb' => ?_, ?_, ?_⟩, ?_, j1, ?_, hj11, hj12⟩
        all_goals first
          | (dsimp only; omega)
          | simp (disch := omega) only [killRange_of_lt, killRange_self, upd_apply_ne, upd_apply_same, cirH_blk1,
              cirH_old1, cirH_rv1, cirH_al1, cirH_sl1]
      case step2 =>
        intro σ ⟨cirH_env, cirH_names, ⟨cirH_blk, cirH_nx, cirH_old, cirH_rv, cirH_al⟩, cirH_sl, j, cirH_wl, hj1, hj2⟩
          r2 hr2
        have hs2 := holds_of_eq_ok hr2
        subst hs1
        dsimp only at cirH_env cirH_names
        have cirH_rg := hrange j hj1 hj2
        unfold forIter at hs2
        cir_hrun_c hs2
        all_goals (try subst hs2)
        all_goals first
          | -- a zero byte in the word: the loop ends
            exact ⟨rfl, rfl, rfl, ⟨cirH_blk, cirH_nx, cirH_old, cirH_rv, cirH_al⟩, cirH_sl, j, cirH_wl, hj1, hj2⟩
          | -- no zero byte: the next word (the element is not the NUL)
            have hcz : cs j ≠ 0 := by
              first
                | omega
                | (intro h0; rw [h0] at cirH_rd0; simp only [Exit.cond.injEq] at cirH_rd0; revert cirH_rd0; decide)
            have hje : j < e := by
              rcases Nat.lt_or_ge j e with h | h
              · exact h
              · have hje' : j = e := by omega
                subst hje'
                exact absurd hz hcz
            refine ⟨rfl, rfl, ⟨?_, ?_, fun b' hb' => ?_, ?_, ?_⟩, ?_, j + 1, ?_, by omega, by omega⟩
            all_goals first
              | (dsimp only [Mem.endScope]; omega)
              | simp (disch := omega) only [Mem.endScope, killRange_of_lt, killRange_self, upd_apply_ne,
                  upd_apply_same, cirH_blk, cirH_old, cirH_rv, cirH_al, cirH_sl]
      case main2 =>
        obtain ⟨⟨st2, σ2⟩, ⟨hst2, cirH_env2, cirH_names2, ⟨cirH_blk2, cirH_nx2, cirH_old2, cirH_rv2, cirH_al2⟩,
          cirH_sl2, j2, cirH_wl2, hj21, hj22⟩, hk2⟩ := hw2
        subst hs1
        dsimp only at hst2 cirH_env2 cirH_names2 cirH_blk2 cirH_nx2 cirH_old2 cirH_rv2 cirH_al2 cirH_sl2 cirH_wl2
        subst hst2
        cir_hrun_c hk2
        -- `for (; *s; s++);`
        obtain ⟨s2, hs2, hk2⟩ := holds_for_name hk2
        refine (fun hw3 => ?main3) (holds_for_inv hk2
          (fun σ => σ.env = s2.env ∧ σ.names = s2.names ∧ SFix m b i kd ty xs σ.mem ∧
            ∃ (j : Nat), σ.mem.blocks (m.next + 1) =
                some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc b [.idx j])⟩ ∧ i ≤ j ∧ j ≤ e)
          (fun a => a.1 = .next ∧ a.2.env = s2.env ∧ a.2.names = s2.names ∧ SFix m b i kd ty xs a.2.mem ∧
            a.2.mem.blocks (m.next + 1) = some ⟨.stack, true, (Ty.int true 8).ptr, .ptr (.loc b [.idx e])⟩)
          ?init3 ?step3)
        case init3 =>
          subst hs2
          refine ⟨rfl, rfl, ⟨?_, ?_, fun b' hb' => ?_, ?_, ?_⟩, j2, ?_, hj21, hj22⟩
          all_goals first
            | (dsimp only; omega)
            | simp (disch := omega) only [killRange_of_lt, killRange_self, upd_apply_ne, upd_apply_same,
                cirH_blk2, cirH_old2, cirH_rv2, cirH_al2]
        case step3 =>
          intro σ ⟨cirH_env, cirH_names, ⟨cirH_blk, cirH_nx, cirH_old, cirH_rv, cirH_al⟩, j, cirH_sl, hj1, hj2⟩
            r2 hr2
          have hs3 := holds_of_eq_ok hr2
          subst hs2
          dsimp only at cirH_env cirH_names
          have cirH_rg := hrange j hj1 hj2
          unfold forIter at hs3
          cir_hrun_c hs3
          all_goals (try subst hs3)
          all_goals first
            | -- the NUL: the loop ends
              (exfalso; simp only [Exit.cond.injEq, bne_eq_false_iff_eq, decide_eq_false_iff_not] at cirH_rd0;
                rw [wrap8_hi (by omega) (by omega)] at cirH_rd0; omega)
            | have hc : cs j = 0 := by
                first
                  | (simp only [Exit.cond.injEq, bne_eq_false_iff_eq] at cirH_rd0; exact cirH_rd0)
                  | (simp only [Exit.cond.injEq, decide_eq_false_iff_not, Decidable.not_not] at cirH_rd0; exact cirH_rd0)
              have hje : j = e := by
                rcases Nat.lt_or_ge j e with h | h
                · exact absurd hc (hnz j hj1 h)
                · omega
              subst hje
              exact ⟨rfl, rfl, rfl, ⟨cirH_blk, cirH_nx, cirH_old, cirH_rv, cirH_al⟩, cirH_sl⟩
            | -- a character: the next one
              have hc : cs j ≠ 0 := by
                first
                  | omega
                  | (simp only [Exit.cond.injEq, bne_iff_ne, ne_eq] at cirH_rd0; exact cirH_rd0)
              have hje : j < e := by
                rcases Nat.lt_or_ge j e with h | h
                · exact h
                · have hje' : j = e := by omega
                  subst hje'
                  exact absurd hz hc
              refine ⟨rfl, rfl, ⟨?_, ?_, fun b' hb' => ?_, ?_, ?_⟩, j + 1, ?_, by omega, by omega⟩
              all_goals first
                | (dsimp only [Mem.endScope]; omega)
                | simp (disch := omega) only [Mem.endScope, killRange_of_lt, killRange_self, upd_apply_ne,
                    upd_apply_same, cirH_blk, cirH_old, cirH_rv, cirH_al]
        case main3 =>
          obtain ⟨⟨st3, σ3⟩, ⟨hst3, cirH_env3, cirH_names3, ⟨cirH_blk3, cirH_nx3, cirH_old3, cirH_rv3, cirH_al3⟩,
            cirH_sl3⟩, hk3⟩ := hw3
          subst hs2
          dsimp only at hst3 cirH_env3 cirH_names3 cirH_blk3 cirH_nx3 cirH_old3 cirH_rv3 cirH_al3 cirH_sl3
          subst hst3
          cir_hrun_c hk3
          subst hk3
          refine ⟨rfl, fun b' hb' => ?_, by dsimp only [Mem.endScope]; omega⟩
          simp (disch := omega) only [Mem.endScope, killRange_of_lt, upd_apply_ne, cirH_old3]

end EquivLean.Demo.Cir.Musl
