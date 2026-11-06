import CIR
import EquivLean.Demo.Gen.Cir.TinyRegex
import EquivLean.Demo.XLang.TinyRegex.CCompileLemmas
import EquivLean.Demo.XLang.TinyRegex.CEnc

/-!
# tiny-regex-c → model, C side: `re_compile`

`re_compile_spec`: from zero statics (as at program start: `initMem_ccl_buf`,
`initMem_re_compiled`), `re_compile(p ++ [0])` terminates without undefined behaviour and returns
`NULL` exactly when the model's `compile p` gives `none`; otherwise it returns `&re_compiled[0]`,
and the statics hold the model's arrays (`CompPost`, in `CEnc`'s terms).  Nothing else of the
caller's memory changes.

Proof (`re_compile_spec_core`, in this file's terms `patVal`, `reVal`, `bufVal`): cirlean's loop
rule on the `while` loop of `re_compile`, with the model's state behind the loop variables
(`ReInv`: the statics encode the model's arrays, the model's remaining loop computes
`compile p`), one symbolic execution per path of the loop body.  A character class runs the
nested copy loop `while ((pattern[++i] != ']') && (pattern[i] != '\0'))` by the same rule, with
the model's copy behind its variables (`CclInv`).
-/

namespace EquivLean.Demo.XLang.TinyRegex.C

open CIR EquivLean.Demo.Gen.Cir.TinyRegex
open EquivLean.Demo.XLang.TinyRegex

set_option maxHeartbeats 40000000

/-- The result of `re_compile` for the model's: `NULL`, or `re_compiled` and `ccl_buf` holding
the model's arrays. -/
def CompPost (kR kC : BlockKind) (res : Option (Array Tok × Array Nat)) (r : Option Val) (m' : Mem) :
    Prop :=
  match res with
  | none => r = some (.ptr .null)
  | some (re, buf) => r = some (.ptr (.loc 25 [.idx 0])) ∧
      m'.blocks 25 = some ⟨kR, true, .array (.record "regex_t") 30, .arr (re.toList.map (tokV 24))⟩ ∧
      m'.blocks 24 = some ⟨kC, true, .array (.int false 8) 40,
        .arr (buf.toList.map fun (x : Nat) => .int (x : Int))⟩

/-- What `re_compile` returns and leaves in the statics, by the model's `compile`. -/
def ReCompilePost (p : List Nat) (m : Mem) (r : Option Val) (m' : Mem) : Prop :=
  match (compile p.toArray).1 with
  | none => r = some (.ptr .null) ∧ Frame m m' [bCcl, bRe]
  | some (re, buf) => r = some (.ptr (.loc bRe [.idx 0])) ∧
      m'.blocks bRe = some ⟨.global, true, .array (.record "regex_t") 30, reVal re⟩ ∧
      m'.blocks bCcl = some ⟨.global, true, .array (.int false 8) 40, bufVal buf⟩ ∧
      Frame m m' [bCcl, bRe]

/-! ### One path of the loop body

The macros below run inside the loop-step goal of `re_compile_spec` and refer to its local names
(`ws`, `i`, `j`, `hb`, `hrc`, …), hence `hygiene false`. -/

/-- Close the goals left by symbolic execution of one path: the model part (`hRe`), then
arithmetic. -/
macro "re_close" : tactic => `(tactic| (
  all_goals (try assumption)
  all_goals (try (cir_strip_mdata; omega))
  all_goals (try cir_close')))

set_option hygiene false in
/-- A meta character `c` (`^ $ . * + ?`): entry `j` gets type `K` (`Kv` as an `Int`). -/
macro "re_meta_path " c:num K:ident Kv:num : tactic => `(tactic| (
  have cirH_x : ws[(0 + i).toNat]'(by rw [cirH_wslen]; omega) = Val.int $c := by
    rw [ws_get hws (by omega) _]; simp only [Int.zero_add, hb]; rfl
  have hRe := reInv_meta hrc hcb hinv hcont hi0 hj0 hjj hip hb (by decide) $K (by decide) $Kv (by decide) (by simp [compStep])
  cir_run
  re_close))

set_option hygiene false in
/-- `\c` for an escaped class `c` (`d D w W s S`): entry `j` gets type `K`. -/
macro "re_esc_path " c:num K:ident Kv:num : tactic => `(tactic| (
  have cirH_x1 : ws[(0 + (i + 1)).toNat]'(by rw [cirH_wslen]; omega) = Val.int $c := by
    rw [ws_get hws (by omega) _]; simp only [Int.zero_add, show (i + 1).toNat = i.toNat + 1 by omega, hc1]; rfl
  have hrd1 : rd p.toArray (i.toNat + 1) = ($c, 0) := by rw [rd_toArray_lt hip1, hc1]
  have hch0 : (0 : Int) = (re[j.toNat]!.ch : Int) := by
    rw [hinv.2.2.1 j.toNat (Nat.le_refl _) (by simp only [MAXOBJ]; omega)]; rfl
  have hRe := reInv_tok hrc hcb hinv hcont hi0 hj0 hjj hip hb (by decide) $K re[j.toNat]!.ch (by decide) $Kv 0 (by decide) hch0 (i.toNat + 1) hip1 (by rw [hc1]; decide) (i + 1 + 1) (by omega) (by simp [compStep, hrd1])
  cir_run
  re_close))

set_option hygiene false in
/-- A path that ends in `return 0`, where the model gives `none` (`hnone`). -/
macro "re_ret0" : tactic => `(tactic| (
  cir_run
  all_goals (try simp only [loopPost])
  all_goals (try cir_run)
  all_goals (try simp only [ReCompilePost, hnone, bCcl, bRe])
  all_goals (try cir_run)
  re_close))

set_option hygiene false in
/-- Clear the facts the rest of a class path no longer needs (disequalities and `toNat`s make
every `omega` call of symbolic execution slow). -/
macro "re_cls_clear" : tactic => `(tactic| (
  try clear hN
  try clear h93
  try clear h92
  try clear hE
  try clear hip
  try clear hjs
  try clear hj30
  try clear hk
  try clear hkk2
  try clear hb
  try clear hc
  try clear hc2
  try clear hcI
  try clear hcont
  try clear hinv
  try clear hS))

set_option hygiene false in
/-- The `[..]` copy loop of a class of kind `Kv`, copied from `iS` (`iSI` as an `Int`), and the
rest of the pass. -/
macro "re_class_loop " iS:term:max iSI:term:max Kv:num : tactic => `(tactic| (
  cir_loop (fun i ccl_bufidx ccl_buf => $iSI ≤ i ∧ i < (p.length : Int) ∧
      i - ccl_bufidx = $iSI - bO ∧ bO ≤ ccl_bufidx ∧ ccl_bufidx ≤ 40 ∧
      CclInv p $iS bO.toNat buf i ccl_bufidx ccl_buf)
    (fun i ccl_bufidx ccl_buf => (p.length : Int) - i)
  case cir_init_goal =>
    cir_run
    all_goals first
      | exact cclInv_start hcb hbsz _ _ rfl rfl
      | exact cclInv_start hcb hbsz _ _ (toNat_add_one hi0) rfl
      | (cir_strip_mdata; omega)
      | cir_close'
  case cir_step_goal =>
    try clear cirH_v1
    try clear cirH_v2
    obtain ⟨hk0, hk1, hk2, hk3, hk4, hcI⟩ := cirH_user
    try cir_simp_hyp cirH_slot2
    by_cases hN : i + 1 = (p.length : Int)
    · -- the NUL: the copy ends
      have hy1b : (0 + (i + 1)).toNat < ws.length := by rw [cirH_wslen]; omega
      have cirH_y1 : ws[(0 + (i + 1)).toNat]'hy1b = Val.int 0 := ws_get_end hws (by omega) _
      obtain ⟨bufA, hcbA, hcc⟩ := cclInv_nul hcI (by omega)
      by_cases hfull : 40 ≤ ccl_bufidx
      · have hnone := class_full hcont hS hip hb hj30 hjs hcc (by simp only [MAXCCL]; omega)
        re_cls_clear
        re_ret0
      · have hnone := class_nul hcont hS hip hb hj30 hjs hcc (by simp only [MAXCCL]; omega) (by omega)
        re_cls_clear
        re_ret0
    have hk : i.toNat + 1 < p.length := by omega
    obtain ⟨c, hc⟩ : ∃ c, p[i.toNat + 1] = c := ⟨_, rfl⟩
    have hcr : 0 < c ∧ c < 256 := hc ▸ hp _ (List.getElem_mem _)
    have hy1b : (0 + (i + 1)).toNat < ws.length := by rw [cirH_wslen]; omega
    have cirH_y1 : ws[(0 + (i + 1)).toNat]'hy1b = Val.int (sc c) := by
      rw [ws_get hws (by omega) _]
      simp only [Int.zero_add, show (i + 1).toNat = i.toNat + 1 by omega, hc]
    by_cases h93 : c = 93
    · -- `]`: the copy ends
      subst h93
      rw [show sc 93 = 93 by decide] at cirH_y1
      obtain ⟨bufA, hcbA, hcc⟩ := cclInv_stop hcI hk hc
      by_cases hfull : 40 ≤ ccl_bufidx
      · have hnone := class_full hcont hS hip hb hj30 hjs hcc (by simp only [MAXCCL]; omega)
        re_cls_clear
        re_ret0
      · have hRe := reInv_class hrc hinv hcont hj0 hjj hip hb hS (by decide) $Kv rfl hcc (by simp only [MAXCCL]; omega) hk (by rw [hc]; decide) ccl_buf hcbA (i + 2) (ccl_bufidx + 1) (by omega) (by omega) _ rfl _ rfl
        re_cls_clear
        cir_run
        all_goals (try simp only [loopPost])
        all_goals (try cir_run)
        re_close
    have cirH_yr : -128 ≤ sc c ∧ sc c ≤ 127 := sc_range' hcr.2
    have cirH_y0 : sc c ≠ 0 := by unfold sc; split <;> omega
    have cirH_y93 : sc c ≠ 93 := by unfold sc; split <;> omega
    by_cases h92 : c = 92
    · -- `\\`
      subst h92
      rw [show sc 92 = 92 by decide] at cirH_y1
      by_cases hfull : 39 ≤ ccl_bufidx
      · have hnone := class_none hcont hS hip hb hj30 hjs (cclInv_esc_full hcI hk hc hfull)
        re_cls_clear
        re_ret0
      have hy2b : (0 + (i + 2)).toNat < ws.length := by rw [cirH_wslen]; omega
      by_cases hE : i.toNat + 2 = p.length
      · have cirH_y2 : ws[(0 + (i + 2)).toNat]'hy2b = Val.int 0 := ws_get_end hws (by omega) _
        have hnone := class_none hcont hS hip hb hj30 hjs (cclInv_esc_end hcI (by omega) hk hc (by omega) hE)
        re_cls_clear
        re_ret0
      have hkk2 : i.toNat + 2 < p.length := by omega
      obtain ⟨c2, hc2⟩ : ∃ c2, p[i.toNat + 2] = c2 := ⟨_, rfl⟩
      have hc2r : 0 < c2 ∧ c2 < 256 := hc2 ▸ hp _ (List.getElem_mem _)
      have cirH_y2 : ws[(0 + (i + 2)).toNat]'hy2b = Val.int (sc c2) := by
        rw [ws_get hws (by omega) _]
        simp only [Int.zero_add, show (i + 2).toNat = i.toNat + 2 by omega, hc2]
      have cirH_y2r : -128 ≤ sc c2 ∧ sc c2 ≤ 127 := sc_range' hc2r.2
      have cirH_y20 : sc c2 ≠ 0 := by unfold sc; split <;> omega
      have cirH_w2 : wrap false 8 (sc c2) = c2 := wrap_u8_sc hc2r.2
      have cirH_w92 : wrap false 8 92 = 92 := by decide
      have hCc := cclInv_esc hcI (by omega) (by omega) (by omega) hkk2 hc hc2 (by omega)
      re_cls_clear
      cir_run
      re_close
    have cirH_y92 : sc c ≠ 92 := by unfold sc; split <;> omega
    by_cases hfull : 40 ≤ ccl_bufidx
    · have hnone := class_none hcont hS hip hb hj30 hjs (cclInv_full hcI hk hc (by omega) h92 h93 hfull)
      re_cls_clear
      re_ret0
    have cirH_w : wrap false 8 (sc c) = c := wrap_u8_sc hcr.2
    have hCc := cclInv_char hcI (by omega) (by omega) (by omega) hk hc (by omega) h92 h93
    re_cls_clear
    cir_run
    re_close
  re_close))

set_option maxHeartbeats 400000000
/-- The C side of `re_compile`, in this file's terms (`patVal`, `reVal`, `bufVal`). -/
theorem re_compile_spec_core (p : List Nat) (hp : ∀ b ∈ p, 0 < b ∧ b < 256) (bp : Nat) (kp : BlockKind)
    (typ : Ty) (m : Mem) (hpat : m.blocks bp = some ⟨kp, true, typ, patVal p⟩)
    (htyp : ∃ es tlen, typ = .array (.int es 8) tlen) (hbp : bp < m.next)
    (h24 : m.blocks bCcl = some ⟨.global, true, .array (.int false 8) 40, bufVal (Array.replicate MAXCCL 0)⟩)
    (h25 : m.blocks bRe = some ⟨.global, true, .array (.record "regex_t") 30,
      reVal (Array.replicate MAXOBJ {})⟩)
    (hnext : 26 ≤ m.next) (hbp24 : bp ≠ bCcl) (hbp25 : bp ≠ bRe) :
    Returns ctx fn_re_compile.sym [.ptr (.loc bp [.idx 0])] m (fun r m' => ReCompilePost p m r m') := by
  obtain ⟨es, tlen, rfl⟩ := htyp
  have hsc : ∀ b ∈ p ++ [0], -128 ≤ sc b ∧ sc b ≤ 127 := by
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact sc_range' (hp b hb).2
    · simp at hb; subst hb; decide
  have cirH_g24 : 24 < m.next := by omega
  have cirH_g25 : 25 < m.next := by omega
  have cirH_bp24 : bp ≠ 24 := hbp24
  have cirH_bp25 : bp ≠ 25 := hbp25
  rw [bufVal_zero] at h24
  rw [reVal_zero] at h25
  simp only [patVal] at hpat
  generalize hws : (p ++ [0]).map (fun b => Val.int (sc b)) = ws at hpat
  have cirH_wslen : ws.length = p.length + 1 := by rw [← hws]; simp
  cir_start
  cir_vcg
  cir_loop (fun i j ccl_bufidx ccl_buf re_compiled => 0 ≤ i ∧ i ≤ p.length ∧ 0 ≤ j ∧ j < 30 ∧
      1 ≤ ccl_bufidx ∧ ccl_bufidx ≤ 40 ∧ i ≤ 3 * j + ccl_bufidx ∧
      ReInv p i j ccl_bufidx ccl_buf re_compiled)
    (fun i j ccl_bufidx ccl_buf re_compiled => 30 - j)
  case cir_init_goal =>
    cir_run
    all_goals first
      | exact reInv_start p
      | omega
      | (simp only [CIR.inRange_eq_true_iff, CIR.intMin_s32, CIR.intMax_s32]; omega)
  case cir_step_goal =>
    obtain ⟨hi0, hi1, hj0, hj1, hb0, hb1, hij, re, buf, hre, hbuf, hinv, hcont⟩ := cirH_user
    subst hre hbuf
    try cir_simp_hyp cirH_slot3
    try cir_simp_hyp cirH_slot4
    generalize hrc : List.map tokVal re.toList = rc at *
    generalize hcb : List.map (fun b : Nat => Val.int (b : Int)) buf.toList = cb at *
    have cirH_rcj : rc[j.toNat]'(by omega) = Val.agg [.int 0, .agg [.int 0, .undef]] :=
      rc_get_j hrc hinv (by omega) _
    by_cases hend : i = (p.length : Int)
    · -- the NUL: the loop ends
      have cirH_x : ws[(0 + i).toNat]'(by rw [cirH_wslen]; omega) = Val.int 0 :=
        ws_get_end hws (by omega) _
      obtain ⟨hpost, hreV, hbufV⟩ := exit_facts hrc hcb hinv hcont hi0 hi1 hj0 hj1
        (Or.inl (by rw [show i.toNat = p.length by omega, rd_toArray_end]))
      cir_run
      all_goals (try (unfold ReCompilePost; rw [hpost]; simp only [bRe, bCcl]; rw [hreV, hbufV]))
      all_goals (try cir_run)
      re_close
    have hip : i.toNat < p.length := by omega
    obtain ⟨b, hb⟩ : ∃ b, p[i.toNat] = b := ⟨_, rfl⟩
    have hbr : 0 < b ∧ b < 256 := hb ▸ hp _ (List.getElem_mem _)
    by_cases hjx : 30 ≤ j + 1
    · -- 29 entries used: the loop ends
      have cirH_x : ws[(0 + i).toNat]'(by rw [cirH_wslen]; omega) = Val.int (sc b) := by
        rw [ws_get hws (by omega) _]; simp only [Int.zero_add, hb]
      have cirH_scr : -128 ≤ sc b ∧ sc b ≤ 127 := sc_range' hbr.2
      have cirH_c0 : sc b ≠ 0 := by unfold sc; split <;> omega
      obtain ⟨hpost, hreV, hbufV⟩ := exit_facts hrc hcb hinv hcont hi0 hi1 hj0 hj1
        (Or.inr (by simp only [MAXOBJ]; omega))
      cir_run
      all_goals (try (unfold ReCompilePost; rw [hpost]; simp only [bRe, bCcl]; rw [hreV, hbufV]))
      all_goals (try cir_run)
      re_close
    have hjj : j + 1 < 30 := by omega
    by_cases h94 : b = 94
    · subst h94; re_meta_path 94 BEGIN 2
    by_cases h36 : b = 36
    · subst h36; re_meta_path 36 END 3
    by_cases h46 : b = 46
    · subst h46; re_meta_path 46 DOT 1
    by_cases h42 : b = 42
    · subst h42; re_meta_path 42 STAR 5
    by_cases h43 : b = 43
    · subst h43; re_meta_path 43 PLUS 6
    by_cases h63 : b = 63
    · subst h63; re_meta_path 63 QUESTIONMARK 4
    by_cases h92 : b = 92
    · subst h92
      have cirH_x : ws[(0 + i).toNat]'(by rw [cirH_wslen]; omega) = Val.int 92 := by
        rw [ws_get hws (by omega) _]; simp only [Int.zero_add, hb]; rfl
      by_cases hend1 : i + 1 = (p.length : Int)
      · -- `\` as the last byte: nothing is written
        have cirH_x1 : ws[(0 + (i + 1)).toNat]'(by rw [cirH_wslen]; omega) = Val.int 0 :=
          ws_get_end hws (by omega) _
        have hrd1 : rd p.toArray (i.toNat + 1) = (0, 0) := by
          rw [show i.toNat + 1 = p.length by omega, rd_toArray_end]
        have hRe := reInv_skip hrc hcb hinv hcont hi0 hj0 hjj hip hb (by decide) (by simp [compStep, hrd1])
        cir_run
        re_close
      have hip1 : i.toNat + 1 < p.length := by omega
      obtain ⟨c1, hc1⟩ : ∃ c1, p[i.toNat + 1] = c1 := ⟨_, rfl⟩
      have hc1r : 0 < c1 ∧ c1 < 256 := hc1 ▸ hp _ (List.getElem_mem _)
      by_cases h100 : c1 = 100
      · subst h100; re_esc_path 100 DIGIT 10
      by_cases h68 : c1 = 68
      · subst h68; re_esc_path 68 NOT_DIGIT 11
      by_cases h119 : c1 = 119
      · subst h119; re_esc_path 119 ALPHA 12
      by_cases h87 : c1 = 87
      · subst h87; re_esc_path 87 NOT_ALPHA 13
      by_cases h115 : c1 = 115
      · subst h115; re_esc_path 115 WHITESPACE 14
      by_cases h83 : c1 = 83
      · subst h83; re_esc_path 83 NOT_WHITESPACE 15
      -- `\c` for any other byte `c`: `CHAR` with `ch := c`
      have cirH_x1 : ws[(0 + (i + 1)).toNat]'(by rw [cirH_wslen]; omega) = Val.int (sc c1) := by
        rw [ws_get hws (by omega) _]; simp only [Int.zero_add, show (i + 1).toNat = i.toNat + 1 by omega, hc1]
      have hrd1 : rd p.toArray (i.toNat + 1) = (c1, 0) := by rw [rd_toArray_lt hip1, hc1]
      have cirH_scr1 : -128 ≤ sc c1 ∧ sc c1 ≤ 127 := sc_range' hc1r.2
      have cirH_d0 : sc c1 ≠ 0 := by unfold sc; split <;> omega
      have cirH_d100 : sc c1 ≠ 100 := by unfold sc; split <;> omega
      have cirH_d68 : sc c1 ≠ 68 := by unfold sc; split <;> omega
      have cirH_d119 : sc c1 ≠ 119 := by unfold sc; split <;> omega
      have cirH_d87 : sc c1 ≠ 87 := by unfold sc; split <;> omega
      have cirH_d115 : sc c1 ≠ 115 := by unfold sc; split <;> omega
      have cirH_d83 : sc c1 ≠ 83 := by unfold sc; split <;> omega
      have cirH_w1 : wrap false 8 (sc c1) = c1 := wrap_u8_sc hc1r.2
      have hRe := reInv_tok hrc hcb hinv hcont hi0 hj0 hjj hip hb (by decide) CHAR c1 (by decide) 7 c1 rfl rfl (i.toNat + 1) hip1 (by rw [hc1]; omega) (i + 1 + 1) (by omega) (by simp [compStep, hrd1, h100, h68, h119, h87, h115, h83, show c1 ≠ 0 by omega])
      cir_run
      re_close
    by_cases h91 : b = 91
    · -- a character class `[..]` or `[^..]`
      subst h91
      clear h94 h36 h46 h42 h43 h63 h92
      have hxb : (0 + i).toNat < ws.length := by rw [cirH_wslen]; omega
      have cirH_x : ws[(0 + i).toNat]'hxb = Val.int 91 := by
        rw [ws_get hws (by omega) _]; simp only [Int.zero_add, hb]; rfl
      have hjs : j.toNat < re.size := by rw [hinv.1]; simp only [MAXOBJ]; omega
      have hj30 : j.toNat + 1 < MAXOBJ := by simp only [MAXOBJ]; omega
      have hbsz : buf.size = MAXCCL := hinv.2.1
      -- the byte after `[` as a signed `char` (0 at the end of the pattern)
      have hx1b : (0 + (i + 1)).toNat < ws.length := by rw [cirH_wslen]; omega
      obtain ⟨v1, cirH_x1, cirH_v1r, hv1⟩ : ∃ v1 : Int, ws[(0 + (i + 1)).toNat]'hx1b = Val.int v1 ∧
          (-128 ≤ v1 ∧ v1 ≤ 127) ∧ (v1 = 94 ↔ (rd p.toArray (i.toNat + 1)).1 = 94) := by
        by_cases hend1 : i + 1 = (p.length : Int)
        · refine ⟨0, ws_get_end hws (by omega) _, by decide, ?_⟩
          rw [show i.toNat + 1 = p.length by omega, rd_toArray_end]; decide
        · have hip1 : i.toNat + 1 < p.length := by omega
          refine ⟨sc p[i.toNat + 1], ?_, sc_range' (hp _ (List.getElem_mem _)).2, ?_⟩
          · rw [ws_get hws (by omega) _]
            simp only [Int.zero_add, show (i + 1).toNat = i.toNat + 1 by omega]
          · rw [rd_toArray_lt hip1]; exact sc_eq_natCast_iff (hp _ (List.getElem_mem _)).2 (by decide)
      generalize hiO : i = iO at *
      generalize hbO : ccl_bufidx = bO at *
      by_cases hcaret : v1 = 94
      · -- `[^`: an `INV_CHAR_CLASS`, copied from `i + 1`
        have h1 : (rd p.toArray (iO.toNat + 1)).1 = 94 := hv1.1 hcaret
        subst hcaret
        have hip1 : iO.toNat + 1 < p.length := by
          have := lt_size_of_rd_ne_zero (p := p.toArray) (i := iO.toNat + 1) (by rw [h1]; decide)
          simpa using this
        have hx2b : (0 + (iO + 2)).toNat < ws.length := by rw [cirH_wslen]; omega
        by_cases hend2 : iO.toNat + 2 = p.length
        · -- `[^` and the NUL: `return 0`
          have cirH_x2 : ws[(0 + (iO + 2)).toNat]'hx2b = Val.int 0 := ws_get_end hws (by omega) _
          have hnone := class_caret_nul hcont hip hb hj30 h1 hend2
          clear hv1 hend hend2 hip1
          re_ret0
        obtain ⟨c2, hc2⟩ : ∃ c2, p[iO.toNat + 2] = c2 := ⟨_, rfl⟩
        have hc2r : 0 < c2 ∧ c2 < 256 := hc2 ▸ hp _ (List.getElem_mem _)
        have cirH_x2 : ws[(0 + (iO + 2)).toNat]'hx2b = Val.int (sc c2) := by
          rw [ws_get hws (by omega) _]
          simp only [Int.zero_add, show (iO + 2).toNat = iO.toNat + 2 by omega, hc2]
        have cirH_v2r : -128 ≤ sc c2 ∧ sc c2 ≤ 127 := sc_range' hc2r.2
        have cirH_v2 : sc c2 ≠ 0 := by unfold sc; split <;> omega
        have hS : ClassStart p iO.toNat (iO.toNat + 1) INV_CHAR_CLASS :=
          Or.inr ⟨rfl, rfl, h1, by rw [rd_toArray_lt (by omega), hc2]; omega⟩
        have hiS : iO + 1 < (p.length : Int) := by omega
        clear hv1 hend hend2 hc2 h1 hip1
        cir_run
        all_goals (try (cir_strip_mdata; omega))
        re_class_loop (iO.toNat + 1) (iO + 1) 9
      -- `[`: a `CHAR_CLASS`, copied from `i`
      have cirH_v1 : v1 ≠ 94 := hcaret
      have hS : ClassStart p iO.toNat iO.toNat CHAR_CLASS := Or.inl ⟨rfl, rfl, fun h => hcaret (hv1.2 h)⟩
      clear hcaret hv1 hend
      cir_run
      all_goals (try (cir_strip_mdata; omega))
      re_class_loop iO.toNat iO 8
    -- any other byte: `CHAR` with `ch := c`
    have cirH_x : ws[(0 + i).toNat]'(by rw [cirH_wslen]; omega) = Val.int (sc b) := by
      rw [ws_get hws (by omega) _]; simp only [Int.zero_add, hb]
    have cirH_scr : -128 ≤ sc b ∧ sc b ≤ 127 := sc_range' hbr.2
    have cirH_c0 : sc b ≠ 0 := by unfold sc; split <;> omega
    have cirH_c94 : sc b ≠ 94 := by unfold sc; split <;> omega
    have cirH_c36 : sc b ≠ 36 := by unfold sc; split <;> omega
    have cirH_c46 : sc b ≠ 46 := by unfold sc; split <;> omega
    have cirH_c42 : sc b ≠ 42 := by unfold sc; split <;> omega
    have cirH_c43 : sc b ≠ 43 := by unfold sc; split <;> omega
    have cirH_c63 : sc b ≠ 63 := by unfold sc; split <;> omega
    have cirH_c92 : sc b ≠ 92 := by unfold sc; split <;> omega
    have cirH_c91 : sc b ≠ 91 := by unfold sc; split <;> omega
    have cirH_w : wrap false 8 (sc b) = b := wrap_u8_sc hbr.2
    have hRe := reInv_tok hrc hcb hinv hcont hi0 hj0 hjj hip hb (by omega) CHAR b (by decide) 7 b rfl rfl i.toNat hip (by rw [hb]; omega) (i + 1) (by omega) (by simp [compStep, h94, h36, h46, h42, h43, h63, h92, h91])
    cir_run
    re_close


/-! ### The statement in the composition's terms (`CEnc`) -/

theorem tokVal_eq_tokV : tokVal = tokV 24 := by
  funext t
  unfold tokVal tokV isClassKind
  by_cases h : t.type = 8 ∨ t.type = 9
  · have h' : (t.type == CHAR_CLASS || t.type == INV_CHAR_CLASS) = true := by
      simp only [CHAR_CLASS, INV_CHAR_CLASS, Bool.or_eq_true, beq_iff_eq]; exact h
    rw [ite_eq_left h', ite_eq_left h]
  · have h' : ¬ (t.type == CHAR_CLASS || t.type == INV_CHAR_CLASS) = true := by
      simp only [CHAR_CLASS, INV_CHAR_CLASS, Bool.or_eq_true, beq_iff_eq]; exact h
    rw [ite_eq_right h', ite_eq_right h]

theorem patVal_eq_patL (p : List Nat) : patVal p = .arr ((patL p).map .int) := by
  simp [patVal, patL, sc]

theorem tokV_zero : tokV 24 {} = .agg [.int 0, .agg [.int 0, .undef]] := by
  simp [tokV]

theorem frame_swap {m m' : Mem} (h : Frame m m' [bCcl, bRe]) : Frame m m' [25, 24] :=
  ⟨h.1, fun b hb hlt => h.2 b (by simp [bCcl, bRe] at hb ⊢; omega) hlt⟩

theorem compPost_of {p : List Nat} {m : Mem} {r : Option Val} {m' : Mem}
    (h : ReCompilePost p m r m') :
    CompPost .global .global (compile p.toArray).1 r m' ∧ Frame m m' [25, 24] := by
  unfold ReCompilePost at h
  unfold CompPost
  generalize (compile p.toArray).1 = res at h ⊢
  rcases res with _ | ⟨re, buf⟩
  · exact ⟨h.1, frame_swap h.2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨⟨h1, ?_, ?_⟩, frame_swap h4⟩
    · rw [h2, reVal, tokVal_eq_tokV]
    · rw [h3, bufVal]

/-- `re_compile(p ++ [0])` from zero-initialized statics (`re_compiled` is block 25, `ccl_buf`
block 24 of the module). -/
theorem re_compile_spec (p : List Nat) (bp : Nat) (kp : BlockKind) (typ : Ty) (m : Mem)
    (hp : ∀ b ∈ p, 0 < b ∧ b < 256)
    (hbp : m.blocks bp = some ⟨kp, true, typ, .arr ((patL p).map .int)⟩)
    (htyp : ∃ es tlen, typ = .array (.int es 8) tlen)
    (hbR : m.blocks 25 = some ⟨.global, true, .array (.record "regex_t") 30,
      .arr (List.replicate 30 (tokV 24 {}))⟩)
    (hbC : m.blocks 24 = some ⟨.global, true, .array (.int false 8) 40, .arr (List.replicate 40 (.int 0))⟩)
    (hn : 26 ≤ m.next) (hbpn : bp < m.next) (hbp26 : 26 ≤ bp) :
    Returns ctx fn_re_compile.sym [.ptr (.loc bp [.idx 0])] m (fun r m' =>
      CompPost .global .global (compile p.toArray).1 r m' ∧ Frame m m' [25, 24]) := by
  have h := re_compile_spec_core p hp bp kp typ m (by rw [patVal_eq_patL]; exact hbp) htyp hbpn
    (by rw [bufVal_zero]; exact hbC) (by rw [reVal_zero, ← tokV_zero]; exact hbR) hn
    (by simp only [bCcl]; omega) (by simp only [bRe]; omega)
  unfold Returns Calls at h ⊢
  refine Res.holds_mono h fun a ha => ?_
  rcases a with ⟨e, m'⟩
  cases e <;> first | exact ha.elim | exact compPost_of ha

/-- `ccl_buf` in the module's initial memory: forty zero bytes. -/
theorem initMem_ccl_buf :
    module.initMem.blocks 24 = some ⟨.global, true, .array (.int false 8) 40, .arr (List.replicate 40 (.int 0))⟩ := by
  rfl

/-- `re_compiled` in the module's initial memory: thirty zero `regex_t`s. -/
theorem initMem_re_compiled :
    module.initMem.blocks 25 = some ⟨.global, true, .array (.record "regex_t") 30,
      .arr (List.replicate 30 (tokV 24 {}))⟩ := by
  rfl

theorem initMem_next : module.initMem.next = 26 := by
  rw [Module.initMem_next]; rfl

end EquivLean.Demo.XLang.TinyRegex.C
