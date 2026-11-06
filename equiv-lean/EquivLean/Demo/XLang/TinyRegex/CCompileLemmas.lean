import EquivLean.Demo.XLang.TinyRegex.CCompileDefs
import EquivLean.Demo.XLang.TinyRegex.ModelLemmas

/-!
# tiny-regex-c → model, C side: small lemmas for `re_compile`

Bytes against signed `char`s, the pattern string against the model's `rd`, and the encodings of
the statics under the model's `Array.set!`.
-/

namespace EquivLean.Demo.XLang.TinyRegex.C

open CIR EquivLean.Demo.XLang.TinyRegex

/-! ## Bytes and signed `char`s -/

theorem sc_lt128 {b : Nat} (h : b < 128) : sc b = b := by
  unfold sc; simp [h]

theorem sc_eq_natCast_iff {b n : Nat} (hb : b < 256) (hn : n < 128) : sc b = (n : Int) ↔ b = n := by
  unfold sc; split <;> omega

theorem sc_ne_natCast {b n : Nat} (hb : b < 256) (hn : n < 128) (h : b ≠ n) : sc b ≠ (n : Int) := by
  rw [Ne, sc_eq_natCast_iff hb hn]; exact h

theorem sc_range' {b : Nat} (h : b < 256) : -128 ≤ sc b ∧ sc b ≤ 127 := by
  unfold sc; split <;> omega

/-- Storing a `char` into an `unsigned char`: the byte. -/
theorem wrap_u8_sc {b : Nat} (h : b < 256) : wrap false 8 (sc b) = (b : Int) := by
  unfold sc wrap
  split
  · simp only
    exact Int.emod_eq_of_lt (by omega) (by omega)
  · simp only
    rw [show (b : Int) - 256 = (b : Int) + (-1) * 2 ^ 8 by omega, Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by omega) (by omega)

/-! ## The pattern string -/

theorem pat_getElem_lt {p : List Nat} {k : Nat} (hk : k < p.length) (h : k < (p ++ [0]).length) :
    (p ++ [0])[k] = p[k] := List.getElem_append_left hk

theorem pat_getElem_end {p : List Nat} {k : Nat} (hk : k = p.length) (h : k < (p ++ [0]).length) :
    (p ++ [0])[k] = 0 := by
  subst hk; simp

theorem rd_toArray_lt {p : List Nat} {k : Nat} (hk : k < p.length) :
    rd p.toArray k = (p[k], 0) := by
  unfold rd; simp [hk]

theorem rd_toArray_end {p : List Nat} : rd p.toArray p.length = (0, 0) := by
  unfold rd; simp

/-! ## The statics under `set!` -/

theorem map_toList_set! {α β : Type} (f : α → β) (a : Array α) (k : Nat) (x : α) :
    (a.set! k x).toList.map f = (a.toList.map f).set k (f x) := by
  simp [Array.set!_eq_setIfInBounds, List.map_set]

theorem tokVal_type (t : Tok) (k : Nat) (hk : isClassKind k = false) :
    tokVal { t with type := k } = .agg [.int k, .agg [.int t.ch, .undef]] := by
  simp [tokVal, hk]

theorem tokVal_default : tokVal ({} : Tok) = .agg [.int 0, .agg [.int 0, .undef]] := by
  simp [tokVal, isClassKind, CHAR_CLASS, INV_CHAR_CLASS]

/-! ## The loop invariant's model part -/

/-- The model state behind `re_compile`'s loop variables `i`, `j`, `ccl_bufidx` and the statics'
elements `cb` (`ccl_buf`), `rc` (`re_compiled`): the statics encode the model's arrays, and the
rest of the model's loop computes `compile p`.  A definition, so that symbolic execution leaves
it alone. -/
def ReInv (p : List Nat) (i j bidx : Int) (cb rc : List Val) : Prop :=
  ∃ (re : Array Tok) (buf : Array Nat), rc = re.toList.map tokVal ∧
    cb = buf.toList.map (fun b : Nat => Val.int (b : Int)) ∧
    CompInv j.toNat bidx.toNat re buf ∧
    compLoop p.toArray i.toNat j.toNat bidx.toNat re buf 0 = compile p.toArray

theorem toNat_add_one {i : Int} (h : 0 ≤ i) : (i + 1).toNat = i.toNat + 1 := by omega

/-- The model's continuation after a pass of the loop body that leaves the new index `i'`
(pointing at a non-NUL character) and the new arrays. -/
theorem compLoop_cont {p : List Nat} {i j bidx : Nat} {re : Array Tok} {buf : Array Nat}
    {i' b' : Nat} {re' : Array Tok} {buf' : Array Nat}
    (hi : i < p.length) (h0 : p[i] ≠ 0) (hj : j + 1 < MAXOBJ)
    (hstep : compStep p.toArray i j bidx re buf p[i] = (some (i', b', re', buf'), 0))
    (hi' : i' < p.length) (h0' : p[i'] ≠ 0) :
    compLoop p.toArray i j bidx re buf 0 = compLoop p.toArray (i' + 1) (j + 1) b' re' buf' 0 := by
  rw [compLoop_step (by simpa using hi) (by simpa using h0) hj]
  simp only [List.getElem_toArray] at hstep ⊢
  rw [hstep]
  simp only [rd_toArray_lt hi', h0', Nat.or_zero, ite_false]

/-- A pass that only sets the type of entry `j` to a non-class kind `t` (meta characters,
escaped classes) and leaves `i' = i + d` at a non-NUL character. -/
theorem reInv_set {p : List Nat} {i j bidx : Int} {re : Array Tok} {buf : Array Nat}
    {rc cb : List Val} (hrc : re.toList.map tokVal = rc)
    (hcb : buf.toList.map (fun b : Nat => Val.int (b : Int)) = cb)
    (hinv : CompInv j.toNat bidx.toNat re buf)
    (hcont : compLoop p.toArray i.toNat j.toNat bidx.toNat re buf 0 = compile p.toArray)
    (_hi : 0 ≤ i) (hj : 0 ≤ j) (hj1 : j + 1 < 30) (hip : i.toNat < p.length)
    (h0 : p[i.toNat] ≠ 0) (t : Tok) (i' : Nat) (hi' : i' < p.length) (h0' : p[i'] ≠ 0)
    (hstep : compStep p.toArray i.toNat j.toNat bidx.toNat re buf p[i.toNat] =
      (some (i', bidx.toNat, re.set! j.toNat t, buf), 0)) :
    ReInv p ((i' : Int) + 1) (j + 1) bidx cb (rc.set j.toNat (tokVal t)) := by
  have hj30 : j.toNat + 1 < MAXOBJ := by simp only [MAXOBJ]; omega
  refine ⟨re.set! j.toNat t, buf, ?_, hcb.symm, ?_, ?_⟩
  · rw [map_toList_set!, hrc]
  · rw [toNat_add_one hj]
    exact compInv_step hinv hj30 (by rw [hstep])
  · rw [toNat_add_one hj, show ((i' : Int) + 1).toNat = i' + 1 by omega, ← hcont]
    exact (compLoop_cont hip h0 hj30 hstep hi' h0').symm

/-- The invariant at loop entry. -/
theorem reInv_start (p : List Nat) :
    ReInv p 0 0 1 (List.replicate 40 (.int 0))
      (List.replicate 30 (.agg [.int 0, .agg [.int 0, .undef]])) := by
  refine ⟨Array.replicate MAXOBJ {}, Array.replicate MAXCCL 0, ?_, ?_, compInv_start, rfl⟩
  · have := reVal_zero; simp only [reVal, Val.arr.injEq] at this; exact this.symm
  · have := bufVal_zero; simp only [bufVal, Val.arr.injEq] at this; exact this.symm

/-- The pattern list at a character before the NUL. -/
theorem ws_get {p : List Nat} {ws : List Val} (hws : (p ++ [0]).map (fun b => Val.int (sc b)) = ws)
    {k : Nat} (hk : k < p.length) (h : k < ws.length) : ws[k] = Val.int (sc p[k]) := by
  subst hws
  simp only [List.getElem_map]
  rw [List.getElem_append_left hk]

/-- The pattern list at the NUL. -/
theorem ws_get_end {p : List Nat} {ws : List Val} (hws : (p ++ [0]).map (fun b => Val.int (sc b)) = ws)
    {k : Nat} (hk : k = p.length) (h : k < ws.length) : ws[k] = Val.int 0 := by
  subst hws hk; simp [sc]

/-- `re_compiled[j]` before it is written: the zero entry. -/
theorem rc_get_j {re : Array Tok} {rc : List Val} (hrc : re.toList.map tokVal = rc) {j : Nat} {bidx : Nat}
    {buf : Array Nat} (hinv : CompInv j bidx re buf) (hj : j < 30) (h : j < rc.length) :
    rc[j] = Val.agg [.int 0, .agg [.int 0, .undef]] := by
  subst hrc
  have hsz : j < re.size := by rw [hinv.1]; exact hj
  have h0 : re[j]! = {} := hinv.2.2.1 j (Nat.le_refl _) hj
  rw [getElem!_pos re j hsz] at h0
  simp [h0, tokVal_default]

/-- A pass of the loop body that sets entry `j` to type `K` (a non-class kind) and leaves `i`
at the same, non-NUL character: the meta characters `^ $ . * + ?`. -/
theorem reInv_meta {p : List Nat} {i j bidx : Int} {re : Array Tok} {buf : Array Nat}
    {rc cb : List Val} (hrc : re.toList.map tokVal = rc)
    (hcb : buf.toList.map (fun b : Nat => Val.int (b : Int)) = cb)
    (hinv : CompInv j.toNat bidx.toNat re buf)
    (hcont : compLoop p.toArray i.toNat j.toNat bidx.toNat re buf 0 = compile p.toArray)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hj1 : j + 1 < 30) (hip : i.toNat < p.length)
    {c : Nat} (hb : p[i.toNat] = c) (hc0 : c ≠ 0) (K : Nat) (hK : isClassKind K = false) (Kv : Int)
    (hKv : Kv = K)
    (hstep : compStep p.toArray i.toNat j.toNat bidx.toNat re buf c =
      (some (i.toNat, bidx.toNat, re.set! j.toNat { re[j.toNat]! with type := K }, buf), 0)) :
    ReInv p (i + 1) (j + 1) bidx cb (rc.set j.toNat (Val.agg [Val.int Kv, Val.agg [Val.int 0, Val.undef]])) := by
  have hsz : j.toNat < re.size := by rw [hinv.1]; simp only [MAXOBJ]; omega
  have hrj : re[j.toNat]! = {} := hinv.2.2.1 j.toNat (Nat.le_refl _) (by simp only [MAXOBJ]; omega)
  have htv : tokVal { re[j.toNat]! with type := K } = Val.agg [Val.int Kv, Val.agg [Val.int 0, Val.undef]] := by
    rw [hrj, hKv]; simp [tokVal, hK]
  rw [← htv, show i + 1 = ((i.toNat : Nat) : Int) + 1 by omega]
  exact reInv_set hrc hcb hinv hcont hi hj hj1 hip (by rw [hb]; exact hc0) _ i.toNat hip
    (by rw [hb]; exact hc0) (by rw [hb]; exact hstep)

/-- A pass that sets entry `j` to `type := K, ch := ch` (a non-class kind; `CHAR` sets `ch`) and
continues at `i' + 1`, where the model's step returns index `i'` (pointing at a non-NUL byte). -/
theorem reInv_tok {p : List Nat} {i j bidx : Int} {re : Array Tok} {buf : Array Nat}
    {rc cb : List Val} (hrc : re.toList.map tokVal = rc)
    (hcb : buf.toList.map (fun b : Nat => Val.int (b : Int)) = cb)
    (hinv : CompInv j.toNat bidx.toNat re buf)
    (hcont : compLoop p.toArray i.toNat j.toNat bidx.toNat re buf 0 = compile p.toArray)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hj1 : j + 1 < 30) (hip : i.toNat < p.length)
    {c : Nat} (hb : p[i.toNat] = c) (hc0 : c ≠ 0) (K ch : Nat) (hK : isClassKind K = false)
    (Kv chv : Int) (hKv : Kv = K) (hchv : chv = ch) (i' : Nat) (hi' : i' < p.length) (h0' : p[i'] ≠ 0)
    (inew : Int) (hinew : inew = (i' : Int) + 1)
    (hstep : compStep p.toArray i.toNat j.toNat bidx.toNat re buf c =
      (some (i', bidx.toNat, re.set! j.toNat { re[j.toNat]! with type := K, ch := ch }, buf), 0)) :
    ReInv p inew (j + 1) bidx cb (rc.set j.toNat (Val.agg [Val.int Kv, Val.agg [Val.int chv, Val.undef]])) := by
  have htv : tokVal { re[j.toNat]! with type := K, ch := ch } =
      Val.agg [Val.int Kv, Val.agg [Val.int chv, Val.undef]] := by
    rw [hKv, hchv]; simp [tokVal, hK]
  rw [← htv, hinew]
  exact reInv_set hrc hcb hinv hcont hi hj hj1 hip (by rw [hb]; exact hc0) _ i' hi' h0'
    (by rw [hb]; exact hstep)

/-- At a loop exit: what `re_compile` then returns, by the model. -/
theorem exit_facts {p : List Nat} {i j bidx : Int} {re : Array Tok} {buf : Array Nat}
    {rc cb : List Val} (hrc : re.toList.map tokVal = rc)
    (hcb : buf.toList.map (fun b : Nat => Val.int (b : Int)) = cb)
    (hinv : CompInv j.toNat bidx.toNat re buf)
    (hcont : compLoop p.toArray i.toNat j.toNat bidx.toNat re buf 0 = compile p.toArray)
    (_hi : 0 ≤ i) (hip : i ≤ p.length) (hj : 0 ≤ j) (hj1 : j < 30)
    (hex : (rd p.toArray i.toNat).1 = 0 ∨ MAXOBJ ≤ j.toNat + 1) :
    (compile p.toArray).1 = some (re.set! j.toNat { re[j.toNat]! with type := UNUSED }, buf) ∧
    reVal (re.set! j.toNat { re[j.toNat]! with type := UNUSED }) =
      .arr (rc.set j.toNat (.agg [.int 0, .agg [.int 0, .undef]])) ∧
    bufVal buf = .arr cb := by
  have hrj : re[j.toNat]! = {} := hinv.2.2.1 j.toNat (Nat.le_refl _) (by simp only [MAXOBJ]; omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcont, compLoop_exit (by simp; omega) hex]
  · rw [reVal, map_toList_set!, hrc, hrj]; simp [tokVal, isClassKind, UNUSED, CHAR_CLASS, INV_CHAR_CLASS]
  · rw [bufVal, hcb]

/-- A pass that writes nothing (`\` as the last byte) and continues at `i + 1`. -/
theorem reInv_skip {p : List Nat} {i j bidx : Int} {re : Array Tok} {buf : Array Nat}
    {rc cb : List Val} (hrc : re.toList.map tokVal = rc)
    (hcb : buf.toList.map (fun b : Nat => Val.int (b : Int)) = cb)
    (hinv : CompInv j.toNat bidx.toNat re buf)
    (hcont : compLoop p.toArray i.toNat j.toNat bidx.toNat re buf 0 = compile p.toArray)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hj1 : j + 1 < 30) (hip : i.toNat < p.length)
    {c : Nat} (hb : p[i.toNat] = c) (hc0 : c ≠ 0)
    (hstep : compStep p.toArray i.toNat j.toNat bidx.toNat re buf c =
      (some (i.toNat, bidx.toNat, re, buf), 0)) :
    ReInv p (i + 1) (j + 1) bidx cb rc := by
  have hj30 : j.toNat + 1 < MAXOBJ := by simp only [MAXOBJ]; omega
  refine ⟨re, buf, hrc.symm, hcb.symm, ?_, ?_⟩
  · rw [toNat_add_one hj]
    exact compInv_step hinv hj30 (by rw [hstep])
  · rw [toNat_add_one hj, toNat_add_one hi, ← hcont]
    exact (compLoop_cont hip (by rw [hb]; exact hc0) hj30 (by rw [hb]; exact hstep) hip
      (by rw [hb]; exact hc0)).symm

/-! ## Character classes -/

/-- Where the copy of a class at `i` starts, and its kind: after `[` (`CHAR_CLASS`), or after
`[^` when a byte follows the `^` (`INV_CHAR_CLASS`). -/
def ClassStart (p : List Nat) (i iS K : Nat) : Prop :=
  (iS = i ∧ K = CHAR_CLASS ∧ (rd p.toArray (i + 1)).1 ≠ 94) ∨
    (iS = i + 1 ∧ K = INV_CHAR_CLASS ∧ (rd p.toArray (i + 1)).1 = 94 ∧ (rd p.toArray (i + 2)).1 ≠ 0)

theorem set!_set!_ccl {re : Array Tok} {j : Nat} (hj : j < re.size) (x : Tok) (b : Nat) :
    (re.set! j x).set! j { (re.set! j x)[j]! with ccl := b } = re.set! j { x with ccl := b } := by
  rw [Array.getElem!_set!_self _ _ _ hj]
  simp [Array.set!_eq_setIfInBounds]

/-- The pass for `[` at `i`: the copy from `iS`, then the NUL terminator and `u.ccl := begin`. -/
theorem compStep_class {p : List Nat} {i j bidx : Nat} {re : Array Tok} {buf : Array Nat}
    {iS K : Nat} (hS : ClassStart p i iS K) (hi : i < p.length) (hj : j < re.size) :
    compStep p.toArray i j bidx re buf 91 =
      match cclCopy p.toArray iS bidx buf with
      | (none, u) => (none, u)
      | (some (i', b', bufA), u) =>
        if b' ≥ MAXCCL then (none, u)
        else (some (i', b' + 1, re.set! j { re[j]! with type := K, ccl := bidx }, bufA.set! b' 0), u) := by
  have hu1 : rd p.toArray (i + 1) = ((rd p.toArray (i + 1)).1, 0) :=
    Prod.ext rfl (rd_snd_of_le (by simp; omega))
  unfold compStep
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_left (by decide), hu1]
  dsimp only
  rcases hS with ⟨rfl, rfl, h1⟩ | ⟨rfl, rfl, h1, h2⟩
  · rw [ite_eq_right (by simpa using h1)]
    rcases cclCopy p.toArray iS bidx buf with ⟨_ | ⟨i', b', bufA⟩, u⟩
    · simp
    · dsimp only
      by_cases hb : b' ≥ MAXCCL
      · rw [ite_eq_left hb, ite_eq_left hb]; simp
      · rw [ite_eq_right hb, ite_eq_right hb, set!_set!_ccl hj]; simp
  · have hu2 : rd p.toArray (i + 2) = ((rd p.toArray (i + 2)).1, 0) := by
      refine Prod.ext rfl (rd_snd_of_le ?_)
      have := lt_size_of_rd_ne_zero (p := p.toArray) (i := i + 1) (by rw [h1]; decide)
      simp at this ⊢; omega
    rw [ite_eq_left (by simpa using h1), hu2]
    dsimp only
    rw [ite_eq_right (by simpa using h2)]
    rcases cclCopy p.toArray (i + 1) bidx buf with ⟨_ | ⟨i', b', bufA⟩, u⟩
    · simp
    · dsimp only
      by_cases hb : b' ≥ MAXCCL
      · rw [ite_eq_left hb, ite_eq_left hb]; simp
      · rw [ite_eq_right hb, ite_eq_right hb, set!_set!_ccl hj]; simp

/-- `[` followed by `^` and the NUL: `return 0`. -/
theorem class_caret_nul {p : List Nat} {i j bidx : Nat} {re : Array Tok} {buf : Array Nat}
    (hcont : compLoop p.toArray i j bidx re buf 0 = compile p.toArray)
    (hi : i < p.length) (hb : p[i] = 91) (hj : j + 1 < MAXOBJ)
    (h1 : (rd p.toArray (i + 1)).1 = 94) (h2 : i + 2 = p.length) :
    (compile p.toArray).1 = none := by
  have hu1 : rd p.toArray (i + 1) = (94, 0) := Prod.ext h1 (rd_snd_of_le (by simp; omega))
  have hu2 : rd p.toArray (i + 2) = (0, 0) := by rw [h2]; exact rd_toArray_end
  rw [← hcont, compLoop_step (by simpa using hi) (by simp [hb]) hj]
  simp only [List.getElem_toArray, hb]
  unfold compStep
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_left (by decide), hu1]
  dsimp only
  rw [hu2]
  rfl

/-- A class at `i` whose copy fails: `return 0`. -/
theorem class_none {p : List Nat} {i j bidx : Nat} {re : Array Tok} {buf : Array Nat} {iS K : Nat}
    (hcont : compLoop p.toArray i j bidx re buf 0 = compile p.toArray)
    (hS : ClassStart p i iS K) (hi : i < p.length) (hb : p[i] = 91) (hj : j + 1 < MAXOBJ)
    (hjs : j < re.size) (hcc : (cclCopy p.toArray iS bidx buf).1 = none) :
    (compile p.toArray).1 = none := by
  rw [← hcont, compLoop_step (by simpa using hi) (by simp [hb]) hj]
  simp only [List.getElem_toArray, hb]
  rw [compStep_class hS hi hjs]
  rcases h : cclCopy p.toArray iS bidx buf with ⟨_ | ⟨i', b', bufA⟩, u⟩
  · rfl
  · rw [h] at hcc; cases hcc

/-- A class whose copy fills `ccl_buf`: `return 0`. -/
theorem class_full {p : List Nat} {i j bidx : Nat} {re : Array Tok} {buf : Array Nat} {iS K : Nat}
    (hcont : compLoop p.toArray i j bidx re buf 0 = compile p.toArray)
    (hS : ClassStart p i iS K) (hi : i < p.length) (hb : p[i] = 91) (hj : j + 1 < MAXOBJ)
    (hjs : j < re.size) {i' b' : Nat} {bufA : Array Nat} {u : Nat}
    (hcc : cclCopy p.toArray iS bidx buf = (some (i', b', bufA), u)) (hb' : MAXCCL ≤ b') :
    (compile p.toArray).1 = none := by
  rw [← hcont, compLoop_step (by simpa using hi) (by simp [hb]) hj]
  simp only [List.getElem_toArray, hb]
  rw [compStep_class hS hi hjs, hcc]
  dsimp only
  rw [ite_eq_left hb']

/-- A class ended by the NUL (no `]`): `if (pattern[i] == 0) return 0;`. -/
theorem class_nul {p : List Nat} {i j bidx : Nat} {re : Array Tok} {buf : Array Nat} {iS K : Nat}
    (hcont : compLoop p.toArray i j bidx re buf 0 = compile p.toArray)
    (hS : ClassStart p i iS K) (hi : i < p.length) (hb : p[i] = 91) (hj : j + 1 < MAXOBJ)
    (hjs : j < re.size) {i' b' : Nat} {bufA : Array Nat} {u : Nat}
    (hcc : cclCopy p.toArray iS bidx buf = (some (i', b', bufA), u)) (hb' : b' < MAXCCL)
    (hz : i' = p.length) : (compile p.toArray).1 = none := by
  subst hz
  rw [← hcont, compLoop_step (by simpa using hi) (by simp [hb]) hj]
  simp only [List.getElem_toArray, hb]
  rw [compStep_class hS hi hjs, hcc]
  dsimp only
  rw [ite_eq_right (by omega)]
  dsimp only
  rw [rd_toArray_end]
  rfl

/-- A class `[..]` (or `[^..]`) of kind `K` at `i`, copied by the model as `cclCopy … = some (i',
b', bufA)` with `i'` at the closing `]`: entry `j` gets `type := K` and `u.ccl := &ccl_buf[bidx]`,
`ccl_buf` gets the NUL at `b'`, and the loop goes on at `i' + 1`. -/
theorem reInv_class {p : List Nat} {i j bidx : Int} {re : Array Tok} {buf : Array Nat}
    {rc : List Val} (hrc : re.toList.map tokVal = rc) (hinv : CompInv j.toNat bidx.toNat re buf)
    (hcont : compLoop p.toArray i.toNat j.toNat bidx.toNat re buf 0 = compile p.toArray)
    (hj : 0 ≤ j) (hj1 : j + 1 < 30) (hip : i.toNat < p.length) (hb : p[i.toNat] = 91)
    {iS K : Nat} (hS : ClassStart p i.toNat iS K) (hK : isClassKind K = true) (Kv : Int)
    (hKv : Kv = K) {i' b' : Nat} {bufA : Array Nat}
    (hcc : cclCopy p.toArray iS bidx.toNat buf = (some (i', b', bufA), 0)) (hb' : b' < MAXCCL)
    (hi' : i' < p.length) (h0' : p[i'] ≠ 0) (cbA : List Val)
    (hcbA : bufA.toList.map (fun b : Nat => Val.int (b : Int)) = cbA)
    (inew bnew : Int) (hinew : inew = (i' : Int) + 1) (hbnew : bnew = (b' : Int) + 1)
    (bk : Nat) (hbk : bk = b') (bi : Nat) (hbi : bi = bidx.toNat) :
    ReInv p inew (j + 1) bnew (cbA.set bk (.int 0))
      (rc.set j.toNat (.agg [.int Kv, .agg [.undef, .ptr (.loc bCcl [.idx bi])]])) := by
  subst inew bnew bk bi Kv
  have hj30 : j.toNat + 1 < MAXOBJ := by simp only [MAXOBJ]; omega
  have hjs : j.toNat < re.size := by rw [hinv.1]; omega
  have hstep : compStep p.toArray i.toNat j.toNat bidx.toNat re buf p[i.toNat] =
      (some (i', b' + 1, re.set! j.toNat { re[j.toNat]! with type := K, ccl := bidx.toNat },
        bufA.set! b' 0), 0) := by
    rw [hb, compStep_class hS hip hjs, hcc]; dsimp only; rw [ite_eq_right (by omega)]
  have htv : tokVal { re[j.toNat]! with type := K, ccl := bidx.toNat } =
      .agg [.int K, .agg [.undef, .ptr (.loc bCcl [.idx bidx.toNat])]] := by
    simp [tokVal, hK]
  refine ⟨re.set! j.toNat { re[j.toNat]! with type := K, ccl := bidx.toNat }, bufA.set! b' 0,
    ?_, ?_, ?_, ?_⟩
  · rw [map_toList_set!, hrc, htv]
  · rw [map_toList_set!, hcbA]; rfl
  · rw [toNat_add_one hj, show ((b' : Int) + 1).toNat = b' + 1 by omega]
    exact compInv_step hinv hj30 (by rw [hstep])
  · rw [toNat_add_one hj, show ((i' : Int) + 1).toNat = i' + 1 by omega,
      show ((b' : Int) + 1).toNat = b' + 1 by omega, ← hcont]
    exact (compLoop_cont hip (by rw [hb]; decide) hj30 hstep hi' h0').symm

/-! ### The `[..]` copy loop -/

/-- The state of the copy loop `while ((pattern[++i] != ']') && (pattern[i] != '\0'))` behind its
variables `i`, `ccl_bufidx` and `ccl_buf`'s elements `cb`: the model's copy from here gives what
the copy from its start (`iS`, `bS`, `buf0`) gives.  A definition, as `ReInv`. -/
def CclInv (p : List Nat) (iS bS : Nat) (buf0 : Array Nat) (i bidx : Int) (cb : List Val) : Prop :=
  ∃ bufA : Array Nat, cb = bufA.toList.map (fun b : Nat => Val.int (b : Int)) ∧
    bufA.size = MAXCCL ∧ cclCopy p.toArray i.toNat bidx.toNat bufA = cclCopy p.toArray iS bS buf0

theorem cclInv_start {p : List Nat} {buf0 : Array Nat} {cb : List Val}
    (hcb : buf0.toList.map (fun b : Nat => Val.int (b : Int)) = cb) (hsz : buf0.size = MAXCCL)
    {iS bS : Nat} (i bidx : Int) (hi : i.toNat = iS) (hb : bidx.toNat = bS) :
    CclInv p iS bS buf0 i bidx cb := by
  subst hi hb; exact ⟨buf0, hcb.symm, hsz, rfl⟩

/-- A byte other than `\`, `]` and the NUL: copied. -/
theorem cclInv_char {p : List Nat} {iS bS : Nat} {buf0 : Array Nat} {i bidx : Int} {cb : List Val}
    (h : CclInv p iS bS buf0 i bidx cb) (hi : 0 ≤ i) (hb : 0 ≤ bidx) (hb40 : bidx < 40)
    (hk : i.toNat + 1 < p.length) {c : Nat} (hc : p[i.toNat + 1] = c) (hc0 : c ≠ 0)
    (hc92 : c ≠ 92) (hc93 : c ≠ 93) :
    CclInv p iS bS buf0 (i + 1) (bidx + 1) (cb.set bidx.toNat (.int c)) := by
  obtain ⟨bufA, rfl, hsz, hcc⟩ := h
  refine ⟨bufA.set! bidx.toNat c, ?_, by simp [hsz], ?_⟩
  · rw [map_toList_set!]
  · rw [toNat_add_one hi, toNat_add_one hb, ← hcc,
      cclCopy_char (i := i.toNat) (bidx := bidx.toNat) (buf := bufA) (by simpa using hk)
        (by simpa [hc] using hc0) (by simpa [hc] using hc92) (by simpa [hc] using hc93)
        (by simp only [MAXCCL]; omega)]
    simp [hc]

/-- `\` and the byte after it: both copied. -/
theorem cclInv_esc {p : List Nat} {iS bS : Nat} {buf0 : Array Nat} {i bidx : Int} {cb : List Val}
    (h : CclInv p iS bS buf0 i bidx cb) (hi : 0 ≤ i) (hb : 0 ≤ bidx) (hb39 : bidx < 39)
    (hk : i.toNat + 2 < p.length) (hc : p[i.toNat + 1] = 92) {c2 : Nat}
    (hc2 : p[i.toNat + 2] = c2) (hc20 : c2 ≠ 0) :
    CclInv p iS bS buf0 (i + 2) (bidx + 2)
      ((cb.set bidx.toNat (.int 92)).set (bidx + 1).toNat (.int c2)) := by
  obtain ⟨bufA, rfl, hsz, hcc⟩ := h
  refine ⟨(bufA.set! bidx.toNat 92).set! (bidx.toNat + 1) c2, ?_, by simp [hsz], ?_⟩
  · rw [map_toList_set!, map_toList_set!, toNat_add_one hb]; rfl
  · rw [show (i + 2).toNat = i.toNat + 2 by omega, show (bidx + 2).toNat = bidx.toNat + 2 by omega,
      ← hcc,
      cclCopy_esc (i := i.toNat) (bidx := bidx.toNat) (buf := bufA) (by simpa using hk)
        (by simpa using hc) (by simp only [MAXCCL]; omega) (by simpa [hc2] using hc20)]
    simp [hc2]

/-- `\` with fewer than two free bytes in `ccl_buf`: the copy fails. -/
theorem cclInv_esc_full {p : List Nat} {iS bS : Nat} {buf0 : Array Nat} {i bidx : Int}
    {cb : List Val} (h : CclInv p iS bS buf0 i bidx cb) (hk : i.toNat + 1 < p.length)
    (hc : p[i.toNat + 1] = 92) (hb39 : 39 ≤ bidx) : (cclCopy p.toArray iS bS buf0).1 = none := by
  obtain ⟨bufA, rfl, _, hcc⟩ := h
  rw [← hcc, cclCopy_esc_full (i := i.toNat) (bidx := bidx.toNat) (buf := bufA)
    (by simpa using hk) (by simpa using hc) (by simp only [MAXCCL]; omega)]

/-- `\` as the last byte of the pattern: the copy fails. -/
theorem cclInv_esc_end {p : List Nat} {iS bS : Nat} {buf0 : Array Nat} {i bidx : Int}
    {cb : List Val} (h : CclInv p iS bS buf0 i bidx cb) (hb : 0 ≤ bidx)
    (hk : i.toNat + 1 < p.length) (hc : p[i.toNat + 1] = 92) (hb39 : bidx < 39)
    (he : i.toNat + 2 = p.length) : (cclCopy p.toArray iS bS buf0).1 = none := by
  obtain ⟨bufA, rfl, _, hcc⟩ := h
  rw [← hcc, cclCopy_esc_end (i := i.toNat) (bidx := bidx.toNat) (buf := bufA)
    (by simpa using hk) (by simpa using hc) (by simp only [MAXCCL]; omega) (by simpa using he)]

/-- Another byte with `ccl_buf` full: the copy fails. -/
theorem cclInv_full {p : List Nat} {iS bS : Nat} {buf0 : Array Nat} {i bidx : Int} {cb : List Val}
    (h : CclInv p iS bS buf0 i bidx cb) (hk : i.toNat + 1 < p.length) {c : Nat}
    (hc : p[i.toNat + 1] = c) (hc0 : c ≠ 0) (hc92 : c ≠ 92) (hc93 : c ≠ 93) (hb40 : 40 ≤ bidx) :
    (cclCopy p.toArray iS bS buf0).1 = none := by
  obtain ⟨bufA, rfl, _, hcc⟩ := h
  rw [← hcc, cclCopy_full (i := i.toNat) (bidx := bidx.toNat) (buf := bufA) (by simpa using hk)
    (by simpa [hc] using hc0) (by simpa [hc] using hc92) (by simpa [hc] using hc93)
    (by simp only [MAXCCL]; omega)]

/-- `]`: the copy ends there. -/
theorem cclInv_stop {p : List Nat} {iS bS : Nat} {buf0 : Array Nat} {i bidx : Int} {cb : List Val}
    (h : CclInv p iS bS buf0 i bidx cb) (hk : i.toNat + 1 < p.length) (hc : p[i.toNat + 1] = 93) :
    ∃ bufA : Array Nat, bufA.toList.map (fun b : Nat => Val.int (b : Int)) = cb ∧
      cclCopy p.toArray iS bS buf0 = (some (i.toNat + 1, bidx.toNat, bufA), 0) := by
  obtain ⟨bufA, rfl, _, hcc⟩ := h
  exact ⟨bufA, rfl, by rw [← hcc, cclCopy_stop (by simpa using hk) (Or.inl (by simpa using hc))]⟩

/-- The NUL (no `]`): the copy ends there. -/
theorem cclInv_nul {p : List Nat} {iS bS : Nat} {buf0 : Array Nat} {i bidx : Int} {cb : List Val}
    (h : CclInv p iS bS buf0 i bidx cb) (hk : i.toNat + 1 = p.length) :
    ∃ bufA : Array Nat, bufA.toList.map (fun b : Nat => Val.int (b : Int)) = cb ∧
      cclCopy p.toArray iS bS buf0 = (some (i.toNat + 1, bidx.toNat, bufA), 0) := by
  obtain ⟨bufA, rfl, _, hcc⟩ := h
  exact ⟨bufA, rfl, by rw [← hcc, cclCopy_last (by simpa using hk)]⟩

end EquivLean.Demo.XLang.TinyRegex.C
