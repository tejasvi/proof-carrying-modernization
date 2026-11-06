import EquivLean.Demo.XLang.Jsmn.RustPrim

/-!
# jsmn → model, Rust side: one turn of `jsmn_parse`'s loop

`Inv` is the loop invariant on the Rust state (parser, token array, `count`); `StepPost` relates
the Rust state after one loop turn to the model's `step`.  One lemma per byte class (whitespace,
`:`, `,`, a closing bracket, an opening bracket, a quote, a primitive's first byte), then
`body_step` for every live byte.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas jsmn_rs

namespace EquivLean.Demo.XLang.Jsmn.Rust

/-- Closes a branch with a hypothesis `false = true` (cheaper than `contradiction`, which can
unfold the model's searches in the other hypotheses). -/
macro "rust_contra" : tactic => `(tactic| first
  | exact absurd ‹false = true› Bool.false_ne_true
  | exact absurd trivial ‹¬True›)

/-- A loop body whose outcome satisfies `∃ v, r = .ok (.cont v) ∧ P v` continues with such a `v`. -/
theorem exists_cont_of_wp {α β : Type} {c : Result (ControlFlow α β)} {P : α → Prop}
    (h : wp c (fun r => ∃ v, r = .ok (.cont v) ∧ P v)) :
    ∃ v, c = Result.ok (.cont v) ∧ P v := by
  rcases (wp_iff _ _).1 h with ⟨a, rfl, ha⟩ | ⟨e, rfl, he⟩
  · obtain ⟨v, hv, hp⟩ := ha
    cases hv
    exact ⟨_, rfl, hp⟩
  · simp at he

/-! ## The invariant -/

/-- The loop invariant of `jsmn_parse`: the source is short, `pos ≤ len`, the filled tokens fit
in the array and are no more than the bytes read, `-1 ≤ toksuper < toknext`, every filled token's
size is at most `toknext` (so `size + 1` does not overflow), and `count = toknext`. -/
def Inv (js : Slice U8) (p : JsmnParser) (ts : Slice JsmnTok) (count : I32) : Prop :=
  js.val.length < 2 ^ 28 ∧ p.pos.val ≤ js.val.length ∧ p.toknext.val ≤ ts.val.length ∧
  p.toknext.val ≤ p.pos.val ∧ -1 ≤ p.toksuper.val ∧ p.toksuper.val < p.toknext.val ∧
  (∀ t ∈ mtoks ts p.toknext.val, t.size ≤ p.toknext.val) ∧ count.val = p.toknext.val

/-- One loop turn against the model's `step` outcome `o`: on an error the loop stops with the
error code; otherwise it continues (`stop = false`) in a state whose model view is the model's
new state, the invariant holds, the array keeps its length `n` and `pos` moved forward. -/
def StepPost (js : Slice U8) (n : Nat) (p : JsmnParser) (o : Except Int St)
    (v : JsmnParser × Slice JsmnTok × I32 × I32 × Bool) : Prop :=
  match o with
  | .error e => v.2.2.2.2 = true ∧ v.2.2.2.1.val = e ∧ e < 0
  | .ok st => v.2.2.2.2 = false ∧ absSt v.1 v.2.1 = st ∧ Inv js v.1 v.2.1 v.2.2.1 ∧
      v.2.1.val.length = n ∧ p.pos.val < v.1.pos.val

theorem stepPost_ok {js : Slice U8} {n : Nat} {p : JsmnParser} {st : St} {p' : JsmnParser}
    {ts' : Slice JsmnTok} {count' ret' : I32} (habs : absSt p' ts' = st) (hinv : Inv js p' ts' count')
    (hn : ts'.val.length = n) (hpos : p.pos.val < p'.pos.val) :
    StepPost js n p (.ok st) (p', ts', count', ret', false) :=
  ⟨rfl, habs, hinv, hn, hpos⟩

theorem stepPost_err {js : Slice U8} {n : Nat} {p : JsmnParser} {e : Int} {p' : JsmnParser}
    {ts' : Slice JsmnTok} {count' ret' : I32} (hr : ret'.val = e) (he : e < 0) :
    StepPost js n p (.error e) (p', ts', count', ret', true) :=
  ⟨rfl, hr, he⟩

/-! ## Token list facts -/

theorem mtoks_mem {ts : Slice JsmnTok} {k j : Nat} (hj : j < k) (hk : k ≤ ts.val.length) :
    toTok (ts.val[j]'(by omega)) ∈ mtoks ts k := by
  rw [List.mem_iff_getElem]
  refine ⟨j, by rw [mtoks_length hk]; exact hj, ?_⟩
  simp [mtoks]

theorem size_le {ts : Slice JsmnTok} {k j : Nat} {B : Int} (h : ∀ t ∈ mtoks ts k, t.size ≤ B)
    (hj : j < k) (hk : k ≤ ts.val.length) : (ts.val[j]'(by omega)).size.val ≤ B :=
  h _ (mtoks_mem hj hk)

theorem sizes_append {l : List Tok} {B : Int} {t : Tok} (h : ∀ u ∈ l, u.size ≤ B) (ht : t.size ≤ B) :
    ∀ u ∈ l ++ [t], u.size ≤ B := by
  intro u hu
  rcases List.mem_append.1 hu with hu | hu
  · exact h u hu
  · simp at hu
    subst hu
    exact ht

theorem sizes_incSize {l : List Tok} {B : Int} (h : ∀ u ∈ l, u.size ≤ B) (i : Nat) :
    ∀ u ∈ incSize l i, u.size ≤ B + 1 := by
  intro u hu
  unfold incSize at hu
  rw [List.mem_iff_getElem] at hu
  obtain ⟨j, hj, rfl⟩ := hu
  rw [List.getElem_modify]
  have hj' : j < l.length := by simpa using hj
  have := h _ (List.getElem_mem hj')
  split_ifs
  · simp only
    omega
  · omega

theorem sizes_bumpSup {l : List Tok} {B : Int} (h : ∀ u ∈ l, u.size ≤ B) (sup : Int) :
    ∀ u ∈ bumpSup l sup, u.size ≤ B + 1 := by
  unfold bumpSup
  split_ifs
  · intro u hu
    have := h u hu
    omega
  · exact sizes_incSize h _

/-- `tokens[i].size += 1` on a slice: `incSize` of the model's view. -/
theorem mtoks_bump (X : Slice JsmnTok) (i : Usize) (j k : Nat) (hij : i.val = j) (hj : j < k)
    (hk : k ≤ X.val.length) (sz : I32) (hsz : sz.val = (X.val[j]'(by omega)).size.val + 1) :
    mtoks (X.set i { X.val[j]'(by omega) with size := sz }) k = incSize (mtoks X k) j := by
  rw [mtoks_set_lt]
  unfold incSize
  apply List.ext_getElem
  · simp
  · intro m h1 h2
    rw [List.getElem_modify, List.getElem_set]
    simp only [hij]
    split_ifs with h3
    · subst h3
      simp [mtoks, toTok, hsz]
    · rfl

theorem slice_set_len {α : Type} (s : Slice α) (i : Usize) (x : α) :
    (s.set i x).val.length = s.val.length := by
  simp [Slice.set_val_eq]

theorem slice_set_get_self {α : Type} (s : Slice α) (i : Usize) (x : α)
    (h : i.val < (s.set i x).val.length) : (s.set i x).val[i.val]'h = x := by
  simp [Slice.set_val_eq]

theorem slice_set_get_ne {α : Type} (s : Slice α) (i : Usize) (x : α) (j : Nat) (hij : i.val ≠ j)
    (h : j < (s.set i x).val.length) :
    (s.set i x).val[j]'h = s.val[j]'(by rw [slice_set_len] at h; exact h) := by
  simp [Slice.set_val_eq, List.getElem_set_ne hij]

/-- In-bounds slice accesses as plain values (`simp` rules whose bound is left to the
discharger, so no branch on the bound appears). -/
theorem slice_index_mut_ok {α : Type} {s : Slice α} {i : Usize} (h : i.val < s.val.length) :
    Slice.index_mut_usize s i = .ok (s.val[i.val], Slice.set s i) := by
  rw [slice_index_mut_usize_eq, dif_pos h]

theorem slice_index_ok {α : Type} {s : Slice α} {i : Usize} (h : i.val < s.val.length) :
    Slice.index_usize s i = .ok (s.val[i.val]) := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq, List.getElem?_eq_getElem h]

/-- `mtoks_bump` with the new size as the generated code computes it (a `simp` rule). -/
theorem mtoks_bump' (X : Slice JsmnTok) (i : Usize) (j k : Nat) (hij : i.val = j) (hj : j < k)
    (hk : k ≤ X.val.length)
    (h : -2 ^ (IScalarTy.I32.numBits - 1) ≤ (X.val[j]'(by omega)).size.val + 1 ∧
      (X.val[j]'(by omega)).size.val + 1 < 2 ^ (IScalarTy.I32.numBits - 1)) :
    mtoks (X.set i { X.val[j]'(by omega) with
      size := IScalar.ofIntCore ((X.val[j]'(by omega)).size.val + 1) h }) k = incSize (mtoks X k) j :=
  mtoks_bump X i j k hij hj hk _ (by simp)

/-! ## The backward searches as `wp` rules (their start index is a computed term) -/

theorem find_open_wp (ts : Slice JsmnTok) (K : Nat) (hK : K ≤ ts.val.length) (k : Nat) (hk : k ≤ K)
    (X : I32) (hX : X.val = (k : Int) - 1) {Q : Except Error I32 → Prop}
    (hq : ∀ r : I32, r.val = optIdx (lastOpen (mtoks ts K) k) → Q (.ok r)) :
    wp (find_open ts X) Q := by
  obtain ⟨r, hr, hrv⟩ := find_open_loop_eq ts K hK k X hk hX
  unfold find_open
  rw [hr, wp_ok]
  exact hq r hrv

theorem find_open_container_wp (ts : Slice JsmnTok) (K : Nat) (hK : K ≤ ts.val.length) (X : I32)
    (hX : X.val = (K : Int) - 1) {Q : Except Error I32 → Prop}
    (hq : ∀ r : I32, r.val = optIdx (lastOpenCont (mtoks ts K) K) → Q (.ok r)) :
    wp (find_open_container ts X) Q := by
  obtain ⟨r, hr, hrv⟩ := find_open_container_loop_eq ts K hK K X (le_refl _) hX
  unfold find_open_container
  rw [hr, wp_ok]
  exact hq r hrv

theorem lastOpen_succ_closed {l : List Tok} {i : Nat} (h : isOpen (l.getD i dflt) = false) :
    lastOpen l (i + 1) = lastOpen l i := by
  simp only [lastOpen, h, Bool.false_eq_true, _root_.ite_false]

theorem lastOpen_set {l : List Tok} {i : Nat} (x : Tok) : ∀ j, j ≤ i → lastOpen (l.set i x) j = lastOpen l j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j IH =>
    intro hj
    have hg : (l.set i x).getD j dflt = l.getD j dflt := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (show i ≠ j by omega)]
    simp only [lastOpen, hg, IH (by omega)]

theorem optIdx_lastOpen_lt {l : List Tok} {k j : Nat} (h : lastOpen l k = some j) : j < k := by
  induction k with
  | zero => simp [lastOpen] at h
  | succ k IH =>
    simp only [lastOpen] at h
    split_ifs at h
    · simp at h
      omega
    · have := IH h
      omega

theorem optIdx_lastOpen_bounds (l : List Tok) (i : Nat) :
    -1 ≤ optIdx (lastOpen l i) ∧ optIdx (lastOpen l i) < i := by
  cases h : lastOpen l i with
  | none =>
    simp only [optIdx]
    omega
  | some j =>
    have := optIdx_lastOpen_lt h
    simp only [optIdx]
    omega

/-- Closing the token at `i` (setting its end) makes it not open: the search from `i + 1` in the
new list is the search from `i` in the old one. -/
theorem lastOpen_close (l : List Tok) (i : Nat) (hi : i < l.length) (y : Tok) (hy : isOpen y = false) :
    lastOpen (l.set i y) (i + 1) = lastOpen l i := by
  rw [lastOpen_succ_closed, lastOpen_set y i (le_refl _)]
  simp [List.getD_eq_getElem?_getD, hi, hy]

theorem isOpen_end_set (t : JsmnTok) (e : I32) (he : 0 ≤ e.val) :
    isOpen (toTok { t with «end» := e }) = false := by
  have : e.val ≠ -1 := by omega
  simp [isOpen, toTok, this]

theorem sizes_set {l : List Tok} {B : Int} (h : ∀ u ∈ l, u.size ≤ B) (i : Nat) (y : Tok)
    (hy : y.size ≤ B) : ∀ u ∈ l.set i y, u.size ≤ B := by
  intro u hu
  rcases List.mem_or_eq_of_mem_set hu with hu | hu
  · exact h u hu
  · subst hu
    exact hy

/-- The second search of a closing bracket: from the token just closed (index `i`, end set to
`e ≥ 0`), the model's search below `i` in the old list. -/
theorem find_open_after_close_wp (ts : Slice JsmnTok) (K : Nat) (hK : K ≤ ts.val.length) (i : Nat)
    (hi : i < K) (idx : Usize) (hidx : idx.val = i) (t : JsmnTok) (e : I32) (he : 0 ≤ e.val)
    (X : I32) (hX : X.val = i) {Q : Except Error I32 → Prop}
    (hq : ∀ r : I32, r.val = optIdx (lastOpen (mtoks ts K) i) → Q (.ok r)) :
    wp (find_open (ts.set idx { t with «end» := e }) X) Q := by
  refine find_open_wp _ K (by simp only [Slice.set_val_eq, List.length_set]; exact hK) (i + 1) hi X
    (by omega) ?_
  intro r hr
  apply hq
  rw [hr, mtoks_set_lt, hidx,
    lastOpen_close _ i (by rw [mtoks_length hK]; exact hi) _ (isOpen_end_set t e he)]

theorem lastOpenCont_lt {l : List Tok} {k j : Nat} (h : lastOpenCont l k = some j) : j < k := by
  induction k with
  | zero => simp [lastOpenCont] at h
  | succ k IH =>
    simp only [lastOpenCont] at h
    split_ifs at h
    · simp at h
      omega
    · have := IH h
      omega

/-! ## The model's step, per byte class -/

theorem step_ws {js : List Nat} {n : Nat} {st : St}
    (h : byteAt js st.pos = 9 ∨ byteAt js st.pos = 13 ∨ byteAt js st.pos = 10 ∨ byteAt js st.pos = 32) :
    step js n st = .ok ⟨st.pos + 1, st.toks, st.sup⟩ := by
  rcases h with h | h | h | h <;> simp [step, h]

theorem step_colon {js : List Nat} {n : Nat} {st : St} (h : byteAt js st.pos = 58) :
    step js n st = .ok ⟨st.pos + 1, st.toks, (st.toks.length : Int) - 1⟩ := by
  simp [step, h]

theorem step_comma {js : List Nat} {n : Nat} {st : St} (h : byteAt js st.pos = 44) :
    step js n st =
      (let t := st.toks.getD st.sup.toNat dflt
      if st.sup ≠ -1 ∧ t.type ≠ ARRAY ∧ t.type ≠ OBJECT then
        .ok ⟨st.pos + 1, st.toks,
          match lastOpenCont st.toks st.toks.length with
          | some i => i
          | none => st.sup⟩
      else .ok ⟨st.pos + 1, st.toks, st.sup⟩) := by
  (simp +decide only [step, h, ite_true, ite_false]) <;> rfl

theorem step_close {js : List Nat} {n : Nat} {st : St} (obj : Bool)
    (h : byteAt js st.pos = if obj then 125 else 93) :
    step js n st =
      match lastOpen st.toks st.toks.length with
      | none => .error ERROR_INVAL
      | some i =>
        if (st.toks.getD i dflt).type ≠ (if obj then OBJECT else ARRAY) then .error ERROR_INVAL
        else
          .ok ⟨st.pos + 1, st.toks.set i { st.toks.getD i dflt with stop := st.pos + 1 },
            optIdx (lastOpen st.toks i)⟩ := by
  cases obj <;> simp only [Bool.false_eq_true, _root_.ite_false, _root_.ite_true] at h ⊢ <;>
    ((simp +decide only [step, h, ite_true, ite_false]) <;> rfl)

theorem step_string {js : List Nat} {n : Nat} {st : St} (h : byteAt js st.pos = 34) :
    step js n st =
      match parseString js n st with
      | .error e => .error e
      | .ok st' => .ok ⟨st'.pos + 1, bumpSup st'.toks st'.sup, st'.sup⟩ := by
  (simp +decide only [step, h, ite_true, ite_false]) <;> rfl

theorem step_prim {js : List Nat} {n : Nat} {st : St}
    (h1 : ¬ (byteAt js st.pos = 123 ∨ byteAt js st.pos = 91))
    (h2 : ¬ (byteAt js st.pos = 125 ∨ byteAt js st.pos = 93)) (h3 : byteAt js st.pos ≠ 34)
    (h4 : ¬ (byteAt js st.pos = 9 ∨ byteAt js st.pos = 13 ∨ byteAt js st.pos = 10 ∨
      byteAt js st.pos = 32))
    (h5 : byteAt js st.pos ≠ 58) (h6 : byteAt js st.pos ≠ 44) :
    step js n st =
      match parsePrimitive js n st with
      | .error e => .error e
      | .ok st' => .ok ⟨st'.pos + 1, bumpSup st'.toks st'.sup, st'.sup⟩ := by
  (simp only [step, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]) <;> rfl

theorem step_open {js : List Nat} {n : Nat} {st : St} (obj : Bool)
    (h : byteAt js st.pos = if obj then 123 else 91) :
    step js n st =
      if n ≤ st.toks.length then .error ERROR_NOMEM
      else
        .ok ⟨st.pos + 1,
          bumpSup st.toks st.sup ++ [⟨if obj then OBJECT else ARRAY, st.pos, -1, 0⟩],
          st.toks.length⟩ := by
  cases obj <;> simp only [Bool.false_eq_true, _root_.ite_false, _root_.ite_true] at h ⊢ <;>
    ((simp +decide only [step, h, ite_true, ite_false]) <;> rfl)

theorem parseString_toks {js : List Nat} {n : Nat} {st st' : St}
    (h : parseString js n st = .ok st') : ∃ tk : Tok, tk.size = 0 ∧ st'.toks = st.toks ++ [tk] := by
  unfold parseString at h
  split at h
  · cases h
  · split_ifs at h
    cases h
    exact ⟨_, rfl, rfl⟩

theorem parsePrimitive_toks {js : List Nat} {n : Nat} {st st' : St}
    (h : parsePrimitive js n st = .ok st') : ∃ tk : Tok, tk.size = 0 ∧ st'.toks = st.toks ++ [tk] := by
  unfold parsePrimitive at h
  split at h
  · cases h
  · split_ifs at h
    cases h
    exact ⟨_, rfl, rfl⟩

/-! ## The byte classes -/

section
variable {js : Slice U8} {p : JsmnParser} {ts : Slice JsmnTok} {count ret : I32}

theorem body_ws (h : Inv js p ts count) (hl : p.pos.val < js.val.length)
    (hc : (js.val[p.pos.val]'hl).val = 9 ∨ (js.val[p.pos.val]'hl).val = 13 ∨
      (js.val[p.pos.val]'hl).val = 10 ∨ (js.val[p.pos.val]'hl).val = 32) :
    ∃ v, jsmn_parse_loop.body js (Slice.len js) p ts count ret false = .ok (.cont v) ∧
      StepPost js ts.val.length p (step (bytes js) ts.val.length (absSt p ts)) v := by
  obtain ⟨hlen, hpos, hk, hkp, hs1, hs2, hsz, hcount⟩ := h
  have hm : step (bytes js) ts.val.length (absSt p ts) =
      .ok ⟨p.pos.val + 1, mtoks ts p.toknext.val, p.toksuper.val⟩ := by
    apply step_ws
    simp only [absSt, byteAt_bytes hl]
    exact hc
  rw [hm]
  have hmax := js.property
  apply exists_cont_of_wp
  unfold jsmn_parse_loop.body
  aeneas_wp
  rust_split
  all_goals try rust_contra
  all_goals try (exfalso; omega)
  all_goals refine ⟨_, rfl, rfl, ?_, ?_, rfl, ?_⟩
  all_goals simp only [Inv, absSt, UScalar.ofNatCore_val_eq]
  all_goals first
    | omega
    | rfl
    | exact ⟨hlen, by omega, hk, by omega, hs1, hs2, hsz, hcount⟩

theorem body_colon (h : Inv js p ts count) (hl : p.pos.val < js.val.length)
    (hc : (js.val[p.pos.val]'hl).val = 58) :
    ∃ v, jsmn_parse_loop.body js (Slice.len js) p ts count ret false = .ok (.cont v) ∧
      StepPost js ts.val.length p (step (bytes js) ts.val.length (absSt p ts)) v := by
  obtain ⟨hlen, hpos, hk, hkp, hs1, hs2, hsz, hcount⟩ := h
  have hm : step (bytes js) ts.val.length (absSt p ts) =
      .ok ⟨p.pos.val + 1, mtoks ts p.toknext.val, (p.toknext.val : Int) - 1⟩ := by
    rw [step_colon (by simp only [absSt, byteAt_bytes hl]; exact hc)]
    simp [absSt, mtoks_length hk]
  rw [hm]
  have hmax := js.property
  have hck := hcast_i32_val (x := p.toknext) (by omega)
  apply exists_cont_of_wp
  unfold jsmn_parse_loop.body
  aeneas_wp [hck]
  rust_split
  all_goals try rust_contra
  all_goals try (exfalso; omega)
  all_goals refine ⟨_, rfl, rfl, ?_, ?_, rfl, ?_⟩
  all_goals simp only [Inv, absSt, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq, hck]
  all_goals first
    | omega
    | rfl
    | exact ⟨hlen, by omega, hk, by omega, by omega, by omega, hsz, hcount⟩

theorem body_comma (h : Inv js p ts count) (hl : p.pos.val < js.val.length)
    (hc : (js.val[p.pos.val]'hl).val = 44) :
    ∃ v, jsmn_parse_loop.body js (Slice.len js) p ts count ret false = .ok (.cont v) ∧
      StepPost js ts.val.length p (step (bytes js) ts.val.length (absSt p ts)) v := by
  obtain ⟨hlen, hpos, hk, hkp, hs1, hs2, hsz, hcount⟩ := h
  rw [step_comma (by simp only [absSt, byteAt_bytes hl]; exact hc)]
  simp only [absSt, mtoks_length hk]
  have hmax := js.property
  have hck := hcast_i32_val (x := p.toknext) (by omega)
  by_cases hsup : p.toksuper.val = -1
  · -- `toksuper == -1`: unchanged
    rw [if_neg (by simp [hsup])]
    apply exists_cont_of_wp
    unfold jsmn_parse_loop.body
    aeneas_wp
    rust_split
    all_goals try rust_contra
    all_goals try (exfalso; omega)
    all_goals refine ⟨_, rfl, rfl, ?_, ?_, rfl, ?_⟩
    all_goals simp only [Inv, absSt, UScalar.ofNatCore_val_eq]
    all_goals first
      | omega
      | rfl
      | exact ⟨hlen, by omega, hk, by omega, hs1, hs2, hsz, hcount⟩
  · have hs0 : 0 ≤ p.toksuper.val := by omega
    have hcs := hcast_usize_val hs0
    have hst : p.toksuper.val.toNat < p.toknext.val := by omega
    have hsl : p.toksuper.val.toNat < ts.val.length := by omega
    rw [mtoks_getD hst hk dflt]
    by_cases hcont : isCont (ts.val[p.toksuper.val.toNat]'hsl).typ = true
    · -- `toksuper` is an object or array: unchanged
      have hcond : ¬ (p.toksuper.val ≠ -1 ∧ (toTok (ts.val[p.toksuper.val.toNat]'hsl)).type ≠ ARRAY ∧
          (toTok (ts.val[p.toksuper.val.toNat]'hsl)).type ≠ OBJECT) := by
        have := (isCont_iff _).1 hcont
        simp only [toTok]
        omega
      rw [if_neg hcond]
      apply exists_cont_of_wp
      unfold jsmn_parse_loop.body
      aeneas_wp [hcs, is_container_eq, hcont]
      rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine ⟨_, rfl, rfl, ?_, ?_, rfl, ?_⟩
      all_goals simp only [Inv, absSt, UScalar.ofNatCore_val_eq]
      all_goals first
        | omega
        | rfl
        | exact ⟨hlen, by omega, hk, by omega, hs1, hs2, hsz, hcount⟩
    · -- a key or value: back to the last open object or array (if any)
      have hcont' : isCont (ts.val[p.toksuper.val.toNat]'hsl).typ = false := by simpa using hcont
      have hcond : p.toksuper.val ≠ -1 ∧ (toTok (ts.val[p.toksuper.val.toNat]'hsl)).type ≠ ARRAY ∧
          (toTok (ts.val[p.toksuper.val.toNat]'hsl)).type ≠ OBJECT := by
        have h1 : ¬ (typeCode (ts.val[p.toksuper.val.toNat]'hsl).typ = ARRAY ∨
            typeCode (ts.val[p.toksuper.val.toNat]'hsl).typ = OBJECT) := by
          rw [← isCont_iff]
          simpa using hcont
        simp only [toTok]
        omega
      rw [if_pos hcond]
      cases hlo : lastOpenCont (mtoks ts p.toknext.val) p.toknext.val with
      | none =>
        apply exists_cont_of_wp
        unfold jsmn_parse_loop.body
        aeneas_wp [hcs, is_container_eq, hcont', Bool.false_eq_true]
        rust_split
        all_goals try rust_contra
        all_goals try (exfalso; omega)
        all_goals refine find_open_container_wp ts p.toknext.val hk _ (by simp [hck]) ?_
        all_goals intro r hr
        all_goals rw [hlo] at hr
        all_goals simp only [optIdx] at hr
        all_goals aeneas_wp [hr]
        all_goals rust_split
        all_goals try rust_contra
        all_goals try (exfalso; omega)
        all_goals refine ⟨_, rfl, rfl, ?_, ?_, rfl, ?_⟩
        all_goals simp only [Inv, absSt, UScalar.ofNatCore_val_eq]
        all_goals first
          | omega
          | rfl
          | exact ⟨hlen, by omega, hk, by omega, hs1, hs2, hsz, hcount⟩
      | some i =>
        have hik : i < p.toknext.val := lastOpenCont_lt hlo
        apply exists_cont_of_wp
        unfold jsmn_parse_loop.body
        aeneas_wp [hcs, is_container_eq, hcont', Bool.false_eq_true]
        rust_split
        all_goals try rust_contra
        all_goals try (exfalso; omega)
        all_goals refine find_open_container_wp ts p.toknext.val hk _ (by simp [hck]) ?_
        all_goals intro r hr
        all_goals rw [hlo] at hr
        all_goals simp only [optIdx] at hr
        all_goals aeneas_wp [hr]
        all_goals rust_split
        all_goals try rust_contra
        all_goals try (exfalso; omega)
        all_goals refine ⟨_, rfl, rfl, ?_, ?_, rfl, ?_⟩
        all_goals simp only [Inv, absSt, UScalar.ofNatCore_val_eq, St.mk.injEq, true_and, and_true, hr]
        all_goals first
          | omega
          | rfl
          | exact ⟨hlen, by omega, hk, by omega, by omega, by omega, hsz, hcount⟩

theorem body_close (h : Inv js p ts count) (hl : p.pos.val < js.val.length) (obj : Bool)
    (hc : (js.val[p.pos.val]'hl).val = if obj then 125 else 93) :
    ∃ v, jsmn_parse_loop.body js (Slice.len js) p ts count ret false = .ok (.cont v) ∧
      StepPost js ts.val.length p (step (bytes js) ts.val.length (absSt p ts)) v := by
  obtain ⟨hlen, hpos, hk, hkp, hs1, hs2, hsz, hcount⟩ := h
  rw [step_close obj (by simp only [absSt, byteAt_bytes hl]; exact hc)]
  simp only [absSt, mtoks_length hk]
  have hmax := js.property
  have hck := hcast_i32_val (x := p.toknext) (by omega)
  have hcp := hcast_i32_val (x := p.pos) (by omega)
  have hdec : decide ((js.val[p.pos.val]'hl).val = 125) = obj := by
    cases obj <;> simp_all
  have hc' : (js.val[p.pos.val]'hl).val = 125 ∨ (js.val[p.pos.val]'hl).val = 93 := by
    cases obj <;> simp_all
  clear hc
  cases hlo : lastOpen (mtoks ts p.toknext.val) p.toknext.val with
  | none =>
    -- no open token: `JSMN_ERROR_INVAL`
    apply exists_cont_of_wp
    unfold jsmn_parse_loop.body
    aeneas_wp [hck]
    rust_split
    all_goals try rust_contra
    all_goals try (exfalso; omega)
    all_goals refine find_open_wp ts p.toknext.val hk p.toknext.val (le_refl _) _ (by simp [hck]) ?_
    all_goals intro r hr
    all_goals rw [hlo] at hr
    all_goals simp only [optIdx] at hr
    all_goals aeneas_wp [hr, not_true_eq_false]
    all_goals rust_split
    all_goals try rust_contra
    all_goals try (exfalso; omega)
    all_goals exact ⟨_, rfl, stepPost_err (by simp [JSMN_ERROR_INVAL, ERROR_INVAL]) (by simp [ERROR_INVAL])⟩
  | some i =>
    have hik : i < p.toknext.val := optIdx_lastOpen_lt hlo
    have hil : i < ts.val.length := by omega
    dsimp only
    simp only [mtoks_getD hik hk dflt]
    by_cases htype : (toTok (ts.val[i]'hil)).type ≠ (if obj then OBJECT else ARRAY)
    · -- the last open token has the other type: `JSMN_ERROR_INVAL`
      rw [if_pos htype]
      have hb1 : typeIs (ts.val[i]'hil).typ obj = false := by
        cases hb : typeIs (ts.val[i]'hil).typ obj
        · rfl
        · exact absurd ((typeIs_iff _ _).1 hb) htype
      apply exists_cont_of_wp
      unfold jsmn_parse_loop.body
      aeneas_wp [hck]
      rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine find_open_wp ts p.toknext.val hk p.toknext.val (le_refl _) _ (by simp [hck]) ?_
      all_goals intro r hr
      all_goals rw [hlo] at hr
      all_goals simp only [optIdx] at hr
      all_goals have hcr := hcast_usize_val (x := r) (by omega)
      all_goals aeneas_wp [hr, hcr, Int.toNat_natCast, type_is_eq, hdec, hb1, not_true_eq_false,
        Bool.false_eq_true]
      all_goals rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals exact ⟨_, rfl, stepPost_err (by simp [JSMN_ERROR_INVAL, ERROR_INVAL]) (by simp [ERROR_INVAL])⟩
    · -- close it; `toksuper` becomes the open token below it, or -1
      rw [if_neg htype]
      have hb1 : typeIs (ts.val[i]'hil).typ obj = true :=
        (typeIs_iff _ _).2 (by simpa [toTok] using htype)
      have hszi : (ts.val[i]'hil).size.val ≤ p.toknext.val := size_le hsz hik hk
      have hbd := optIdx_lastOpen_bounds (mtoks ts p.toknext.val) i
      apply exists_cont_of_wp
      unfold jsmn_parse_loop.body
      aeneas_wp [hck]
      rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine find_open_wp ts p.toknext.val hk p.toknext.val (le_refl _) _ (by simp [hck]) ?_
      all_goals intro r hr
      all_goals rw [hlo] at hr
      all_goals simp only [optIdx] at hr
      all_goals have hcr := hcast_usize_val (x := r) (by omega)
      all_goals aeneas_wp [hr, hcr, Int.toNat_natCast, type_is_eq, hdec, hb1, hcp,
        slice_index_mut_usize_eq, Slice.set_val_eq, List.length_set, not_true_eq_false]
      all_goals rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine find_open_after_close_wp ts p.toknext.val hk i hik _ (by rw [hcr, hr]; rfl)
                  _ _ (by simp only [IScalar.ofInt_val_eq, hcp]; omega) r hr ?_
      all_goals intro j hj
      all_goals aeneas_wp [hj, not_true_eq_false]
      all_goals rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine ⟨_, rfl, stepPost_ok ?_ ?_ (by simp [Slice.set_val_eq]) (by simp)⟩
      all_goals simp only [absSt, Inv, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq, St.mk.injEq,
        true_and, Slice.set_val_eq, List.length_set, mtoks_set_lt, hcr, hr, Int.toNat_natCast]
      all_goals first
        | exact ⟨by simp [toTok], by omega⟩
        | exact ⟨hlen, by omega, hk, by omega, by omega, by omega,
            sizes_set hsz i _ (by simp only [toTok]; omega), hcount⟩

theorem body_string (h : Inv js p ts count) (hl : p.pos.val < js.val.length)
    (hc : (js.val[p.pos.val]'hl).val = 34) :
    ∃ v, jsmn_parse_loop.body js (Slice.len js) p ts count ret false = .ok (.cont v) ∧
      StepPost js ts.val.length p (step (bytes js) ts.val.length (absSt p ts)) v := by
  obtain ⟨hlen, hpos, hk, hkp, hs1, hs2, hsz, hcount⟩ := h
  rw [step_string (by simp only [absSt, byteAt_bytes hl]; exact hc)]
  obtain ⟨⟨r, p2, ts2⟩, hps, hpost⟩ := parse_string_spec (p := p) (ts := ts) hl hlen hk
  have hmax := js.property
  cases hpr : parseString (bytes js) ts.val.length (absSt p ts) with
  | error e =>
    rw [hpr] at hpost
    dsimp only at hpost
    obtain ⟨hr, he⟩ := hpost
    dsimp only
    apply exists_cont_of_wp
    unfold jsmn_parse_loop.body
    aeneas_wp [hps]
    rust_split
    all_goals try rust_contra
    all_goals try (exfalso; omega)
    all_goals exact ⟨_, rfl, stepPost_err hr he⟩
  | ok st' =>
    rw [hpr] at hpost
    dsimp only at hpost
    obtain ⟨hr, habs, hk2, hsup2, hlen2, hkl, hp1, hp2⟩ := hpost
    obtain ⟨tk, htk0, htoks⟩ := parseString_toks hpr
    subst habs
    dsimp only
    simp only [absSt] at htoks ⊢
    rw [hk2] at htoks
    have hsz2 : ∀ t ∈ mtoks ts2 (p.toknext.val + 1), t.size ≤ p.toknext.val := by
      rw [htoks]
      exact sizes_append hsz (by rw [htk0]; omega)
    rw [hsup2, hk2]
    by_cases hsup : p.toksuper.val = -1
    · -- no parent token
      apply exists_cont_of_wp
      unfold jsmn_parse_loop.body
      aeneas_wp [hps, hsup2]
      rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine ⟨_, rfl, stepPost_ok ?_ ?_ hlen2 (by simp only [UScalar.ofNatCore_val_eq]; omega)⟩
      all_goals simp only [absSt, Inv, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq, St.mk.injEq,
        true_and, and_true, hk2, hsup2, bumpSup, hsup, _root_.ite_true]
      all_goals first
        | rfl
        | exact ⟨hlen, by omega, by omega, by omega, by omega, by omega,
            fun t ht => by have := hsz2 t ht; push_cast; omega, by omega⟩
    · -- the parent token's size + 1
      have hcs := hcast_usize_val (x := p.toksuper) (by omega)
      have hs3 : p.toksuper.val.toNat < p.toknext.val + 1 := by omega
      have hl2 : p.toknext.val + 1 ≤ ts2.val.length := by omega
      have hsz3 := size_le hsz2 hs3 hl2
      have hszlo := IScalar.hmin (ts2.val[p.toksuper.val.toNat]'(by omega)).size
      simp only [IScalarTy.I32_numBits_eq] at hszlo
      apply exists_cont_of_wp
      unfold jsmn_parse_loop.body
      aeneas_wp [hps, hsup2, hcs, slice_index_mut_usize_eq, Slice.set_val_eq, List.length_set]
      rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine ⟨_, rfl, stepPost_ok ?_ ?_ (by simp [Slice.set_val_eq, hlen2])
        (by simp only [UScalar.ofNatCore_val_eq]; omega)⟩
      all_goals simp only [absSt, Inv, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq, St.mk.injEq,
        true_and, and_true, hk2, hsup2, Slice.set_val_eq, List.length_set,
        mtoks_bump' ts2 _ _ _ hcs hs3 hl2, bumpSup, hsup, _root_.ite_false]
      all_goals first
        | rfl
        | exact ⟨hlen, by omega, by omega, by omega, by omega, by omega,
            fun t ht => by have := sizes_incSize hsz2 _ t ht; push_cast; omega, by omega⟩

theorem body_prim (h : Inv js p ts count) (hl : p.pos.val < js.val.length)
    (hz : (js.val[p.pos.val]'hl).val ≠ 0)
    (hc : ¬ ((js.val[p.pos.val]'hl).val = 123 ∨ (js.val[p.pos.val]'hl).val = 91 ∨
      (js.val[p.pos.val]'hl).val = 125 ∨ (js.val[p.pos.val]'hl).val = 93 ∨
      (js.val[p.pos.val]'hl).val = 34 ∨ (js.val[p.pos.val]'hl).val = 9 ∨
      (js.val[p.pos.val]'hl).val = 13 ∨ (js.val[p.pos.val]'hl).val = 10 ∨
      (js.val[p.pos.val]'hl).val = 32 ∨ (js.val[p.pos.val]'hl).val = 58 ∨
      (js.val[p.pos.val]'hl).val = 44)) :
    ∃ v, jsmn_parse_loop.body js (Slice.len js) p ts count ret false = .ok (.cont v) ∧
      StepPost js ts.val.length p (step (bytes js) ts.val.length (absSt p ts)) v := by
  obtain ⟨hlen, hpos, hk, hkp, hs1, hs2, hsz, hcount⟩ := h
  have hb : byteAt (bytes js) (absSt p ts).pos = (js.val[p.pos.val]'hl).val := by
    simp only [absSt, byteAt_bytes hl]
  rw [step_prim (by rw [hb]; omega) (by rw [hb]; omega) (by rw [hb]; omega) (by rw [hb]; omega)
    (by rw [hb]; omega) (by rw [hb]; omega)]
  have hd : primDelim (js.val[p.pos.val]'hl).val = false := by
    simp only [primDelim, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    omega
  obtain ⟨⟨r, p2, ts2⟩, hps, hpost⟩ := parse_primitive_spec (p := p) (ts := ts) hl hlen hz hd hk
  have hmax := js.property
  cases hpr : parsePrimitive (bytes js) ts.val.length (absSt p ts) with
  | error e =>
    rw [hpr] at hpost
    dsimp only at hpost
    obtain ⟨hr, he⟩ := hpost
    dsimp only
    apply exists_cont_of_wp
    unfold jsmn_parse_loop.body
    aeneas_wp [hps]
    rust_split
    all_goals try rust_contra
    all_goals try (exfalso; omega)
    all_goals exact ⟨_, rfl, stepPost_err hr he⟩
  | ok st' =>
    rw [hpr] at hpost
    dsimp only at hpost
    obtain ⟨hr, habs, hk2, hsup2, hlen2, hkl, hp1, hp2⟩ := hpost
    obtain ⟨tk, htk0, htoks⟩ := parsePrimitive_toks hpr
    subst habs
    dsimp only
    simp only [absSt] at htoks ⊢
    rw [hk2] at htoks
    have hsz2 : ∀ t ∈ mtoks ts2 (p.toknext.val + 1), t.size ≤ p.toknext.val := by
      rw [htoks]
      exact sizes_append hsz (by rw [htk0]; omega)
    rw [hsup2, hk2]
    by_cases hsup : p.toksuper.val = -1
    · -- no parent token
      apply exists_cont_of_wp
      unfold jsmn_parse_loop.body
      aeneas_wp [hps, hsup2]
      rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine ⟨_, rfl, stepPost_ok ?_ ?_ hlen2 (by simp only [UScalar.ofNatCore_val_eq]; omega)⟩
      all_goals simp only [absSt, Inv, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq, St.mk.injEq,
        true_and, and_true, hk2, hsup2, bumpSup, hsup, _root_.ite_true]
      all_goals first
        | rfl
        | exact ⟨hlen, by omega, by omega, by omega, by omega, by omega,
            fun t ht => by have := hsz2 t ht; push_cast; omega, by omega⟩
    · -- the parent token's size + 1
      have hcs := hcast_usize_val (x := p.toksuper) (by omega)
      have hs3 : p.toksuper.val.toNat < p.toknext.val + 1 := by omega
      have hl2 : p.toknext.val + 1 ≤ ts2.val.length := by omega
      have hsz3 := size_le hsz2 hs3 hl2
      have hszlo := IScalar.hmin (ts2.val[p.toksuper.val.toNat]'(by omega)).size
      simp only [IScalarTy.I32_numBits_eq] at hszlo
      apply exists_cont_of_wp
      unfold jsmn_parse_loop.body
      aeneas_wp [hps, hsup2, hcs, slice_index_mut_usize_eq, Slice.set_val_eq, List.length_set]
      rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine ⟨_, rfl, stepPost_ok ?_ ?_ (by simp [Slice.set_val_eq, hlen2])
        (by simp only [UScalar.ofNatCore_val_eq]; omega)⟩
      all_goals simp only [absSt, Inv, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq, St.mk.injEq,
        true_and, and_true, hk2, hsup2, Slice.set_val_eq, List.length_set,
        mtoks_bump' ts2 _ _ _ hcs hs3 hl2, bumpSup, hsup, _root_.ite_false]
      all_goals first
        | rfl
        | exact ⟨hlen, by omega, by omega, by omega, by omega, by omega,
            fun t ht => by have := sizes_incSize hsz2 _ t ht; push_cast; omega, by omega⟩

theorem body_open (h : Inv js p ts count) (hl : p.pos.val < js.val.length) (obj : Bool)
    (hc : (js.val[p.pos.val]'hl).val = if obj then 123 else 91) :
    ∃ v, jsmn_parse_loop.body js (Slice.len js) p ts count ret false = .ok (.cont v) ∧
      StepPost js ts.val.length p (step (bytes js) ts.val.length (absSt p ts)) v := by
  obtain ⟨hlen, hpos, hk, hkp, hs1, hs2, hsz, hcount⟩ := h
  rw [step_open obj (by simp only [absSt, byteAt_bytes hl]; exact hc)]
  simp only [absSt, mtoks_length hk]
  have hmax := js.property
  have hc' : (js.val[p.pos.val]'hl).val = 123 ∨ (js.val[p.pos.val]'hl).val = 91 := by
    cases obj <;> simp_all
  by_cases hfull : ts.val.length ≤ p.toknext.val
  · -- the array is full: `JSMN_ERROR_NOMEM`
    rw [if_pos hfull]
    have ha := alloc_token_none (p := p) (ts := ts) hfull
    apply exists_cont_of_wp
    unfold jsmn_parse_loop.body
    aeneas_wp [ha]
    rust_split
    all_goals try rust_contra
    all_goals try (exfalso; omega)
    all_goals exact ⟨_, rfl, stepPost_err (by simp [JSMN_ERROR_NOMEM, ERROR_NOMEM]) (by simp [ERROR_NOMEM])⟩
  · rw [if_neg hfull]
    have hlt : p.toknext.val < ts.val.length := by omega
    obtain ⟨a, ha, ha1, ha2, ha3, ha4, ha5⟩ := alloc_token_some (p := p) (ts := ts) hlt
    obtain ⟨o, p1, ts1⟩ := a
    simp only at ha1 ha2 ha3 ha4 ha5
    subst ha1 ha5
    have hck1 := hcast_i32_val (x := p1.toknext) (by omega)
    have hcp1 := hcast_i32_val (x := p1.pos) (by rw [ha2]; omega)
    have hl1 : p.toknext.val < (ts.set p.toknext (allocd (ts.val[p.toknext.val]'hlt))).val.length := by
      rw [slice_set_len]; exact hlt
    have ha2' : p1.pos.val = p.pos.val := by rw [ha2]
    have hcp := hcast_i32_val (x := p.pos) (by omega)
    cases obj <;> simp only [Bool.false_eq_true, _root_.ite_false, _root_.ite_true] at hc ⊢
    all_goals
     by_cases hsup : p.toksuper.val = -1
     · -- no parent token
      apply exists_cont_of_wp
      unfold jsmn_parse_loop.body
      aeneas_wp
      rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals rw [ha, wp_ok]
      all_goals aeneas_wp [ha4, slice_index_mut_ok, slice_set_len, hlt, hck1, hcp1]
      all_goals rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine ⟨_, rfl, stepPost_ok ?_ ?_ (by simp only [slice_set_len])
                  (by simp only [UScalar.ofNatCore_val_eq]; omega)⟩
      all_goals simp only [absSt, Inv, St.mk.injEq, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq,
        hck1, ha2, ha3, slice_set_len, mtoks_set_eq, mtoks_set_ge, le_refl, hlt, hl1, bumpSup, hsup,
        _root_.ite_true]
      all_goals simp only [slice_set_get_self, allocd, toTok, typeCode, IScalar.ofInt_val_eq, hcp,
        true_and]
      all_goals first
        | omega
        | exact ⟨hlen, by omega, by omega, by omega, by omega, by omega,
            sizes_append (fun u hu => by have := hsz u hu; push_cast; omega) (by simp <;> omega),
            by omega⟩
     · -- the parent token's size + 1
      have hcs := hcast_usize_val (x := p.toksuper) (by omega)
      have hst : p.toksuper.val.toNat < p.toknext.val := by omega
      have hne : p.toksuper.val.toNat ≠ p.toknext.val := by omega
      have hsl1 : p.toksuper.val.toNat < (ts.set p.toknext (allocd (ts.val[p.toknext.val]'hlt))).val.length := by
        rw [slice_set_len]; omega
      have hB : (ts.set p.toknext (allocd (ts.val[p.toknext.val]'hlt))).val[p.toksuper.val.toNat]'hsl1 =
          ts.val[p.toksuper.val.toNat]'(by omega) :=
        slice_set_get_ne _ _ _ _ (by omega) _
      have hszB : ((ts.set p.toknext (allocd (ts.val[p.toknext.val]'hlt))).val[p.toksuper.val.toNat]'hsl1).size.val ≤
          p.toknext.val := by
        rw [hB]; exact size_le hsz hst hk
      have hszBlo := IScalar.hmin ((ts.set p.toknext (allocd (ts.val[p.toknext.val]'hlt))).val[p.toksuper.val.toNat]'hsl1).size
      simp only [IScalarTy.I32_numBits_eq] at hszBlo
      have hsl : p.toksuper.val.toNat < ts.val.length := by omega
      have hcsne : (IScalar.hcast .Usize p.toksuper).val ≠ p.toknext.val := by rw [hcs]; exact hne
      apply exists_cont_of_wp
      unfold jsmn_parse_loop.body
      aeneas_wp
      rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals rw [ha, wp_ok]
      all_goals aeneas_wp [ha4, hcs, slice_index_mut_ok, slice_index_ok, slice_set_len, hlt, hsl, hck1,
        hcp1]
      all_goals rust_split
      all_goals try rust_contra
      all_goals try (exfalso; omega)
      all_goals refine ⟨_, rfl, stepPost_ok ?_ ?_ (by simp only [slice_set_len])
                  (by simp only [UScalar.ofNatCore_val_eq]; omega)⟩
      all_goals simp only [absSt, Inv, St.mk.injEq, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq,
        hck1, ha2, ha3, slice_set_len, mtoks_set_eq, mtoks_set_ge, le_refl, hlt, hl1,
        mtoks_bump' (ts.set p.toknext (allocd (ts.val[p.toknext.val]'hlt))) _ _ _ hcs hst hl1.le,
        bumpSup, hsup, _root_.ite_false]
      all_goals simp only [slice_set_get_self, slice_set_get_ne _ _ _ _ hcsne, allocd, toTok, typeCode,
        IScalar.ofInt_val_eq, hcp, true_and]
      all_goals first
        | omega
        | exact ⟨hlen, by omega, by omega, by omega, by omega, by omega,
            sizes_append (fun u hu => by have := sizes_incSize hsz _ u hu; push_cast; omega)
              (by simp <;> omega),
            by omega⟩

/-- One turn of `jsmn_parse`'s loop on a live byte: the model's `step`. -/
theorem body_step (h : Inv js p ts count) (hlive : live (bytes js) p.pos.val) :
    ∃ v, jsmn_parse_loop.body js (Slice.len js) p ts count ret false = .ok (.cont v) ∧
      StepPost js ts.val.length p (step (bytes js) ts.val.length (absSt p ts)) v := by
  have hl := lt_of_live hlive
  have hz : (js.val[p.pos.val]'hl).val ≠ 0 := (live_bytes hl).1 hlive
  by_cases h1 : (js.val[p.pos.val]'hl).val = 123
  · exact body_open h hl true (by simpa using h1)
  by_cases h2 : (js.val[p.pos.val]'hl).val = 91
  · exact body_open h hl false (by simpa using h2)
  by_cases h3 : (js.val[p.pos.val]'hl).val = 125
  · exact body_close h hl true (by simpa using h3)
  by_cases h4 : (js.val[p.pos.val]'hl).val = 93
  · exact body_close h hl false (by simpa using h4)
  by_cases h5 : (js.val[p.pos.val]'hl).val = 34
  · exact body_string h hl h5
  by_cases h6 : (js.val[p.pos.val]'hl).val = 9 ∨ (js.val[p.pos.val]'hl).val = 13 ∨
      (js.val[p.pos.val]'hl).val = 10 ∨ (js.val[p.pos.val]'hl).val = 32
  · exact body_ws h hl h6
  by_cases h7 : (js.val[p.pos.val]'hl).val = 58
  · exact body_colon h hl h7
  by_cases h8 : (js.val[p.pos.val]'hl).val = 44
  · exact body_comma h hl h8
  exact body_prim h hl hz (by omega)

theorem body_stop (len : Usize) (v : JsmnParser × Slice JsmnTok × I32 × I32) :
    jsmn_parse_loop.body js len v.1 v.2.1 v.2.2.1 v.2.2.2 true =
      .ok (.done (v.1, v.2.1, v.2.2.1, v.2.2.2, true)) := rfl

/-- At the end of the input (or a NUL byte) the loop stops. -/
theorem body_end (hd : ¬ live (bytes js) p.pos.val) :
    jsmn_parse_loop.body js (Slice.len js) p ts count ret false =
      .ok (.done (p, ts, count, ret, false)) := by
  by_cases hl : p.pos.val < js.val.length
  · have hz : (js.val[p.pos.val]'hl).val = 0 := by
      rw [live_bytes hl] at hd
      omega
    apply eq_ok_of_wp
    unfold jsmn_parse_loop.body
    aeneas_wp
    rust_split
    all_goals try rust_contra
    all_goals try (exfalso; omega)
    all_goals simp
  · apply eq_ok_of_wp
    unfold jsmn_parse_loop.body
    aeneas_wp
    rust_split
    all_goals try rust_contra
    all_goals try (exfalso; omega)
    all_goals simp

end

end EquivLean.Demo.XLang.Jsmn.Rust
