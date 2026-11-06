import EquivLean.Modernize.Cbstm03b.RustRun4

/-!
# CBSTM03B → Rust: one call

`call` dispatches on the DD name as the model does (`dd_iff`), takes the OPEN outcome of the file
(`open_err_code_spec`: `255` for none, else the status, below 100 by `CallHyp`) and runs the file's procedure
(`*_proc_spec`). `call_spec_of`: on inputs with `CallHyp`, and with `AcctKeyAgree` (on a keyed READ of ACCTFILE,
`acct_key` reads the model's value of the key), `call` returns the model's state and area. `acct_key_agree`: on the
statements' domain (the key's first `k` bytes are CP037 digits, `CallHyp.acctKey`) `acct_key`'s digit fold `% 10 ^ 11`
is the model's `acctVal`, so `call_spec : CallSpec`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Rust

/-- The OPEN outcome of file `i + 1`: `255` (no error) for none, else the status. -/
theorem open_err_code_spec (oe : Std.Array (Option U8) 4#usize) (i : Nat)
    (hlt : ∀ c, oe.val.getD i none = some c → c.val < 100) :
    ∃ c, cbstm03b.open_err_code (oe.val.getD i none) = .ok c ∧
      ((c.val = 255 ∧ absOe oe (i + 1) = none) ∨ (c.val < 100 ∧ absOe oe (i + 1) = some c.val)) := by
  unfold absOe
  rw [Nat.add_sub_cancel]
  cases h : oe.val.getD i none with
  | none => exact ⟨cbstm03b.NO_ERR, rfl, Or.inl ⟨no_err_val, rfl⟩⟩
  | some c => exact ⟨c, rfl, Or.inr ⟨hlt c h, rfl⟩⟩

/-- On a keyed READ of ACCTFILE, `acct_key` reads the model's value of the key. -/
def AcctKeyAgree (q : cbstm03b.LkM03bArea) : Prop :=
  Model.aOp (LkM03bArea.vals q) = opReadK → Model.aDd (LkM03bArea.vals q) = ddAcct →
    ∀ key, cbstm03b.acct_key q = .ok key →
      key.val = Model.acctVal (Model.aKey (LkM03bArea.vals q)) (Model.aKeyLn (LkM03bArea.vals q)).toNat

/-- **One call**: on inputs with `CallHyp` and `AcctKeyAgree`, `call` returns (no panic) the model's state and
area. -/
theorem call_spec_of (oe : Std.Array (Option U8) 4#usize) (st : cbstm03b.State) (q : cbstm03b.LkM03bArea)
    (h : CallHyp oe st q) (hacct : AcctKeyAgree q) :
    ∃ st' q', cbstm03b.call oe st q = .ok (st', q') ∧
      absSt st' = (Model.call (absOe oe) (absSt st) (LkM03bArea.vals q)).1 ∧
      LkM03bArea.vals q' = (Model.call (absOe oe) (absSt st) (LkM03bArea.vals q)).2 := by
  have hl4 : oe.val.length = 4 := oe.property
  have hi0 : Array.index_usize oe 0#usize = .ok (oe.val.getD 0 none) := index_usize_getD _ _ (by simp [hl4])
  have hi1 : Array.index_usize oe 1#usize = .ok (oe.val.getD 1 none) := index_usize_getD _ _ (by simp [hl4])
  have hi2 : Array.index_usize oe 2#usize = .ok (oe.val.getD 2 none) := index_usize_getD _ _ (by simp [hl4])
  have hi3 : Array.index_usize oe 3#usize = .ok (oe.val.getD 3 none) := index_usize_getD _ _ (by simp [hl4])
  have hdd := aDd_vals q
  by_cases hT : q.lk_m03b_dd.val = [84#u8, 82#u8, 78#u8, 88#u8, 70#u8, 73#u8, 76#u8, 69#u8]
  · have hT' : Model.aDd (LkM03bArea.vals q) = ddTrnx := by rw [hdd]; exact (dd_iff ebc_trnx).2 hT
    obtain ⟨c, hc, hcc⟩ := open_err_code_spec oe 0 (h.oe_lt 0 (by norm_num))
    obtain ⟨v, hv, hvv⟩ := trnx_proc_spec c _ hcc st q
    have hM : Model.call (absOe oe) (absSt st) (LkM03bArea.vals q) = (absSt v.1, LkM03bArea.vals v.2) := by
      rw [hvv]
      simp only [Model.call, eq_true hT', ↓reduceIte]
    refine ⟨v.1, v.2, ?_, by rw [hM], by rw [hM]⟩
    simp only [cbstm03b.call, eq8_eq, Array.make, Array.from_val, eq_true hT, decide_true, bind_ok, ↓reduceIte,
      hi0, hc, hv]
  have hT' : Model.aDd (LkM03bArea.vals q) ≠ ddTrnx := fun e => hT ((dd_iff ebc_trnx).1 (hdd ▸ e))
  by_cases hX : q.lk_m03b_dd.val = [88#u8, 82#u8, 69#u8, 70#u8, 70#u8, 73#u8, 76#u8, 69#u8]
  · have hX' : Model.aDd (LkM03bArea.vals q) = ddXref := by rw [hdd]; exact (dd_iff ebc_xref).2 hX
    obtain ⟨c, hc, hcc⟩ := open_err_code_spec oe 1 (h.oe_lt 1 (by norm_num))
    obtain ⟨v, hv, hvv⟩ := xref_proc_spec c _ hcc st q
    have hM : Model.call (absOe oe) (absSt st) (LkM03bArea.vals q) = (absSt v.1, LkM03bArea.vals v.2) := by
      rw [hvv]
      simp only [Model.call, hT', eq_true hX', ↓reduceIte]
    refine ⟨v.1, v.2, ?_, by rw [hM], by rw [hM]⟩
    simp only [cbstm03b.call, eq8_eq, Array.make, Array.from_val, hT, eq_true hX, decide_true, decide_false,
      bind_ok, ↓reduceIte,
      Bool.false_eq_true, hi1, hc, hv]
  have hX' : Model.aDd (LkM03bArea.vals q) ≠ ddXref := fun e => hX ((dd_iff ebc_xref).1 (hdd ▸ e))
  by_cases hC : q.lk_m03b_dd.val = [67#u8, 85#u8, 83#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]
  · have hC' : Model.aDd (LkM03bArea.vals q) = ddCust := by rw [hdd]; exact (dd_iff ebc_cust).2 hC
    obtain ⟨c, hc, hcc⟩ := open_err_code_spec oe 2 (h.oe_lt 2 (by norm_num))
    have hkl : Model.aOp (LkM03bArea.vals q) = opReadK →
        0 ≤ q.lk_m03b_key_ln.val ∧ q.lk_m03b_key_ln.val ≤ 25 := fun hk => by
      have := h.keyLn hk (Or.inl hC')
      rw [aKeyLn_vals] at this
      omega
    obtain ⟨v, hv, hvv⟩ := cust_proc_spec c _ hcc st q hkl
    have hM : Model.call (absOe oe) (absSt st) (LkM03bArea.vals q) = (absSt v.1, LkM03bArea.vals v.2) := by
      rw [hvv]
      simp only [Model.call, hT', hX', eq_true hC', ↓reduceIte]
    refine ⟨v.1, v.2, ?_, by rw [hM], by rw [hM]⟩
    simp only [cbstm03b.call, eq8_eq, Array.make, Array.from_val, hT, hX, eq_true hC, decide_true, decide_false,
      bind_ok, ↓reduceIte,
      Bool.false_eq_true, hi2, hc, hv]
  have hC' : Model.aDd (LkM03bArea.vals q) ≠ ddCust := fun e => hC ((dd_iff ebc_cust).1 (hdd ▸ e))
  by_cases hA : q.lk_m03b_dd.val = [65#u8, 67#u8, 67#u8, 84#u8, 70#u8, 73#u8, 76#u8, 69#u8]
  · have hA' : Model.aDd (LkM03bArea.vals q) = ddAcct := by rw [hdd]; exact (dd_iff ebc_acct).2 hA
    obtain ⟨c, hc, hcc⟩ := open_err_code_spec oe 3 (h.oe_lt 3 (by norm_num))
    have hkv : Model.aOp (LkM03bArea.vals q) = opReadK → ∃ key, cbstm03b.acct_key q = .ok key ∧
        key.val = Model.acctVal (Model.aKey (LkM03bArea.vals q)) (Model.aKeyLn (LkM03bArea.vals q)).toNat :=
      fun hk => by
        have hr := h.keyLn hk (Or.inr hA')
        rw [aKeyLn_vals] at hr
        obtain ⟨key, hkey, -⟩ := acct_key_eq q (by omega) hr.2
        exact ⟨key, hkey, hacct hk hA' key hkey⟩
    obtain ⟨v, hv, hvv⟩ := acct_proc_spec c _ hcc st q h.acct hkv
    have hM : Model.call (absOe oe) (absSt st) (LkM03bArea.vals q) = (absSt v.1, LkM03bArea.vals v.2) := by
      rw [hvv]
      simp only [Model.call, hT', hX', hC', eq_true hA', ↓reduceIte]
    refine ⟨v.1, v.2, ?_, by rw [hM], by rw [hM]⟩
    simp only [cbstm03b.call, eq8_eq, Array.make, Array.from_val, hT, hX, hC, eq_true hA, decide_true,
      decide_false, bind_ok,
      ↓reduceIte, Bool.false_eq_true, hi3, hc, hv]
  have hA' : Model.aDd (LkM03bArea.vals q) ≠ ddAcct := fun e => hA ((dd_iff ebc_acct).1 (hdd ▸ e))
  refine ⟨st, q, ?_, ?_, ?_⟩
  · simp only [cbstm03b.call, eq8_eq, Array.make, Array.from_val, hT, hX, hC, hA, decide_false, bind_ok,
      ↓reduceIte,
      Bool.false_eq_true]
  · simp only [Model.call, hT', hX', hC', hA', ↓reduceIte]
  · simp only [Model.call, hT', hX', hC', hA', ↓reduceIte]

/-! ## The ACCTFILE key on digit keys (the statements' domain) -/

/-- The Latin-1 byte of a CP037 digit is an ASCII digit. -/
theorem ebc_digit_inv : ∀ n : Fin 256, 240 ≤ ebcdicOfLatin1 n.val → ebcdicOfLatin1 n.val ≤ 249 →
    48 ≤ n.val ∧ n.val ≤ 57 := by decide +kernel

theorem and15_digit : ∀ n, n < 10 → (48 + n) &&& 15 = n := by decide

/-- ASCII digits read by `b &&& 15`, as a number. -/
theorem digitsVal_digits (L : List U8) (h : ∀ u ∈ L, 48 ≤ u.val ∧ u.val ≤ 57) :
    digitsVal L = ((Cobol.Digits.ofDigits 10 (L.map (fun u => u.val - 48)) : Nat) : Int) := by
  have key : ∀ (L : List U8), (∀ u ∈ L, 48 ≤ u.val ∧ u.val ≤ 57) → ∀ n : Nat,
      L.foldl (fun acc b => acc * 10 + ((b.val &&& 15 : Nat) : Int)) (n : Int) =
        (((L.map (fun u => u.val - 48)).foldl (fun a d => a * 10 + d) n : Nat) : Int) := by
    intro L
    induction L with
    | nil => intro _ n; rfl
    | cons u t ih =>
      intro h n
      have hu := h u (by simp)
      have h15 : u.val &&& 15 = u.val - 48 := by
        have := and15_digit (u.val - 48) (by omega)
        rwa [show 48 + (u.val - 48) = u.val by omega] at this
      simp only [List.foldl_cons, List.map_cons, h15]
      rw [show (n : Int) * 10 + ((u.val - 48 : Nat) : Int) = ((n * 10 + (u.val - 48) : Nat) : Int) by
        push_cast; ring]
      exact ih (fun v hv => h v (by simp [hv])) _
  exact key L h 0

theorem ofDigits_append10 (A B : List Nat) :
    Cobol.Digits.ofDigits 10 (A ++ B) =
      Cobol.Digits.ofDigits 10 A * 10 ^ B.length + Cobol.Digits.ofDigits 10 B := by
  induction A with
  | nil => simp
  | cons a A ih =>
    rw [List.cons_append, Cobol.Digits.ofDigits_cons, ih, Cobol.Digits.ofDigits_cons, List.length_append,
      Nat.pow_add]
    ring

/-- The value of `k` digits modulo `10 ^ 11` is the value of their last 11 (`PIC 9(11)` keeps those). -/
theorem ofDigits_drop_mod (ds : List Nat) (k : Nat) (hk : ds.length = k) :
    Cobol.Digits.ofDigits 10 ds % 100000000000 =
      Cobol.Digits.ofDigits 10 (ds.drop (k - 11)) % 100000000000 := by
  conv_lhs => rw [← List.take_append_drop (k - 11) ds]
  rw [ofDigits_append10]
  rcases Nat.lt_or_ge k 11 with h | h
  · rw [show k - 11 = 0 by omega]
    simp
  · have hl : (ds.drop (k - 11)).length = 11 := by simp; omega
    rw [hl, show (10 : Nat) ^ 11 = 100000000000 by norm_num]
    omega

/-- `MOVE` into `PIC 9(11)`, for a nonnegative value: the value modulo `10 ^ 11`. -/
theorem fitNum11 (v : Int) (h0 : 0 ≤ v) : (Sem.fitNum {} { digits := 11 } v).2 = v % 100000000000 := by
  have hv : ((v.natAbs : Nat) : Int) = v := Int.natAbs_of_nonneg h0
  simp only [Sem.fitNum, Sem.fitDec, NumFmt.fullBinary, truncDigits, Bool.false_eq_true, ↓reduceIte, hv]
  split_ifs <;> omega

/-- The model's value of a key whose first `k` bytes are ASCII digits (as Latin-1 bytes). -/
theorem acctVal_digits (L : List U8) (k : Nat) (hk1 : 1 ≤ k) (hLk : L.length = k)
    (h : ∀ u ∈ L, 48 ≤ u.val ∧ u.val ≤ 57) (key : List U8) (hkey : key.take k = L) :
    Model.acctVal (key.map (fun u => ebcdicOfLatin1 u.val)) k =
      ((Cobol.Digits.ofDigits 10 (L.map (fun u => u.val - 48)) : Nat) : Int) % 100000000000 := by
  have hdlt : ∀ d ∈ L.map (fun u => u.val - 48), d < 10 := by
    intro d hd
    rw [List.mem_map] at hd
    obtain ⟨u, hu, rfl⟩ := hd
    have := h u hu
    omega
  have hdl : (L.map (fun u => u.val - 48)).length = k := by rw [List.length_map, hLk]
  have henc : (key.map (fun u => ebcdicOfLatin1 u.val)).take k =
      encZoned {} { digits := k } ((Cobol.Digits.ofDigits 10 (L.map (fun u => u.val - 48)) : Nat) : Int) := by
    rw [← List.map_take, hkey]
    have hto : Cobol.Digits.toDigits 10 (L.map (fun u => u.val - 48)).length
        (Cobol.Digits.ofDigits 10 (L.map (fun u => u.val - 48))) = L.map (fun u => u.val - 48) :=
      Cobol.Digits.toDigits_ofDigits _ hdlt
    rw [hdl] at hto
    rcases k with _ | j
    · omega
    simp only [encZoned, Int.natAbs_natCast, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
    rw [← List.map_singleton (f := Config.digitByte {}), ← List.map_append,
      show Cobol.Digits.toDigits 10 j (Cobol.Digits.ofDigits 10 (L.map (fun u => u.val - 48)) / 10) ++
        [Cobol.Digits.ofDigits 10 (L.map (fun u => u.val - 48)) % 10] =
        Cobol.Digits.toDigits 10 (j + 1) (Cobol.Digits.ofDigits 10 (L.map (fun u => u.val - 48))) from rfl,
      hto, List.map_map]
    apply List.map_congr_left
    intro u hu
    have := h u hu
    simp only [Function.comp_apply]
    have e := ebc_digit48 (u.val - 48) (by omega)
    rw [show 48 + (u.val - 48) = u.val by omega] at e
    rw [e]
    rfl
  have hlt := Cobol.Digits.ofDigits_lt (b := 10) (by norm_num) _ hdlt
  rw [hdl] at hlt
  have hdec : decodeNum {} { digits := k } ((key.map (fun u => ebcdicOfLatin1 u.val)).take k) =
      some ((Cobol.Digits.ofDigits 10 (L.map (fun u => u.val - 48)) : Nat) : Int) := by
    rw [henc]
    simp only [decodeNum, show k ≠ 0 by omega, ↓reduceIte]
    exact decZoned_encZoned {} _ _ (by simp; omega) (by simpa using hlt) (fun _ => Int.natCast_nonneg _)
  unfold Model.acctVal
  rw [hdec, Option.getD_some, fitNum11 _ (Int.natCast_nonneg _)]

/-- `acct_key` on a key whose first `k` bytes are CP037 digits reads the model's value. -/
theorem acct_key_agree (q : cbstm03b.LkM03bArea) (h1 : 1 ≤ q.lk_m03b_key_ln.val) (h25 : q.lk_m03b_key_ln.val ≤ 25)
    (hd : ∀ b ∈ (Model.aKey (LkM03bArea.vals q)).take (Model.aKeyLn (LkM03bArea.vals q)).toNat,
      240 ≤ b ∧ b ≤ 249)
    (key : I64) (hkey : cbstm03b.acct_key q = .ok key) :
    key.val = Model.acctVal (Model.aKey (LkM03bArea.vals q)) (Model.aKeyLn (LkM03bArea.vals q)).toNat := by
  obtain ⟨r, hr, hrv⟩ := acct_key_eq q (by omega) h25
  rw [hkey] at hr
  obtain rfl : key = r := Result.ok_injective hr
  rw [aKey_vals, aKeyLn_vals] at hd ⊢
  have hkl : q.lk_m03b_key.val.length = 25 := q.lk_m03b_key.property
  have hdig : ∀ u ∈ q.lk_m03b_key.val.take q.lk_m03b_key_ln.val.toNat, 48 ≤ u.val ∧ u.val ≤ 57 := by
    intro u hu
    have := hd (ebcdicOfLatin1 u.val) (by rw [← List.map_take]; exact List.mem_map_of_mem hu)
    exact ebc_digit_inv ⟨u.val, by scalar_tac⟩ this.1 this.2
  have hLk : (q.lk_m03b_key.val.take q.lk_m03b_key_ln.val.toNat).length = q.lk_m03b_key_ln.val.toNat := by
    simp [hkl]
    omega
  rw [hrv, acctVal_digits _ _ (by omega) hLk hdig _ rfl,
    digitsVal_digits _ (fun u hu => hdig u (List.mem_of_mem_drop hu)), List.map_drop]
  have := ofDigits_drop_mod ((q.lk_m03b_key.val.take q.lk_m03b_key_ln.val.toNat).map (fun u => u.val - 48))
    q.lk_m03b_key_ln.val.toNat (by rw [List.length_map, hLk])
  exact_mod_cast this.symm

theorem acctKeyAgree_of (oe : Std.Array (Option U8) 4#usize) (st : cbstm03b.State) (q : cbstm03b.LkM03bArea)
    (h : CallHyp oe st q) : AcctKeyAgree q := by
  intro hk hA key hkey
  have hr := h.keyLn hk (Or.inr hA)
  rw [aKeyLn_vals] at hr
  exact acct_key_agree q hr.1 hr.2 (h.acctKey hk hA) key hkey

/-- **The equation of `call`** (`RustSpec.CallSpec`). -/
theorem call_spec : CallSpec := fun oe st q h => call_spec_of oe st q h (acctKeyAgree_of oe st q h)

end EquivLean.Modernize.Cbstm03b.Rust
