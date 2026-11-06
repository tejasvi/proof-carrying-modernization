import EquivLean.Modernize.Cbstm03a.Java.RecDefs

open Cobol Cobol.StmCore EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr digitChar argText StrOk space
  fixStr_length fixStr_eq_self fixStr_eq_take fixStr_eq_append zpadStr_length
  cp037Str_inj cp037Str_eq_iff cp037Str_length cp037Str_append cp037Str_take
  cp037_digit cp037_space cp037_replicate_space cp037Unit_inj)
open EquivLean.Modernize.Cbstm03a.StmBridge EquivLean.Modernize.Cbstm03a.Model

namespace EquivLean.Modernize.Cbstm03a.Java

/-! ## 1. `jeb` (`jline (bs.map cp037Code)` = `cp037Str bs`) and basic slicing/padding -/

def jeb (bs : List UInt8) : JStr := jline (bs.map cp037Code)

theorem jeb_eq_cp037Str (bs : List UInt8) : jeb bs = cp037Str bs := by
  simp [jeb, jline, cp037Str, cp037Unit, cp037Code, List.map_map, Function.comp_def]

@[simp] theorem jeb_nil : jeb [] = [] := rfl

theorem jeb_cons (b : UInt8) (bs : List UInt8) : jeb (b :: bs) = cp037Unit b :: jeb bs := by
  simp [jeb_eq_cp037Str, cp037Str]

theorem jeb_append (a b : List UInt8) : jeb (a ++ b) = jeb a ++ jeb b := by
  simp [jeb_eq_cp037Str, cp037Str_append]

@[simp] theorem jeb_length (bs : List UInt8) : (jeb bs).length = bs.length := by
  simp [jeb_eq_cp037Str, cp037Str_length]

theorem jeb_take (bs : List UInt8) (n : Nat) : (jeb bs).take n = jeb (bs.take n) := by
  simp [jeb_eq_cp037Str, cp037Str_take]

theorem jeb_drop (bs : List UInt8) (n : Nat) : (jeb bs).drop n = jeb (bs.drop n) := by
  simp [jeb, jline, ← List.map_drop]

theorem jeb_replicate (n : Nat) (b : UInt8) :
    jeb (List.replicate n b) = List.replicate n (cp037Unit b) := by
  simp [jeb_eq_cp037Str, cp037Str, List.map_replicate]

theorem jeb_inj {a b : List UInt8} : jeb a = jeb b ↔ a = b := by
  rw [jeb_eq_cp037Str, jeb_eq_cp037Str, cp037Str_eq_iff]

theorem sub_jeb (bs : List UInt8) (a b : Nat) :
    sub (jeb bs) a b = jeb ((bs.take b).drop a) := by
  simp [sub, jeb_take, jeb_drop]

theorem sub_jeb_fld (bs : List UInt8) (a b : Nat) :
    sub (jeb bs) a b = jeb (fld bs a (b - a)) := by
  rw [sub_jeb, List.drop_take]
  rfl

theorem jline_append (a b : List Nat) : jline (a ++ b) = jline a ++ jline b :=
  List.map_append ..

theorem map_jline_cp037Code (ls : List (List UInt8)) :
    (ls.map (·.map cp037Code)).map jline = ls.map jeb := by
  simp [jeb, List.map_map, Function.comp_def]

theorem fixStr_eq_take_append (s : JStr) (n : Nat) :
    fixStr s n = s.take n ++ List.replicate (n - s.length) space := by
  by_cases h : s.length ≤ n
  · rw [fixStr_eq_append h, List.take_of_length_le h]
  · rw [fixStr_eq_take (by omega), Nat.sub_eq_zero_of_le (by omega), List.replicate_zero,
      List.append_nil]

theorem ovw_eq_take_append_drop : ∀ (J B : List UInt8),
    ovw J B = J.take B.length ++ B.drop J.length
  | [], B => by simp [ovw]
  | _ :: _, [] => by simp [ovw]
  | b :: bs, c :: d => by
    simp only [ovw, List.length_cons, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    exact congrArg (b :: ·) (ovw_eq_take_append_drop bs d)

theorem ovw_sp_eq (J : List UInt8) (n : Nat) :
    ovw J (sp n) = J.take n ++ List.replicate (n - J.length) 64 := by
  rw [ovw_eq_take_append_drop]
  simp [sp, List.drop_replicate]

theorem fixStr_jeb (bs : List UInt8) (n : Nat) :
    fixStr (jeb bs) n = jeb (ovw bs (sp n)) := by
  rw [fixStr_eq_take_append, ovw_sp_eq, jeb_append, jeb_take, jeb_length, jeb_replicate, cp037_space]

theorem sl_jeb_of_len {bs : List UInt8} (h : bs.length = 80) : sl (jeb bs) = jeb bs :=
  fixStr_eq_self (by simp [h])

theorem hl_jeb_of_len {bs : List UInt8} (h : bs.length = 100) : hl (jeb bs) = jeb bs :=
  fixStr_eq_self (by simp [h])

/-! ## 2. `JStr.indexOf`, `cutAtT`, `appT`, `starT`, `paraT`, `stNameT`, `stAdd3T` -/

def findPat (pat : JStr) : JStr → Option Nat
  | [] => none
  | t@(_ :: rest) => if JStr.isPrefixOf pat t then some 0 else (findPat pat rest).map (· + 1)

theorem indexOf_go_eq (pat : JStr) (hpat : pat.isEmpty = false) :
    ∀ (s : JStr) (i : Nat),
      JStr.indexOf.go pat s i = match findPat pat s with
        | some m => ((i + m : Nat) : Int)
        | none => -1
  | [], i => by simp [JStr.indexOf.go, findPat, hpat]
  | c :: rest, i => by
    rw [JStr.indexOf.go, findPat]
    split
    · simp
    · rw [indexOf_go_eq pat hpat rest (i + 1)]
      cases findPat pat rest with
      | none => rfl
      | some m => simp [Nat.add_right_comm, Nat.add_assoc]

theorem cutAtT_eq_findPat (s pat : JStr) (hpat : pat.isEmpty = false) :
    cutAtT s pat = match findPat pat s with
      | some m => s.take m
      | none => s := by
  unfold cutAtT JStr.indexOf
  rw [indexOf_go_eq pat hpat s 0]
  cases findPat pat s with
  | none => simp
  | some m => simp

theorem cutAtT_single (d : JChar) : ∀ s : JStr, cutAtT s [d] = s.takeWhile (· != d)
  | [] => by rw [cutAtT_eq_findPat _ _ rfl]; rfl
  | x :: xs => by
    have ih := cutAtT_single d xs
    rw [cutAtT_eq_findPat _ _ rfl] at ih ⊢
    simp only [findPat, JStr.isPrefixOf, Bool.and_true, List.takeWhile_cons]
    by_cases h : x = d
    · subst h; simp
    · have hdx : (d == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
      have hxd : (x != d) = true := bne_iff_ne.mpr h
      simp only [hdx, Bool.false_eq_true, ↓reduceIte, hxd]
      rw [← ih]
      cases findPat [d] xs <;> rfl

theorem cutAtT_jeb_single (b : UInt8) (bs : List UInt8) :
    cutAtT (jeb bs) [cp037Unit b] = jeb (tokB b bs) := by
  rw [cutAtT_single]
  unfold tokB
  induction bs with
  | nil => rfl
  | cons x xs ih =>
    rw [jeb_cons, List.takeWhile_cons, List.takeWhile_cons]
    have heq : (cp037Unit x != cp037Unit b) = (x != b) := by
      rw [Bool.eq_iff_iff]
      simp only [bne_iff_ne, Ne]
      exact ⟨fun h e => h (e ▸ rfl), fun h e => h (cp037Unit_inj e)⟩
    rw [heq]
    split
    · rw [jeb_cons, ih]
    · rfl

theorem cp037_star : cp037Unit 92 = chStar := by decide +kernel

theorem cutAtT_jeb_star (bs : List UInt8) :
    cutAtT (jeb bs) [chStar] = jeb (tokB 92 bs) := by
  rw [← cp037_star, cutAtT_jeb_single]

theorem cutAtT_jeb_space (bs : List UInt8) :
    cutAtT (jeb bs) [space] = jeb (tokB 64 bs) := by
  rw [← cp037_space, cutAtT_jeb_single]

theorem cutAtT_double_nil (d : JChar) : cutAtT [] [d, d] = [] := by
  rw [cutAtT_eq_findPat _ _ rfl]; rfl

theorem cutAtT_double_single (d x : JChar) : cutAtT [x] [d, d] = [x] := by
  rw [cutAtT_eq_findPat _ _ rfl]
  simp [findPat, JStr.isPrefixOf]

theorem cutAtT_double_cons_cons (d x y : JChar) (rest : JStr) :
    cutAtT (x :: y :: rest) [d, d] =
      if x = d ∧ y = d then [] else x :: cutAtT (y :: rest) [d, d] := by
  rw [cutAtT_eq_findPat (x :: y :: rest) [d, d] rfl,
      cutAtT_eq_findPat (y :: rest) [d, d] rfl]
  rw [findPat]
  change (match if (d == x && (d == y && true)) = true then some 0
      else Option.map (· + 1) (findPat [d, d] (y :: rest)) with
    | some m => List.take m (x :: y :: rest)
    | none => x :: y :: rest) = _
  by_cases h : x = d ∧ y = d
  · obtain ⟨rfl, rfl⟩ := h; simp
  · have hp : (d == x && (d == y && true)) = false := by
      simp only [Bool.and_true, Bool.and_eq_false_iff]
      by_cases hx : x = d
      · right; exact beq_eq_false_iff_ne.mpr fun hy => h ⟨hx, hy.symm⟩
      · left; exact beq_eq_false_iff_ne.mpr (Ne.symm hx)
    simp only [hp, Bool.false_eq_true, ↓reduceIte, h]
    cases findPat [d, d] (y :: rest) <;> rfl

theorem cutAtT_jeb_space2 : ∀ bs : List UInt8,
    cutAtT (jeb bs) [space, space] = jeb (tok2 bs)
  | [] => by rw [jeb_nil, cutAtT_double_nil, tok2_nil, jeb_nil]
  | [x] => by rw [jeb_cons, jeb_nil, cutAtT_double_single, tok2_single, jeb_cons, jeb_nil]
  | x :: y :: rest => by
    rw [jeb_cons, jeb_cons, cutAtT_double_cons_cons, tok2_cons_cons]
    have heq : (cp037Unit x = space ∧ cp037Unit y = space) ↔ (x = 64 ∧ y = 64) := by
      rw [← cp037_space]
      exact ⟨fun ⟨h1, h2⟩ => ⟨cp037Unit_inj h1, cp037Unit_inj h2⟩,
             fun ⟨h1, h2⟩ => ⟨h1 ▸ rfl, h2 ▸ rfl⟩⟩
    simp only [heq]
    split
    · rfl
    · rw [jeb_cons, ← jeb_cons y rest, cutAtT_jeb_space2 (y :: rest)]

def pieceT (src : JStr) (delim : Option JStr) : JStr :=
  match delim with
  | none => src
  | some d => cutAtT src d

theorem take_append_take_sub (a b : JStr) (cap : Nat) :
    a.take cap ++ b.take (cap - (a.take cap).length) = (a ++ b).take cap := by
  have h : cap - (a.take cap).length = cap - a.length := by
    simp only [List.length_take]; omega
  rw [h, List.take_append]

theorem appT_take (a : JStr) (cap : Nat) (src : JStr) (delim : Option JStr) :
    appT (a.take cap) cap src delim = (a ++ pieceT src delim).take cap := by
  unfold appT pieceT
  exact take_append_take_sub a _ cap

theorem appT_nil (cap : Nat) (src : JStr) (delim : Option JStr) :
    appT [] cap src delim = (pieceT src delim).take cap := by
  simpa using appT_take [] cap src delim

theorem fixStr_take_self (a : JStr) (cap : Nat) :
    fixStr (a.take cap) cap = fixStr a cap := by
  rw [fixStr_eq_take_append, fixStr_eq_take_append, List.take_take, Nat.min_self, List.length_take]
  congr 2
  omega

theorem jl_tEndP : jl "</p>" = jeb tEndP := by decide +kernel
theorem jl_tP : jl "<p>" = jeb tP := by decide +kernel
theorem jl_tPStyle : jl "<p style=\"font-size:16px\">" = jeb tPStyle := by decide +kernel
theorem jl_tAcct : jl "<p>Account ID         : " = jeb tAcct := by decide +kernel
theorem jl_tBal : jl "<p>Current Balance    : " = jeb tBal := by decide +kernel
theorem jl_tFico : jl "<p>FICO Score         : " = jeb tFico := by decide +kernel

theorem tokB92_tEndP : tokB 92 tEndP = tEndP := by decide +kernel

theorem starT_jeb (pre field : List UInt8) (hpre : tokB 92 pre = pre) :
    starT (jeb pre) (jeb field) = jeb (hfield pre (tokB 92 field) tEndP) := by
  unfold starT hfield
  rw [appT_nil, appT_take, appT_take, fixStr_take_self]
  simp only [pieceT, jl_tEndP, cutAtT_jeb_star, hpre, tokB92_tEndP, ← jeb_append, fixStr_jeb]

theorem paraT_jeb (pre field : List UInt8) (hpre : tokB 92 pre = pre) :
    paraT (jeb pre) (jeb field) = jeb (hfield pre (tok2 field ++ [64, 64]) tEndP) := by
  unfold paraT hfield
  rw [appT_nil, appT_take, appT_take, appT_take, fixStr_take_self]
  simp only [pieceT, jl_tEndP, cutAtT_jeb_star, cutAtT_jeb_space2, hpre, tokB92_tEndP]
  have hsp2 : ([space, space] : JStr) = jeb [64, 64] := by decide +kernel
  rw [hsp2]
  simp only [← jeb_append, fixStr_jeb, List.append_assoc]

theorem stNameT_jeb (cr : List UInt8) :
    stNameT (jeb cr) = jeb (stName (fld cr 9 25) (fld cr 34 25) (fld cr 59 25)) := by
  unfold stNameT stName
  rw [appT_nil, appT_take, appT_take, appT_take, appT_take, appT_take, fixStr_take_self]
  have s1 : sub (jeb cr) 9 34 = jeb (fld cr 9 25) := sub_jeb_fld cr 9 34
  have s2 : sub (jeb cr) 34 59 = jeb (fld cr 34 25) := sub_jeb_fld cr 34 59
  have s3 : sub (jeb cr) 59 84 = jeb (fld cr 59 25) := sub_jeb_fld cr 59 84
  simp only [pieceT, s1, s2, s3, cutAtT_jeb_space]
  have hsp1 : ([space] : JStr) = jeb [64] := by decide +kernel
  rw [hsp1]
  simp only [← jeb_append, fixStr_jeb, List.append_assoc]

theorem stAdd3T_jeb (cr : List UInt8) :
    stAdd3T (jeb cr) = jeb (stAdd3 (fld cr 184 50) (fld cr 234 2) (fld cr 236 3) (fld cr 239 10)) := by
  unfold stAdd3T stAdd3
  rw [appT_nil, appT_take, appT_take, appT_take, appT_take, appT_take, appT_take, appT_take,
    fixStr_take_self]
  have s1 : sub (jeb cr) 184 234 = jeb (fld cr 184 50) := sub_jeb_fld cr 184 234
  have s2 : sub (jeb cr) 234 236 = jeb (fld cr 234 2) := sub_jeb_fld cr 234 236
  have s3 : sub (jeb cr) 236 239 = jeb (fld cr 236 3) := sub_jeb_fld cr 236 239
  have s4 : sub (jeb cr) 239 249 = jeb (fld cr 239 10) := sub_jeb_fld cr 239 249
  simp only [pieceT, s1, s2, s3, s4, cutAtT_jeb_space]
  have hsp1 : ([space] : JStr) = jeb [64] := by decide +kernel
  rw [hsp1]
  simp only [← jeb_append, fixStr_jeb, List.append_assoc]

/-! ## 3. Zoned decimal decoding (`decodeZonedI`, `zonedVal`) and editing (`fmtCurrBalI`, `fmtZI`, `fmtZStr`) -/

theorem zpadStr_eq_jline_zpad (n c : Nat) : zpadStr c n = jline (zpad n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ m ih =>
    rw [zpadStr, ih, zpad, zpad, toDigits_succ, List.map_append, jline_append]
    rfl

theorem zpadStr_mod (c m : Nat) : zpadStr (c % 10 ^ m) m = zpadStr c m := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih =>
    simp only [zpadStr]
    have h1 : c % 10 ^ (m + 1) / 10 = c / 10 % 10 ^ m := by
      rw [Nat.pow_succ, Nat.mul_comm (10 ^ m) 10, Nat.mod_mul_right_div_self]
    have h2 : c % 10 ^ (m + 1) % 10 = c % 10 := by
      rw [Nat.pow_succ]
      exact Nat.mod_mul_left_mod c (10 ^ m) 10
    rw [h1, h2, ih]

theorem jeb_encodeNum_signed (d : Nat) (sc : Int) (v : Int) :
    jeb (encodeNum {} { digits := d, scale := sc, signed := true } v) =
      zpadStr (v.natAbs / 10) (d - 1) ++
        [BitVec.ofNat 16 (overpunch (decide (v < 0)) (v.natAbs % 10))] := by
  rw [jeb, text_signed rfl rfl rfl rfl v, jline_append, ← zpadStr_eq_jline_zpad]
  rfl

theorem zdig_digitChar_fin : ∀ d : Fin 10, zdig (digitChar d.val) = d.val := by
  decide +kernel

theorem zdig_digitChar {d : Nat} (hd : d < 10) : zdig (digitChar d) = d :=
  zdig_digitChar_fin ⟨d, hd⟩

theorem foldl_zdig_zpadStr : ∀ (k m acc : Nat),
    (zpadStr m k).foldl (fun v d => v * 10 + zdig d) acc = acc * 10 ^ k + m % 10 ^ k
  | 0, m, acc => by simp [zpadStr, Nat.mod_one]
  | k + 1, m, acc => by
    rw [zpadStr, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_zdig_zpadStr k (m / 10) acc, zdig_digitChar (Nat.mod_lt _ (by decide))]
    have h1 : m / 10 % 10 ^ k = m % (10 * 10 ^ k) / 10 :=
      (Nat.mod_mul_right_div_self m 10 (10 ^ k)).symm
    have h2 : m % (10 * 10 ^ k) % 10 = m % 10 :=
      Nat.mod_mul_right_mod m 10 (10 ^ k)
    have h3 : (m % (10 * 10 ^ k) / 10) * 10 + m % (10 * 10 ^ k) % 10 = m % (10 * 10 ^ k) := by
      omega
    rw [h1, ← h2, Nat.pow_succ', Nat.add_mul, Nat.add_assoc, h3, Nat.mul_comm 10 (10 ^ k),
      Nat.mul_assoc]

theorem zlast_overpunch_fin : ∀ (neg : Bool) (d : Fin 10),
    zlast (BitVec.ofNat 16 (overpunch neg d.val)) = (d.val, neg) := by
  decide +kernel

theorem zlast_overpunch (neg : Bool) {d : Nat} (hd : d < 10) :
    zlast (BitVec.ofNat 16 (overpunch neg d)) = (d, neg) :=
  zlast_overpunch_fin neg ⟨d, hd⟩

theorem int_of_sign_natAbs (v : Int) :
    (if decide (v < 0) then -((v.natAbs : Nat) : Int) else ((v.natAbs : Nat) : Int)) = v := by
  cases v with
  | ofNat n => simp
  | negSucc n =>
    have h : Int.negSucc n < 0 := Int.negSucc_lt_zero n
    simp only [h, decide_true, ↓reduceIte, Int.natAbs_negSucc]
    rfl

theorem decodeZonedI_encodeNum {d : Nat} {sc : Int} (hd : 0 < d) {v : Int}
    (hv : v.natAbs < 10 ^ d) :
    decodeZonedI (jeb (encodeNum {} { digits := d, scale := sc, signed := true } v)) = v := by
  rw [jeb_encodeNum_signed]
  unfold decodeZonedI
  rw [List.getLast?_concat, List.dropLast_concat]
  dsimp only
  rw [foldl_zdig_zpadStr (d - 1) (v.natAbs / 10) 0,
    zlast_overpunch _ (Nat.mod_lt _ (by decide))]
  dsimp only
  have hdiv_lt : v.natAbs / 10 < 10 ^ (d - 1) := by
    have : 10 ^ d = 10 ^ (d - 1) * 10 := by
      conv => lhs; rw [← Nat.sub_add_cancel hd, Nat.pow_succ]
    omega
  rw [Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hdiv_lt]
  have hdm : v.natAbs / 10 * 10 + v.natAbs % 10 = v.natAbs := by omega
  rw [hdm]
  exact int_of_sign_natAbs v

theorem digitChar_bounds_fin : ∀ d : Fin 10,
    48 ≤ (digitChar d.val).toNat ∧ (digitChar d.val).toNat ≤ 57 ∧
      (digitChar d.val).toNat - 48 = d.val := by
  decide +kernel

theorem mem_zpadStr_digit {m k : Nat} {c : JChar} (hc : c ∈ zpadStr m k) :
    48 ≤ c.toNat ∧ c.toNat ≤ 57 ∧ c.toNat - 48 = zdig c := by
  induction k generalizing m with
  | zero => simp [zpadStr] at hc
  | succ k ih =>
    rw [zpadStr, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact ih hc
    · have hb := digitChar_bounds_fin ⟨m % 10, Nat.mod_lt _ (by decide)⟩
      have hz := zdig_digitChar_fin ⟨m % 10, Nat.mod_lt _ (by decide)⟩
      exact ⟨hb.1, hb.2.1, hb.2.2.trans hz.symm⟩

theorem zAcc_prefix (xs ys : JStr)
    (hxs : ∀ c ∈ xs, 48 ≤ c.toNat ∧ c.toNat ≤ 57 ∧ c.toNat - 48 = zdig c) :
    ∀ i, i ≤ xs.length →
      zAcc (xs ++ ys) i = ((xs.take i).foldl (fun v d => v * 10 + zdig d) 0, false)
  | 0, _ => rfl
  | i + 1, hi => by
    have hlt : i < xs.length := by omega
    have hget : (xs ++ ys).getD i 0 = xs[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt,
        Option.getD_some]
    obtain ⟨hb1, hb2, hb3⟩ := hxs xs[i] (List.getElem_mem hlt)
    rw [zAcc, hget, ite_eq_left_iff.mpr fun h => absurd ⟨hb1, hb2⟩ h,
      zAcc_prefix xs ys hxs i (by omega), hb3,
      List.take_succ_eq_append_getElem hlt, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem zLast_overpunch_fin : ∀ (neg : Bool) (d : Fin 10),
    ¬ (48 ≤ (BitVec.ofNat 16 (overpunch neg d.val)).toNat ∧
       (BitVec.ofNat 16 (overpunch neg d.val)).toNat ≤ 57) ∧
    zLast (BitVec.ofNat 16 (overpunch neg d.val)) false = (d.val, neg) := by
  decide +kernel

theorem zLast_overpunch (neg : Bool) {d : Nat} (hd : d < 10) :
    ¬ (48 ≤ (BitVec.ofNat 16 (overpunch neg d)).toNat ∧
       (BitVec.ofNat 16 (overpunch neg d)).toNat ≤ 57) ∧
    zLast (BitVec.ofNat 16 (overpunch neg d)) false = (d, neg) :=
  zLast_overpunch_fin neg ⟨d, hd⟩

theorem zonedVal_encodeNum {d : Nat} {sc : Int} (hd : 0 < d) {v : Int}
    (hv : v.natAbs < 10 ^ d) :
    zonedVal (jeb (encodeNum {} { digits := d, scale := sc, signed := true } v)) = v := by
  rw [jeb_encodeNum_signed]
  set xs := zpadStr (v.natAbs / 10) (d - 1)
  set c : JChar := BitVec.ofNat 16 (overpunch (decide (v < 0)) (v.natAbs % 10))
  have hlen : (xs ++ [c]).length = xs.length + 1 := by simp
  have hpre := zAcc_prefix xs [c] (fun u hu => mem_zpadStr_digit hu) xs.length (Nat.le_refl _)
  rw [List.take_length] at hpre
  have hget : (xs ++ [c]).getD xs.length 0 = c := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
    simp
  obtain ⟨hnot_dig, hzlast⟩ := zLast_overpunch (decide (v < 0)) (Nat.mod_lt (v.natAbs) (by decide))
  unfold zonedVal
  rw [hlen, zAcc, hget, ite_eq_right_iff.mpr fun h => absurd h hnot_dig,
    ite_eq_left_iff.mpr fun h => absurd hlen.symm h, hpre,
    foldl_zdig_zpadStr (d - 1) (v.natAbs / 10) 0]
  dsimp only
  rw [hzlast]
  dsimp only
  have hdiv_lt : v.natAbs / 10 < 10 ^ (d - 1) := by
    have : 10 ^ d = 10 ^ (d - 1) * 10 := by
      conv => lhs; rw [← Nat.sub_add_cancel hd, Nat.pow_succ]
    omega
  rw [Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hdiv_lt]
  have hdm : v.natAbs / 10 * 10 + v.natAbs % 10 = v.natAbs := by omega
  rw [hdm]
  exact int_of_sign_natAbs v

theorem toDigits_11_split (m : Nat) :
    Digits.toDigits 10 11 m =
      Digits.toDigits 10 9 (m / 100) ++ [m % 100 / 10, m % 10] := by
  have h1 : m / 10 % 10 = m % 100 / 10 := by
    rw [show (100 : Nat) = 10 * 10 from rfl, Nat.mod_mul_right_div_self]
  rw [toDigits_succ, toDigits_succ, Nat.div_div_eq_div_mul, h1]
  simp

theorem zpad_2_eq (m : Nat) :
    zpadStr (m % 100) 2 = [digitChar (m % 100 / 10), digitChar (m % 10)] := by
  have h1 : m % 100 / 10 % 10 = m % 100 / 10 :=
    Nat.mod_eq_of_lt (by have := Nat.mod_lt m (by decide : 0 < 100); omega)
  have h2 : m % 100 % 10 = m % 10 := Nat.mod_mul_left_mod m 10 10
  simp [zpadStr, h1, h2]

theorem jeb_digitByte (d : Nat) (hd : d < 10) :
    cp037Unit (({} : Config).digitByte d) = digitChar d := by
  rw [cp037Unit, ← cp037Code, cp037Code_digitByte d hd]
  rfl

theorem toDigits_map_digitChar (n c : Nat) :
    (Digits.toDigits 10 n c).map digitChar = zpadStr c n := by
  rw [zpadStr_eq_jline_zpad, zpad, jline, List.map_map]
  rfl

theorem rescale_2_2 (v : Int) : rescale .truncation v 2 (2 : Nat) = v := by
  simp [rescale]

abbrev ps9 : List Edit.Pos :=
  [.digit none, .digit none, .digit none, .digit none, .digit none, .digit none,
   .digit none, .digit none, .digit none, .point, .digit none, .digit none, .fixed .minus]

abbrev psZ : List Edit.Pos :=
  [.digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z),
   .digit (some .z), .digit (some .z), .digit (some .z), .digit (some .z), .point,
   .digit none, .digit none, .fixed .minus]

theorem edit9_unfold (v : Int) :
    edit9 v =
      (Edit.editOpt.gen {} 9 (Digits.toDigits 10 11 (v.natAbs % 100000000000))
        (decide (v < 0)) none 0 0 ps9).map (·.1) := by
  unfold edit9 Edit.edit Edit.editOpt
  have hf : Edit.floatSym pic9 = none := by decide
  have hb : Edit.floatBeforePoint ps9 = true := by decide
  have ha : ps9.all (fun p => p != Edit.Pos.digit none) = false := by decide
  simp only [classify_pic9, Option.bind_eq_bind, Option.bind_some, hf, hb, ha, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.false_and]
  change (Edit.editOpt.gen {} 9 (Digits.toDigits 10 11 ((rescale .truncation v 2 (2 : Nat)).natAbs % 100000000000))
    (decide (v < 0)) none (min 9 (min 0 _)) 0 ps9).map (·.1) = _
  rw [rescale_2_2, Nat.zero_min, Nat.min_zero]

theorem editZ_unfold (v : Int) :
    editZ v =
      (Edit.editOpt.gen {} 9 (Digits.toDigits 10 11 (v.natAbs % 100000000000))
        (decide (v < 0)) (some .z)
        (min 9 (((Digits.toDigits 10 11 (v.natAbs % 100000000000)).findIdx? (· != 0)).getD 11))
        0 psZ).map (·.1) := by
  unfold editZ Edit.edit Edit.editOpt
  have hf : Edit.floatSym picZ = none := by decide
  have hb : Edit.floatBeforePoint psZ = true := by decide
  have ha : psZ.all (fun p => p != Edit.Pos.digit none) = false := by decide
  simp only [classify_picZ, Option.bind_eq_bind, Option.bind_some, hf, hb, ha, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.false_and]
  change (Edit.editOpt.gen {} 9 (Digits.toDigits 10 11 ((rescale .truncation v 2 (2 : Nat)).natAbs % 100000000000))
    (decide (v < 0)) (some .z)
    (min 9 (min 9 (((Digits.toDigits 10 11 ((rescale .truncation v 2 (2 : Nat)).natAbs % 100000000000)).findIdx? (· != 0)).getD 11)))
    0 psZ).map (·.1) = _
  rw [rescale_2_2, ← Nat.min_assoc, Nat.min_self]

theorem fmtCurrBalI_eq_edit9 (v : Int) : fmtCurrBalI v = jeb (edit9 v) := by
  unfold fmtCurrBalI
  rw [edit9_unfold]
  set mag := v.natAbs % 100000000000
  have hlen9 : (Digits.toDigits 10 9 (mag / 100)).length = 9 := Digits.length_toDigits 10 9 _
  have hlt9 : ∀ d ∈ Digits.toDigits 10 9 (mag / 100), d < 10 :=
    fun d hd => Digits.toDigits_lt (by decide) 9 _ d hd
  rw [toDigits_11_split mag, ← toDigits_map_digitChar 9 (mag / 100), zpad_2_eq]
  generalize Digits.toDigits 10 9 (mag / 100) = d9 at hlen9 hlt9 ⊢
  match d9, hlen9 with
  | [d0, d1, d2, d3, d4, d5, d6, d7, d8], _ =>
    have h0 := hlt9 d0 (by simp); have h1 := hlt9 d1 (by simp); have h2 := hlt9 d2 (by simp)
    have h3 := hlt9 d3 (by simp); have h4 := hlt9 d4 (by simp); have h5 := hlt9 d5 (by simp)
    have h6 := hlt9 d6 (by simp); have h7 := hlt9 d7 (by simp); have h8 := hlt9 d8 (by simp)
    have jb0 := jeb_digitByte d0 h0; have jb1 := jeb_digitByte d1 h1; have jb2 := jeb_digitByte d2 h2
    have jb3 := jeb_digitByte d3 h3; have jb4 := jeb_digitByte d4 h4; have jb5 := jeb_digitByte d5 h5
    have jb6 := jeb_digitByte d6 h6; have jb7 := jeb_digitByte d7 h7; have jb8 := jeb_digitByte d8 h8
    have hd0 : cp037Unit (({} : Config).digitByte (mag % 100 / 10)) = digitChar (mag % 100 / 10) :=
      jeb_digitByte _ (by omega)
    have hd1 : cp037Unit (({} : Config).digitByte (mag % 10)) = digitChar (mag % 10) :=
      jeb_digitByte _ (by omega)
    have hdot : cp037Unit (Edit.symChar {} .dot) = chDot := by decide +kernel
    have hneg_t : cp037Unit (({} : Config).minusChar) = chDash := by decide +kernel
    have hneg_f : cp037Unit (({} : Config).space) = space := by decide +kernel
    by_cases hv : v < 0 <;>
      simp [Edit.editOpt.gen, Edit.fixedBytes, Edit.signChar, jeb_eq_cp037Str, cp037Str,
        jb0, jb1, jb2, jb3, jb4, jb5, jb6, jb7, jb8, hd0, hd1, hdot, hneg_t, hneg_f, hv]

theorem digitChar_beq_chZero {d : Nat} (hd : d < 10) :
    (digitChar d == chZero) = (d == 0) := by
  revert d; decide

@[simp] theorem digitChar_zero_beq_chZero : (digitChar 0 == chZero) = true := rfl

set_option linter.unusedSimpArgs false in
theorem fmtZI_eq_editZ (v : Int) : fmtZI v = jeb (editZ v) := by
  unfold fmtZI
  rw [editZ_unfold]
  set mag := v.natAbs % 100000000000
  have hlen9 : (Digits.toDigits 10 9 (mag / 100)).length = 9 := Digits.length_toDigits 10 9 _
  have hlt9 : ∀ d ∈ Digits.toDigits 10 9 (mag / 100), d < 10 :=
    fun d hd => Digits.toDigits_lt (by decide) 9 _ d hd
  rw [toDigits_11_split mag, ← toDigits_map_digitChar 9 (mag / 100), zpad_2_eq]
  generalize Digits.toDigits 10 9 (mag / 100) = d9 at hlen9 hlt9 ⊢
  match d9, hlen9 with
  | [d0, d1, d2, d3, d4, d5, d6, d7, d8], _ =>
    have h0 := hlt9 d0 (by simp); have h1 := hlt9 d1 (by simp); have h2 := hlt9 d2 (by simp)
    have h3 := hlt9 d3 (by simp); have h4 := hlt9 d4 (by simp); have h5 := hlt9 d5 (by simp)
    have h6 := hlt9 d6 (by simp); have h7 := hlt9 d7 (by simp); have h8 := hlt9 d8 (by simp)
    have jb0 := jeb_digitByte d0 h0; have jb1 := jeb_digitByte d1 h1; have jb2 := jeb_digitByte d2 h2
    have jb3 := jeb_digitByte d3 h3; have jb4 := jeb_digitByte d4 h4; have jb5 := jeb_digitByte d5 h5
    have jb6 := jeb_digitByte d6 h6; have jb7 := jeb_digitByte d7 h7; have jb8 := jeb_digitByte d8 h8
    have hd0 : cp037Unit (({} : Config).digitByte (mag % 100 / 10)) = digitChar (mag % 100 / 10) :=
      jeb_digitByte _ (by omega)
    have hd1 : cp037Unit (({} : Config).digitByte (mag % 10)) = digitChar (mag % 10) :=
      jeb_digitByte _ (by omega)
    have hdot : cp037Unit (Edit.symChar {} .dot) = chDot := by decide +kernel
    have hneg_t : cp037Unit (({} : Config).minusChar) = chDash := by decide +kernel
    have hneg_f : cp037Unit (({} : Config).space) = space := by decide +kernel
    have hmin9 : ∀ o : Option Nat, min 9 ((o.map (· + 9)).getD 11) = 9 := by
      intro o; cases o <;> simp
    by_cases e0 : d0 = 0
    · subst e0
      by_cases e1 : d1 = 0
      · subst e1
        by_cases e2 : d2 = 0
        · subst e2
          by_cases e3 : d3 = 0
          · subst e3
            by_cases e4 : d4 = 0
            · subst e4
              by_cases e5 : d5 = 0
              · subst e5
                by_cases e6 : d6 = 0
                · subst e6
                  by_cases e7 : d7 = 0
                  · subst e7
                    by_cases e8 : d8 = 0
                    · subst e8
                      have hfind : (([0, 0, 0, 0, 0, 0, 0, 0, 0] ++ [mag % 100 / 10, mag % 10]).findIdx? (· != 0)) =
                          ([mag % 100 / 10, mag % 10].findIdx? (· != 0)).map (fun i => i + 9) := by
                        simp [List.findIdx?_cons, Option.map_map, Function.comp_def, Nat.add_assoc]
                      rw [hfind, hmin9]
                      by_cases hv : v < 0 <;>
                        simp [lead0T, List.takeWhile_cons, List.takeWhile_nil,
                          Edit.editOpt.gen, Edit.fixedBytes,
                          Edit.signChar, jeb_eq_cp037Str, cp037Str, jb0, jb1, jb2, jb3, jb4, jb5,
                          jb6, jb7, jb8, hd0, hd1, hdot, hneg_t, hneg_f, hv]
                    · by_cases hv : v < 0 <;>
                        simp [lead0T, List.takeWhile_cons, digitChar_beq_chZero h8, e8, List.findIdx?_cons,
                          Edit.editOpt.gen, Edit.fixedBytes, Edit.signChar, jeb_eq_cp037Str,
                          cp037Str, jb0, jb1, jb2, jb3, jb4, jb5, jb6, jb7, jb8, hd0, hd1,
                          hdot, hneg_t, hneg_f, hv]
                  · by_cases hv : v < 0 <;>
                      simp [lead0T, List.takeWhile_cons, digitChar_beq_chZero h7, e7, List.findIdx?_cons,
                        Edit.editOpt.gen, Edit.fixedBytes, Edit.signChar, jeb_eq_cp037Str,
                        cp037Str, jb0, jb1, jb2, jb3, jb4, jb5, jb6, jb7, jb8, hd0, hd1,
                        hdot, hneg_t, hneg_f, hv]
                · by_cases hv : v < 0 <;>
                    simp [lead0T, List.takeWhile_cons, digitChar_beq_chZero h6, e6, List.findIdx?_cons,
                      Edit.editOpt.gen, Edit.fixedBytes, Edit.signChar, jeb_eq_cp037Str,
                      cp037Str, jb0, jb1, jb2, jb3, jb4, jb5, jb6, jb7, jb8, hd0, hd1,
                      hdot, hneg_t, hneg_f, hv]
              · by_cases hv : v < 0 <;>
                  simp [lead0T, List.takeWhile_cons, digitChar_beq_chZero h5, e5, List.findIdx?_cons,
                    Edit.editOpt.gen, Edit.fixedBytes, Edit.signChar, jeb_eq_cp037Str,
                    cp037Str, jb0, jb1, jb2, jb3, jb4, jb5, jb6, jb7, jb8, hd0, hd1,
                    hdot, hneg_t, hneg_f, hv]
            · by_cases hv : v < 0 <;>
                simp [lead0T, List.takeWhile_cons, digitChar_beq_chZero h4, e4, List.findIdx?_cons,
                  Edit.editOpt.gen, Edit.fixedBytes, Edit.signChar, jeb_eq_cp037Str,
                  cp037Str, jb0, jb1, jb2, jb3, jb4, jb5, jb6, jb7, jb8, hd0, hd1,
                  hdot, hneg_t, hneg_f, hv]
          · by_cases hv : v < 0 <;>
              simp [lead0T, List.takeWhile_cons, digitChar_beq_chZero h3, e3, List.findIdx?_cons,
                Edit.editOpt.gen, Edit.fixedBytes, Edit.signChar, jeb_eq_cp037Str,
                cp037Str, jb0, jb1, jb2, jb3, jb4, jb5, jb6, jb7, jb8, hd0, hd1,
                hdot, hneg_t, hneg_f, hv]
        · by_cases hv : v < 0 <;>
            simp [lead0T, List.takeWhile_cons, digitChar_beq_chZero h2, e2, List.findIdx?_cons,
              Edit.editOpt.gen, Edit.fixedBytes, Edit.signChar, jeb_eq_cp037Str,
              cp037Str, jb0, jb1, jb2, jb3, jb4, jb5, jb6, jb7, jb8, hd0, hd1,
              hdot, hneg_t, hneg_f, hv]
      · by_cases hv : v < 0 <;>
          simp [lead0T, List.takeWhile_cons, digitChar_beq_chZero h1, e1, List.findIdx?_cons,
            Edit.editOpt.gen, Edit.fixedBytes, Edit.signChar, jeb_eq_cp037Str,
            cp037Str, jb0, jb1, jb2, jb3, jb4, jb5, jb6, jb7, jb8, hd0, hd1,
            hdot, hneg_t, hneg_f, hv]
    · by_cases hv : v < 0 <;>
        simp [lead0T, List.takeWhile_cons, digitChar_beq_chZero h0, e0, List.findIdx?_cons,
          Edit.editOpt.gen, Edit.fixedBytes, Edit.signChar, jeb_eq_cp037Str,
          cp037Str, jb0, jb1, jb2, jb3, jb4, jb5, jb6, jb7, jb8, hd0, hd1,
          hdot, hneg_t, hneg_f, hv]

theorem lead0_eq_lead0T : ∀ s : JStr, lead0 s = lead0T s
  | [] => rfl
  | c :: s => by
    rw [lead0, lead0T, List.takeWhile_cons]
    have hc : digitChar 0 = chZero := rfl
    rw [hc]
    by_cases h : c = chZero
    · subst h; simp [lead0_eq_lead0T s, lead0T, Nat.add_comm]
    · have hb : (c == chZero) = false := beq_eq_false_iff_ne.mpr h
      simp [h, hb]

theorem fmtZStr_eq_fmtZI (v : Int) : fmtZStr v = fmtZI v := by
  unfold fmtZStr fmtZI
  have h1 : zpadStr (v.natAbs % 100000000000 / 100) 9 = zpadStr (v.natAbs / 100) 9 := by
    have : v.natAbs % 100000000000 / 100 = v.natAbs / 100 % 10 ^ 9 := by
      rw [show (100000000000 : Nat) = 100 * 10 ^ 9 from rfl, Nat.mod_mul_right_div_self]
    rw [this, zpadStr_mod]
  have h2 : zpadStr (v.natAbs % 100000000000 % 100) 2 = zpadStr v.natAbs 2 := by
    have : v.natAbs % 100000000000 % 100 = v.natAbs % 10 ^ 2 := by
      rw [show (100000000000 : Nat) = 10 ^ 9 * 100 from rfl]
      exact Nat.mod_mul_left_mod v.natAbs (10 ^ 9) 100
    rw [this, zpadStr_mod]
  have hdot : JStr.ofString "." = [chDot] := rfl
  have hsign : signStr v = [if v < 0 then chDash else space] := by
    unfold signStr; by_cases hv : v < 0 <;> simp [hv] <;> rfl
  rw [h1, h2, lead0_eq_lead0T, hdot, hsign]

theorem fmtZStr_eq_editZ (v : Int) : fmtZStr v = jeb (editZ v) := by
  rw [fmtZStr_eq_fmtZI, fmtZI_eq_editZ]

theorem trunc11Z_eq_fitNum (v : Int) :
    trunc11Z v =
      (Sem.fitNum {} { digits := 11, scale := 2, signed := true, usage := .packed } v).2 := by
  have hfb : ({ digits := 11, scale := 2, signed := true, usage := .packed } : NumFmt).fullBinary {} =
      false := rfl
  simp only [Sem.fitNum, ↓reduceIte, hfb, Bool.false_eq_true]
  rw [EquivLean.Modernize.GlueKit.fitDec_eq 11 v]
  unfold trunc11Z
  have h11 : (10 : Int) ^ 11 = ((100000000000 : Nat) : Int) := rfl
  rw [h11]
  by_cases h : v < 0
  · simp only [h, ↓reduceIte]
    rw [EquivLean.Modernize.GlueKit.tmod_neg_of_neg h,
      Int.tmod_eq_emod_of_nonneg (by omega)]
    have hn : -v = (v.natAbs : Int) := by omega
    rw [hn, ← Int.natCast_emod]
  · simp only [h, ↓reduceIte]
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    have hp : v = (v.natAbs : Int) := by omega
    conv => rhs; rw [hp, ← Int.natCast_emod]

/-! ## 4. `jCreateStatement`, `jWriteTrans`, `tailOf` -/

theorem hl_hfield (pre x post : List UInt8) :
    hl (jeb (hfield pre x post)) = jeb (hfield pre x post) := by
  apply hl_jeb_of_len
  simp [hfield, length_ovw, sp]

set_option maxRecDepth 100000 in
theorem hl_L01 : hl L01 = jeb hL01 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L02 : hl L02 = jeb hL02 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L03 : hl L03 = jeb hL03 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L04 : hl L04 = jeb hL04 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L05 : hl L05 = jeb hL05 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L06 : hl L06 = jeb hL06 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L07 : hl L07 = jeb hL07 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L08 : hl L08 = jeb hL08 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_LTRS : hl LTRS = jeb hLTRS := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_LTRE : hl LTRE = jeb hLTRE := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_LTDE : hl LTDE = jeb hLTDE := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L10 : hl L10 = jeb hL10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L15 : hl L15 = jeb hL15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L16 : hl L16 = jeb hL16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L17 : hl L17 = jeb hL17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L18 : hl L18 = jeb hL18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L22_35 : hl L22_35 = jeb hL22_35 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L30_42 : hl L30_42 = jeb hL30_42 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L31 : hl L31 = jeb hL31 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L43 : hl L43 = jeb hL43 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L47 : hl L47 = jeb hL47 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L48 : hl L48 = jeb hL48 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L50 : hl L50 = jeb hL50 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L51 : hl L51 = jeb hL51 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L53 : hl L53 = jeb hL53 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L54 : hl L54 = jeb hL54 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L58 : hl L58 = jeb hL58 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L61 : hl L61 = jeb hL61 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L64 : hl L64 = jeb hL64 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L75 : hl L75 = jeb hL75 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L78 : hl L78 = jeb hL78 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L79 : hl L79 = jeb hL79 := by decide +kernel
set_option maxRecDepth 100000 in
theorem hl_L80 : hl L80 = jeb hL80 := by decide +kernel

set_option maxRecDepth 100000 in
theorem jCreateStatement_eq {c a : List EquivLean.Cobol.Rec.FVal}
    (hc : CustomerRecord.Valid c) (ha : AccountRecord.Valid a) :
    jCreateStatement (jeb (CustomerRecord.encode c)) (jeb (AccountRecord.encode a)) =
      ((modelHeadStmt c a).map jline, (modelHeadHtml c a).map jline) := by
  unfold modelHeadStmt modelHeadHtml
  rw [map_jline_cp037Code, map_jline_cp037Code]
  obtain ⟨-, -, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ := cust_fields hc
  have h1l := (field_str_bytes customerRecord_contig hc 1 9 25 (by decide) ⟨false, rfl⟩ rfl rfl).2
  have h2l := (field_str_bytes customerRecord_contig hc 2 34 25 (by decide) ⟨false, rfl⟩ rfl rfl).2
  have h3l := (field_str_bytes customerRecord_contig hc 3 59 25 (by decide) ⟨false, rfl⟩ rfl rfl).2
  have h4l := (field_str_bytes customerRecord_contig hc 4 84 50 (by decide) ⟨false, rfl⟩ rfl rfl).2
  have h5l := (field_str_bytes customerRecord_contig hc 5 134 50 (by decide) ⟨false, rfl⟩ rfl rfl).2
  have h6l := (field_str_bytes customerRecord_contig hc 6 184 50 (by decide) ⟨false, rfl⟩ rfl rfl).2
  have h7l := (field_str_bytes customerRecord_contig hc 7 234 2 (by decide) ⟨false, rfl⟩ rfl rfl).2
  have h8l := (field_str_bytes customerRecord_contig hc 8 236 3 (by decide) ⟨false, rfl⟩ rfl rfl).2
  have h9l := (field_str_bytes customerRecord_contig hc 9 239 10 (by decide) ⟨false, rfl⟩ rfl rfl).2
  have hc17 := field_num_decode customerRecord_contig hc 17 329 3 { digits := 3 } (by decide) rfl rfl rfl
  have ha0 := (acct_fields ha).1
  have ha2 := field_num_decode accountRecord_contig ha 2 12 12
    { digits := 12, scale := 2, signed := true } (by decide) rfl rfl rfl
  have ha2_holds := (GlueKit.holds_display rfl).mp ha2.2.2
  set C := CustomerRecord.encode c
  set A := AccountRecord.encode a
  have hnm : stNameT (jeb C) =
      jeb (stName (strOf (c.getD 1 default)) (strOf (c.getD 2 default)) (strOf (c.getD 3 default))) := by
    rw [stNameT_jeb, h1, h2, h3]
  have ha1_sub : sub (jeb C) 84 134 = jeb (strOf (c.getD 4 default)) := by
    rw [sub_jeb_fld, show 134 - 84 = 50 from rfl, h4]
  have ha2_sub : sub (jeb C) 134 184 = jeb (strOf (c.getD 5 default)) := by
    rw [sub_jeb_fld, show 184 - 134 = 50 from rfl, h5]
  have ha3 : stAdd3T (jeb C) =
      jeb (stAdd3 (strOf (c.getD 6 default)) (strOf (c.getD 7 default))
        (strOf (c.getD 8 default)) (strOf (c.getD 9 default))) := by
    rw [stAdd3T_jeb, h6, h7, h8, h9]
  have haid_fix : fixStr (sub (jeb A) 0 11) 20 = jeb (stAcctId (numOf (a.getD 0 default))) := by
    have hs : sub (jeb A) 0 11 = jeb (Sem.digitChars {} 11 (numOf (a.getD 0 default)).natAbs) := by
      rw [sub_jeb, List.drop_zero, ha0]
    have hdl : (Sem.digitChars {} 11 (numOf (a.getD 0 default)).natAbs).length = 11 := by
      simp [Sem.digitChars]
    rw [hs, fixStr_jeb, ovw_sp_eq, hdl, List.take_of_length_le (by omega)]
    rfl
  have hbal_fmt : fmtCurrBalI (decodeZonedI (sub (jeb A) 12 24)) =
      jeb (edit9 (numOf (a.getD 2 default))) := by
    have hs : sub (jeb A) 12 24 =
        jeb (encodeNum {} { digits := 12, scale := 2, signed := true } (numOf (a.getD 2 default))) := by
      rw [sub_jeb_fld, show 24 - 12 = 12 from rfl]
      exact congrArg jeb ha2.1
    rw [hs, decodeZonedI_encodeNum (by decide) ha2_holds.1, fmtCurrBalI_eq_edit9]
  have hfico_fix : fixStr (sub (jeb C) 329 332) 20 = jeb (stFico (numOf (c.getD 17 default))) := by
    have hs : sub (jeb C) 329 332 = jeb (Sem.digitChars {} 3 (numOf (c.getD 17 default)).natAbs) := by
      rw [sub_jeb_fld, show 332 - 329 = 3 from rfl]
      unfold fld
      rw [hc17.1, StmBridge.encodeNum_unsigned_display (by decide)]
    have hdl : (Sem.digitChars {} 3 (numOf (c.getD 17 default)).natAbs).length = 3 := by
      simp [Sem.digitChars]
    rw [hs, fixStr_jeb, ovw_sp_eq, hdl, List.take_of_length_le (by omega)]
    rfl
  set nm := stName (strOf (c.getD 1 default)) (strOf (c.getD 2 default)) (strOf (c.getD 3 default))
  set a1 := strOf (c.getD 4 default)
  set a2 := strOf (c.getD 5 default)
  set a3 := stAdd3 (strOf (c.getD 6 default)) (strOf (c.getD 7 default))
    (strOf (c.getD 8 default)) (strOf (c.getD 9 default))
  set aidT := stAcctId (numOf (a.getD 0 default))
  set balT := edit9 (numOf (a.getD 2 default))
  set ficoT := stFico (numOf (c.getD 17 default))
  have hnml : nm.length = 75 := by simp [nm, stName, length_ovw, sp]
  have ha3l : a3.length = 80 := by simp [a3, stAdd3, length_ovw, sp]
  have haidl : aidT.length = 20 := by simp [aidT, stAcctId, Sem.digitChars, sp]
  have hball : balT.length = 13 := length_edit9 _
  have hficol : ficoT.length = 20 := by simp [ficoT, stFico, Sem.digitChars, sp]
  unfold jCreateStatement stmtHead htmlHead
  rw [hnm, ha1_sub, ha2_sub, ha3, haid_fix, hbal_fmt, hfico_fix]
  refine Prod.ext ?_ ?_
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    have kc2625 : List.replicate 5 space = jeb c2625 := by decide +kernel
    have kc2680 : List.replicate 30 space = jeb c2680 := by decide +kernel
    have kc2760 : List.replicate 30 space = jeb c2760 := by decide +kernel
    have kc3030 : jl "Account ID         :" = jeb c3030 := by decide +kernel
    have kc3070 : List.replicate 40 space = jeb c3070 := by decide +kernel
    have kc3110 : jl "Current Balance    :" = jeb c3110 := by decide +kernel
    have kc3143 : List.replicate 47 space = jeb c3143 := by decide +kernel
    have kc3190 : jl "FICO Score         :" = jeb c3190 := by decide +kernel
    have kc3230 : List.replicate 40 space = jeb c3230 := by decide +kernel
    refine ⟨by decide +kernel, ?_, ?_, ?_, sl_jeb_of_len ha3l, by decide +kernel,
      by decide +kernel, by decide +kernel, ?_, ?_, ?_, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    · rw [kc2625, ← jeb_append]; exact sl_jeb_of_len (by simp [hnml, c2625_lit])
    · rw [kc2680, ← jeb_append]; exact sl_jeb_of_len (by simp [h4l, c2680_lit])
    · rw [kc2760, ← jeb_append]; exact sl_jeb_of_len (by simp [h5l, c2760_lit])
    · rw [kc3030, kc3070, ← jeb_append, ← jeb_append]
      exact sl_jeb_of_len (by simp [haidl, c3030_lit, c3070_lit])
    · rw [kc3110, kc3143, ← jeb_append, ← jeb_append]
      exact sl_jeb_of_len (by simp [hball, c3110_lit, c3143_lit])
    · rw [kc3190, kc3230, ← jeb_append, ← jeb_append]
      exact sl_jeb_of_len (by simp [hficol, c3190_lit, c3230_lit])
  · have hnm50 : sub (jeb nm) 0 50 = jeb (nm.take 50) := by rw [sub_jeb, List.drop_zero]
    have hp1 : hl (paraT (jl "<p style=\"font-size:16px\">") (sub (jeb nm) 0 50)) =
        jeb (hfield tPStyle (tok2 (nm.take 50) ++ [64, 64]) tEndP) := by
      rw [jl_tPStyle, hnm50, paraT_jeb _ _ (by decide +kernel), hl_hfield]
    have hp2 : hl (paraT (jl "<p>") (jeb a1)) =
        jeb (hfield tP (tok2 a1 ++ [64, 64]) tEndP) := by
      rw [jl_tP, paraT_jeb _ _ (by decide +kernel), hl_hfield]
    have hp3 : hl (paraT (jl "<p>") (jeb a2)) =
        jeb (hfield tP (tok2 a2 ++ [64, 64]) tEndP) := by
      rw [jl_tP, paraT_jeb _ _ (by decide +kernel), hl_hfield]
    have hp4 : hl (paraT (jl "<p>") (jeb a3)) =
        jeb (hfield tP (tok2 a3 ++ [64, 64]) tEndP) := by
      rw [jl_tP, paraT_jeb _ _ (by decide +kernel), hl_hfield]
    have hs1 : hl (starT (jl "<p>Account ID         : ") (jeb aidT)) =
        jeb (hfield tAcct (tokB 92 aidT) tEndP) := by
      rw [jl_tAcct, starT_jeb _ _ (by decide +kernel), hl_hfield]
    have hs2 : hl (starT (jl "<p>Current Balance    : ") (jeb balT)) =
        jeb (hfield tBal (tokB 92 balT) tEndP) := by
      rw [jl_tBal, starT_jeb _ _ (by decide +kernel), hl_hfield]
    have hs3 : hl (starT (jl "<p>FICO Score         : ") (jeb ficoT)) =
        jeb (hfield tFico (tokB 92 ficoT) tEndP) := by
      rw [jl_tFico, starT_jeb _ _ (by decide +kernel), hl_hfield]
    have hl11 : hl (jl "<h3>Statement for Account Number: " ++ jeb aidT ++ jl "</h3>") =
        jeb (c3930 ++ aidT ++ c3984 ++ sp 41) := by
      have kc3930 : jl "<h3>Statement for Account Number: " = jeb c3930 := by decide +kernel
      have kc3984 : jl "</h3>" = jeb c3984 := by decide +kernel
      have hlen59 : (c3930 ++ aidT ++ c3984).length = 59 := by
        simp [haidl, c3930_lit, c3984_lit]
      rw [kc3930, kc3984, ← jeb_append, ← jeb_append, hl, fixStr_jeb, ovw_sp_eq, hlen59,
        List.take_of_length_le (by omega)]
      rfl
    simp only [List.map_cons, List.map_nil, hl11, hp1, hp2, hp3, hp4, hs1, hs2, hs3,
      hl_L01, hl_L02, hl_L03, hl_L04, hl_L05, hl_L06, hl_L07, hl_L08, hl_LTRS, hl_LTRE, hl_LTDE,
      hl_L10, hl_L15, hl_L16, hl_L17, hl_L18, hl_L22_35, hl_L30_42, hl_L31, hl_L43,
      hl_L47, hl_L48, hl_L50, hl_L51, hl_L53, hl_L54]

set_option maxRecDepth 100000 in
theorem jWriteTrans_rec {r : List UInt8} (hr : r.length = 350) :
    jWriteTrans (jeb (tId r)) (jeb (tRest r)) (tAmt r) =
      ([jeb (tranStmtR r)], (tranHtmlR r).map jeb) := by
  have hidl : (tId r).length = 16 := by simp [tId, hr]
  have hdescl : (tDesc r).length = 100 := by simp [tDesc, tRest, hr]
  have hsub_desc : sub (jeb (tRest r)) 16 65 = jeb ((tDesc r).take 49) := by
    rw [sub_jeb_fld, show 65 - 16 = 49 from rfl]
    unfold fld tDesc
    rw [List.take_take]
    rfl
  unfold jWriteTrans tranStmtR tranHtmlR
  rw [hsub_desc, fmtZI_eq_editZ]
  refine Prod.ext ?_ ?_
  · simp only [List.cons.injEq, and_true]
    have kc3606 : ([space] : JStr) = jeb c3606 := by decide +kernel
    have kc3656 : ([chDollar] : JStr) = jeb c3656 := by decide +kernel
    rw [kc3606, kc3656, ← jeb_append, ← jeb_append, ← jeb_append, ← jeb_append]
    unfold tranStmt
    apply sl_jeb_of_len
    have hel := length_editZ (tAmt r)
    simp [hidl, hdescl, hel, c3606_lit, c3656_lit]
  · have hs1 : hl (starT (jl "<p>") (jeb (tId r))) = jeb (hfield tP (tokB 92 (tId r)) tEndP) := by
      rw [jl_tP, starT_jeb _ _ (by decide +kernel), hl_hfield]
    have hs2 : hl (starT (jl "<p>") (jeb ((tDesc r).take 49))) =
        jeb (hfield tP (tokB 92 ((tDesc r).take 49)) tEndP) := by
      rw [jl_tP, starT_jeb _ _ (by decide +kernel), hl_hfield]
    have hs3 : hl (starT (jl "<p>") (jeb (editZ (tAmt r)))) =
        jeb (hfield tP (tokB 92 (editZ (tAmt r))) tEndP) := by
      rw [jl_tP, starT_jeb _ _ (by decide +kernel), hl_hfield]
    unfold tranHtml
    simp only [List.map_cons, List.map_nil, hs1, hs2, hs3,
      hl_LTRS, hl_L58, hl_LTDE, hl_L61, hl_L64, hl_LTRE]

set_option maxRecDepth 100000 in
theorem tailOf_eq (o : JOut) (total : I64) :
    tailOf o total =
      ⟨o.disp, o.stmt ++ (tailStmt total.toInt).map jeb,
       o.html ++ tailHtml.map jeb, o.ab⟩ := by
  unfold tailOf tailStmt tailHtml JOut.stmt1 JOut.html1
  rw [fmtZStr_eq_editZ]
  have hs1 : sl (List.replicate 80 chDash) = jeb c3430 := by decide +kernel
  have hs2 : sl (jl "Total EXP:" ++ List.replicate 56 space ++ jl "$" ++ jeb (editZ total.toInt)) =
      jeb (c3670 ++ editZ total.toInt) := by
    have kc3670 : jl "Total EXP:" ++ List.replicate 56 space ++ jl "$" = jeb c3670 := by
      decide +kernel
    rw [kc3670, ← jeb_append]
    apply sl_jeb_of_len
    have hel := length_editZ total.toInt
    simp [hel, c3670_lit]
  have hs3 : sl (List.replicate 32 chStar ++ jl "END OF STATEMENT" ++ List.replicate 32 chStar) =
      jeb c3750 := by decide +kernel
  rw [hs1, hs2, hs3]
  simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    hl_LTRS, hl_L10, hl_L75, hl_LTDE, hl_LTRE, hl_L78, hl_L79, hl_L80,
    List.append_assoc, List.cons_append, List.nil_append]

/-! ## 5. Table load (`ldStep`, `ldAll`, `ldFin` vs `grp`) -/

theorem sub_jeb_tCard (r : List UInt8) : sub (jeb r) 0 16 = jeb (tCard r) := by
  rw [sub_jeb, List.drop_zero]; rfl

theorem sub_jeb_tId (r : List UInt8) : sub (jeb r) 16 32 = jeb (tId r) := by
  rw [sub_jeb, List.drop_take]; rfl

theorem sub_jeb_tRest {r : List UInt8} (hr : r.length = 350) :
    sub (jeb r) 32 350 = jeb (tRest r) := by
  rw [sub_jeb, List.take_of_length_le (by omega)]; rfl

theorem recOf_jeb_350 {r : List UInt8} (hr : r.length = 350) :
    recOf (jeb r) 350 = jeb r := by
  unfold recOf sub
  rw [fixStr_eq_append (by simp [hr]), List.drop_zero,
    List.take_append_of_le_length (by simp [hr]), List.take_of_length_le (by simp [hr])]

theorem memRd_eq (m : Nat → JChar) (off : Int) (n : Nat) :
    memRd m off n = (List.range n).map (fun i : Nat =>
      if 0 ≤ off + (i : Int) ∧ off + (i : Int) < 171156 then m (off + (i : Int)).toNat else space) := by
  unfold memRd
  have h : ∀ l : List Nat, (do let a ← l; pure (a : Int)) = l.map Int.ofNat := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => exact congrArg ((a : Int) :: ·) ih
  rw [h, List.map_map]
  rfl

theorem memRd_memWr_same (m : Nat → JChar) (off : Int) (s : JStr)
    (h0 : 0 ≤ off) (h1 : off + s.length ≤ 171156) :
    memRd (memWr m off s) off s.length = s := by
  rw [memRd_eq]
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  simp only [List.getElem_map, List.getElem_range]
  have hb : 0 ≤ off + (i : Int) ∧ off + (i : Int) < 171156 := ⟨by omega, by omega⟩
  have hj : (off + (i : Int)).toNat < 171156 ∧
      off ≤ ((off + (i : Int)).toNat : Int) ∧
      ((off + (i : Int)).toNat : Int) < off + s.length := ⟨by omega, by omega, by omega⟩
  have hsub : (((off + (i : Int)).toNat : Int) - off).toNat = i := by omega
  rw [ite_eq_left_iff.mpr fun h => absurd hb h]
  dsimp only [memWr]
  rw [ite_eq_left_iff.mpr fun h => absurd hj h, hsub,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2, Option.getD_some]

theorem memRd_memWr_disj (m : Nat → JChar) (off1 : Int) (s : JStr) (off2 : Int) (n : Nat)
    (hdisj : off1 + s.length ≤ off2 ∨ off2 + n ≤ off1) :
    memRd (memWr m off1 s) off2 n = memRd m off2 n := by
  rw [memRd_eq, memRd_eq]
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < n := List.mem_range.mp hi
  split
  · rename_i hb
    have hnot : ¬ ((off2 + (i : Int)).toNat < 171156 ∧
        off1 ≤ ((off2 + (i : Int)).toNat : Int) ∧
        ((off2 + (i : Int)).toNat : Int) < off1 + s.length) := by
      rcases hdisj with h | h <;> omega
    dsimp only [memWr]
    rw [ite_eq_right_iff.mpr fun h => absurd h hnot]
  · rfl

theorem toInt_ofNat64_fin : ∀ n : Fin 100, (BitVec.ofNat 64 n.val).toInt = (n.val : Int) := by
  decide

theorem toInt_ofNat64_small {n : Nat} (h : n < 100) :
    (BitVec.ofNat 64 n).toInt = (n : Int) :=
  toInt_ofNat64_fin ⟨n, h⟩

theorem cardOffJ_toInt_fin : ∀ c : Fin 52, 1 ≤ c.val →
    (cardOffJ (BitVec.ofNat 64 c.val)).toInt = ((c.val : Int) - 1) * 3356 := by
  decide

theorem cardOffJ_toInt {c : Nat} (hc1 : 1 ≤ c) (hc2 : c ≤ 51) :
    (cardOffJ (BitVec.ofNat 64 c)).toInt = ((c : Int) - 1) * 3356 :=
  cardOffJ_toInt_fin ⟨c, by omega⟩ hc1

theorem tranOffJ_toInt_fin : ∀ (c : Fin 51) (t : Fin 11), 1 ≤ c.val → 1 ≤ t.val →
    (tranOffJ (BitVec.ofNat 64 c.val) (BitVec.ofNat 64 t.val)).toInt =
      ((c.val : Int) - 1) * 3356 + 16 + ((t.val : Int) - 1) * 334 ∧
    (tranOffJ (BitVec.ofNat 64 c.val) (BitVec.ofNat 64 t.val) + 16).toInt =
      ((c.val : Int) - 1) * 3356 + 16 + ((t.val : Int) - 1) * 334 + 16 := by
  decide

theorem tranOffJ_toInt {c t : Nat} (hc1 : 1 ≤ c) (hc2 : c ≤ 50) (ht1 : 1 ≤ t) (ht2 : t ≤ 10) :
    (tranOffJ (BitVec.ofNat 64 c) (BitVec.ofNat 64 t)).toInt =
      ((c : Int) - 1) * 3356 + 16 + ((t : Int) - 1) * 334 ∧
    (tranOffJ (BitVec.ofNat 64 c) (BitVec.ofNat 64 t) + 16).toInt =
      ((c : Int) - 1) * 3356 + 16 + ((t : Int) - 1) * 334 + 16 :=
  tranOffJ_toInt_fin ⟨c, by omega⟩ ⟨t, by omega⟩ hc1 ht1

theorem add1_srem_ofNat_fin : ∀ n : Fin 100,
    (BitVec.ofNat 64 n.val + 1).srem 10000 = BitVec.ofNat 64 (n.val + 1) := by
  decide

theorem add1_srem_ofNat {n : Nat} (hn : n < 100) :
    (BitVec.ofNat 64 n + 1).srem 10000 = BitVec.ofNat 64 (n + 1) :=
  add1_srem_ofNat_fin ⟨n, hn⟩

theorem trctSet_length (vs : List Jimple.Value) (cr v : I64) :
    (trctSet vs cr v).length = vs.length := by
  unfold trctSet
  split <;> simp

theorem trctGet_trctSet_same (vs : List Jimple.Value) {c : Nat} (v : I64)
    (hlen : vs.length = 51) (hc1 : 1 ≤ c) (hc2 : c ≤ 51) :
    trctGet (trctSet vs (BitVec.ofNat 64 c) v) (BitVec.ofNat 64 c) = .long v := by
  unfold trctGet trctSet
  rw [toInt_ofNat64_small (by omega)]
  have hb : 1 ≤ (c : Int) ∧ (c : Int) ≤ 51 := ⟨by omega, by omega⟩
  have hidx : ((c : Int) - 1).toNat = c - 1 := by omega
  simp only [hb, and_self, ↓reduceIte, hidx]
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega), Option.getD_some]

theorem trctGet_trctSet_ne (vs : List Jimple.Value) {c1 c2 : Nat} (v : I64)
    (hc1a : 1 ≤ c1) (hc1b : c1 ≤ 51) (hc2a : 1 ≤ c2) (hc2b : c2 ≤ 51) (hne : c1 ≠ c2) :
    trctGet (trctSet vs (BitVec.ofNat 64 c1) v) (BitVec.ofNat 64 c2) =
      trctGet vs (BitVec.ofNat 64 c2) := by
  unfold trctGet trctSet
  rw [toInt_ofNat64_small (by omega), toInt_ofNat64_small (by omega)]
  have hb1 : 1 ≤ (c1 : Int) ∧ (c1 : Int) ≤ 51 := ⟨by omega, by omega⟩
  have hb2 : 1 ≤ (c2 : Int) ∧ (c2 : Int) ≤ 51 := ⟨by omega, by omega⟩
  simp only [hb1, hb2, and_self, ↓reduceIte, List.getD_eq_getElem?_getD]
  rw [List.getElem?_set_ne (by omega)]

def JTableOk (m : Nat → JChar) (gs : List (List (List UInt8))) : Prop :=
  ∀ c, 1 ≤ c → c ≤ gs.length →
    let cr := BitVec.ofNat 64 c
    let g := gs.getD (c - 1) []
    memRd m (cardOffJ cr).toInt 16 = jeb (gCard g) ∧
    ∀ t, 1 ≤ t → t ≤ g.length →
      let tr := BitVec.ofNat 64 t
      memRd m (tranOffJ cr tr).toInt 16 = jeb (tId (g.getD (t - 1) [])) ∧
      memRd m (tranOffJ cr tr + 16).toInt 318 = jeb (tRest (g.getD (t - 1) []))

def JTrctOk (trct : List Jimple.Value) (gs : List (List (List UInt8))) (n : Nat) : Prop :=
  trct.length = 51 ∧
  ∀ c, 1 ≤ c → c ≤ n →
    trctGet trct (BitVec.ofNat 64 c) =
      .long (BitVec.ofNat 64 (gs.getD (c - 1) []).length)

def JLoadInv (s : LdSt) (gs : List (List (List UInt8))) : Prop :=
  1 ≤ gs.length ∧
  s.cr = BitVec.ofNat 64 gs.length ∧
  s.tr = BitVec.ofNat 64 (gs.getLastD []).length ∧
  s.save = jeb (gCard (gs.getLastD [])) ∧
  JTableOk s.m gs ∧
  JTrctOk s.trct gs (gs.length - 1)

theorem ldAll_append (s : LdSt) (a b : List JStr) :
    ldAll s (a ++ b) = ldAll (ldAll s a) b := by
  induction a generalizing s with
  | nil => rfl
  | cons r rs ih => exact ih (ldStep s r)

theorem mem_write_3 (m : Nat → JChar) {c t : Nat} {r : List UInt8}
    (hc1 : 1 ≤ c) (hc2 : c ≤ 50) (ht1 : 1 ≤ t) (ht2 : t ≤ 10) (hr : r.length = 350) :
    let cr := BitVec.ofNat 64 c
    let tr := BitVec.ofNat 64 t
    let m1 := memWr m (cardOffJ cr).toInt (jeb (tCard r))
    let m2 := memWr m1 (tranOffJ cr tr).toInt (jeb (tId r))
    let m3 := memWr m2 (tranOffJ cr tr + 16).toInt (jeb (tRest r))
    memRd m3 (cardOffJ cr).toInt 16 = jeb (tCard r) ∧
    memRd m3 (tranOffJ cr tr).toInt 16 = jeb (tId r) ∧
    memRd m3 (tranOffJ cr tr + 16).toInt 318 = jeb (tRest r) ∧
    (∀ t', 1 ≤ t' → t' < t →
      let tr' := BitVec.ofNat 64 t'
      memRd m3 (tranOffJ cr tr').toInt 16 = memRd m (tranOffJ cr tr').toInt 16 ∧
      memRd m3 (tranOffJ cr tr' + 16).toInt 318 = memRd m (tranOffJ cr tr' + 16).toInt 318) ∧
    (∀ c', 1 ≤ c' → c' < c →
      let cr' := BitVec.ofNat 64 c'
      memRd m3 (cardOffJ cr').toInt 16 = memRd m (cardOffJ cr').toInt 16 ∧
      ∀ t', 1 ≤ t' → t' ≤ 10 →
        let tr' := BitVec.ofNat 64 t'
        memRd m3 (tranOffJ cr' tr').toInt 16 = memRd m (tranOffJ cr' tr').toInt 16 ∧
        memRd m3 (tranOffJ cr' tr' + 16).toInt 318 = memRd m (tranOffJ cr' tr' + 16).toInt 318) := by
  dsimp only
  have hco := cardOffJ_toInt hc1 (by omega)
  obtain ⟨hto1, hto2⟩ := tranOffJ_toInt hc1 hc2 ht1 ht2
  have hcl : (jeb (tCard r)).length = 16 := by simp [tCard, hr]
  have hil : (jeb (tId r)).length = 16 := by simp [tId, hr]
  have hrl : (jeb (tRest r)).length = 318 := by simp [tRest, hr]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [memRd_memWr_disj _ _ _ _ _ (by omega),
        memRd_memWr_disj _ _ _ _ _ (by omega),
        ← hcl, memRd_memWr_same _ _ _ (by omega) (by omega)]
  · rw [memRd_memWr_disj _ _ _ _ _ (by omega),
        ← hil, memRd_memWr_same _ _ _ (by omega) (by omega)]
  · rw [← hrl, memRd_memWr_same _ _ _ (by omega) (by omega)]
  · intro t' ht'1 ht'2
    obtain ⟨hto1', hto2'⟩ := tranOffJ_toInt hc1 hc2 ht'1 (by omega)
    refine ⟨?_, ?_⟩
    · rw [memRd_memWr_disj _ _ _ _ _ (by omega),
          memRd_memWr_disj _ _ _ _ _ (by omega),
          memRd_memWr_disj _ _ _ _ _ (by omega)]
    · rw [memRd_memWr_disj _ _ _ _ _ (by omega),
          memRd_memWr_disj _ _ _ _ _ (by omega),
          memRd_memWr_disj _ _ _ _ _ (by omega)]
  · intro c' hc'1 hc'2
    have hco' := cardOffJ_toInt hc'1 (by omega)
    refine ⟨?_, fun t' ht'1 ht'2 => ?_⟩
    · rw [memRd_memWr_disj _ _ _ _ _ (by omega),
          memRd_memWr_disj _ _ _ _ _ (by omega),
          memRd_memWr_disj _ _ _ _ _ (by omega)]
    · obtain ⟨hto1', hto2'⟩ := tranOffJ_toInt hc'1 (by omega) ht'1 ht'2
      refine ⟨?_, ?_⟩
      · rw [memRd_memWr_disj _ _ _ _ _ (by omega),
            memRd_memWr_disj _ _ _ _ _ (by omega),
            memRd_memWr_disj _ _ _ _ _ (by omega)]
      · rw [memRd_memWr_disj _ _ _ _ _ (by omega),
            memRd_memWr_disj _ _ _ _ _ (by omega),
            memRd_memWr_disj _ _ _ _ _ (by omega)]

theorem ldStep_same (s : LdSt) {r : List UInt8} (hr : r.length = 350)
    (hs : s.save = jeb (tCard r)) :
    ldStep s (jeb r) =
      let tr := (s.tr + 1).srem 10000
      let m1 := memWr s.m (cardOffJ s.cr).toInt (jeb (tCard r))
      let m2 := memWr m1 (tranOffJ s.cr tr).toInt (jeb (tId r))
      let m3 := memWr m2 (tranOffJ s.cr tr + 16).toInt (jeb (tRest r))
      ⟨m3, s.trct, s.cr, tr, jeb (tCard r)⟩ := by
  simp only [ldStep, sub_jeb_tCard, sub_jeb_tId, sub_jeb_tRest hr, hs, ↓reduceIte]

theorem ldStep_diff (s : LdSt) {r : List UInt8} (hr : r.length = 350)
    (hs : s.save ≠ jeb (tCard r)) :
    ldStep s (jeb r) =
      let cr := (s.cr + 1).srem 10000
      let tr := BitVec.ofNat 64 1
      let m1 := memWr s.m (cardOffJ cr).toInt (jeb (tCard r))
      let m2 := memWr m1 (tranOffJ cr tr).toInt (jeb (tId r))
      let m3 := memWr m2 (tranOffJ cr tr + 16).toInt (jeb (tRest r))
      ⟨m3, trctSet s.trct s.cr s.tr, cr, tr, jeb (tCard r)⟩ := by
  unfold ldStep
  dsimp only
  rw [sub_jeb_tCard, sub_jeb_tId, sub_jeb_tRest hr, ite_eq_right_iff.mpr fun h => absurd h hs]
  rfl

theorem ldAll_inv (r0 : List UInt8) (hr0 : r0.length = 350) :
    ∀ (rs : List (List UInt8)),
      (∀ r ∈ r0 :: rs, r.length = 350) →
      (grp (r0 :: rs)).length ≤ 50 →
      (∀ g ∈ grp (r0 :: rs), g.length ≤ 10) →
      JLoadInv (ldAll (ld0 (jeb r0)) ((r0 :: rs).map jeb)) (grp (r0 :: rs)) := by
  intro rs
  induction rs using list_snoc_ind with
  | nil =>
    intro htl _ _
    have hgrp : grp [r0] = [[r0]] := rfl
    rw [hgrp]
    simp only [List.map_cons, List.map_nil, ldAll]
    have hsave0 : (ld0 (jeb r0)).save = jeb (tCard r0) := sub_jeb_tCard r0
    rw [ldStep_same (ld0 (jeb r0)) hr0 hsave0]
    dsimp only [ld0]
    have hcr1 : (1 : I64) = BitVec.ofNat 64 1 := rfl
    have htr1 : ((0 : I64) + 1).srem 10000 = BitVec.ofNat 64 1 := by decide
    rw [htr1, hcr1]
    obtain ⟨hmc, hmi, hmr, -, -⟩ :=
      mem_write_3 mem0 (c := 1) (t := 1) (by decide) (by decide) (by decide) (by decide) hr0
    refine ⟨by simp, rfl, rfl, rfl, ?_, ⟨by simp [trct0], fun c hc1 hc2 => ?_⟩⟩
    · intro c hc1 hc2
      simp only [List.length_singleton] at hc2
      obtain rfl : c = 1 := by omega
      refine ⟨hmc, fun t ht1 ht2 => ?_⟩
      simp only [Nat.sub_self, List.getD_cons_zero, List.length_singleton] at ht2 ⊢
      obtain rfl : t = 1 := by omega
      exact ⟨hmi, hmr⟩
    · simp only [List.length_singleton, Nat.sub_self] at hc2
      omega
  | snoc rs r ih =>
    intro htl hG hT
    have hcons : r0 :: (rs ++ [r]) = (r0 :: rs) ++ [r] := rfl
    rw [hcons, List.map_append, List.map_singleton, ldAll_append, ldAll, ldAll]
    have htl_pre : ∀ x ∈ r0 :: rs, x.length = 350 :=
      fun x hx => htl x (List.mem_append_left _ hx)
    have hr_len : r.length = 350 := htl r (by rw [hcons]; simp)
    obtain ⟨hG_pre, hT_pre_idx⟩ := grp_bounds (r0 :: rs) [r] hG hT
    have hT_pre : ∀ g ∈ grp (r0 :: rs), g.length ≤ 10 := by
      intro g hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      have := hT_pre_idx i hi
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
    have hinv := ih htl_pre hG_pre hT_pre
    obtain ⟨gs0, g, hgs, _⟩ := grp_snoc_form (r0 :: rs) (by simp)
    rw [hgs] at hinv
    obtain ⟨_, hcr, htr, hsave, htab, htrct_len, htrct⟩ := hinv
    simp only [List.length_append, List.length_singleton, getLastD_snoc, Nat.add_sub_cancel] at hcr htr hsave htrct
    generalize ldAll (ld0 (jeb r0)) (List.map jeb (r0 :: rs)) = s at hcr htr hsave htab htrct_len htrct ⊢
    by_cases hsame : gCard g = tCard r
    · have hgrp' : grp ((r0 :: rs) ++ [r]) = gs0 ++ [g ++ [r]] :=
        grp_snoc_same (r0 :: rs) r gs0 g hgs hsame
      rw [hgrp']
      have hG' : (gs0 ++ [g ++ [r]]).length ≤ 50 := by rwa [← hgrp', ← hcons]
      have hgl' : (g ++ [r]).length ≤ 10 := by
        apply hT; rw [hcons, hgrp']; simp
      simp only [List.length_append, List.length_singleton] at hG' hgl'
      have hcond : s.save = jeb (tCard r) := by rw [hsave, hsame]
      rw [ldStep_same s hr_len hcond, hcr, htr, add1_srem_ofNat (by omega)]
      dsimp only
      obtain ⟨hmc, hmi, hmr, hprev_t, hprev_c⟩ :=
        mem_write_3 s.m (c := gs0.length + 1) (t := g.length + 1)
          (by omega) (by omega) (by omega) (by omega) hr_len
      have hgcard' : gCard (g ++ [r]) = tCard r := by simp [gCard]
      refine ⟨by simp, ?_, ?_, ?_, ?_, ⟨htrct_len, ?_⟩⟩
      · simp
      · simp
      · simp [hgcard']
      · intro c hc1 hc2
        simp only [List.length_append, List.length_singleton] at hc2
        by_cases hc : c = gs0.length + 1
        · subst hc
          simp only [Nat.add_sub_cancel, getD_snoc_eq, hgcard']
          refine ⟨hmc, fun t ht1 ht2 => ?_⟩
          simp only [List.length_append, List.length_singleton] at ht2
          by_cases ht : t = g.length + 1
          · subst ht
            simp only [Nat.add_sub_cancel, getD_snoc_eq]
            exact ⟨hmi, hmr⟩
          · have ht_lt : t - 1 < g.length := by omega
            rw [getD_snoc_lt _ _ _ _ ht_lt]
            obtain ⟨-, ht_old⟩ := htab (gs0.length + 1) (by omega) (by simp)
            simp only [Nat.add_sub_cancel, getD_snoc_eq] at ht_old
            obtain ⟨ho1, ho2⟩ := ht_old t ht1 (by omega)
            obtain ⟨hp1, hp2⟩ := hprev_t t ht1 (by omega)
            exact ⟨hp1.trans ho1, hp2.trans ho2⟩
        · have hc_lt : c - 1 < gs0.length := by omega
          rw [getD_snoc_lt _ _ _ _ hc_lt]
          obtain ⟨hc_old, ht_old⟩ := htab c hc1 (by simp; omega)
          rw [getD_snoc_lt _ _ _ _ hc_lt] at hc_old ht_old
          obtain ⟨hpc, hpt⟩ := hprev_c c hc1 (by omega)
          refine ⟨hpc.trans hc_old, fun t ht1 ht2 => ?_⟩
          have ht10 : t ≤ 10 := by
            have hmem : gs0.getD (c - 1) [] ∈ grp (r0 :: rs) := by
              rw [hgs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc_lt, Option.getD_some]
              exact List.mem_append_left _ (List.getElem_mem _)
            have := hT_pre _ hmem
            omega
          obtain ⟨hp1, hp2⟩ := hpt t ht1 ht10
          obtain ⟨ho1, ho2⟩ := ht_old t ht1 ht2
          exact ⟨hp1.trans ho1, hp2.trans ho2⟩
      · intro c hc1 hc2
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hc2
        have hc_lt : c - 1 < gs0.length := by omega
        rw [getD_snoc_lt _ _ _ _ hc_lt]
        have ho := htrct c hc1 hc2
        rwa [getD_snoc_lt _ _ _ _ hc_lt] at ho
    · have hgrp' : grp ((r0 :: rs) ++ [r]) = gs0 ++ [g] ++ [[r]] :=
        grp_snoc_diff (r0 :: rs) r gs0 g hgs hsame
      rw [hgrp']
      have hG' : (gs0 ++ [g] ++ [[r]]).length ≤ 50 := by rwa [← hgrp', ← hcons]
      simp only [List.length_append, List.length_singleton] at hG'
      have hcond : s.save ≠ jeb (tCard r) := by
        rw [hsave, Ne, jeb_inj]
        exact hsame
      rw [ldStep_diff s hr_len hcond, hcr, htr, add1_srem_ofNat (by omega)]
      dsimp only
      obtain ⟨hmc, hmi, hmr, -, hprev_c⟩ :=
        mem_write_3 s.m (c := gs0.length + 1 + 1) (t := 1)
          (by omega) (by omega) (by decide) (by decide) hr_len
      have hgcard' : gCard [r] = tCard r := rfl
      refine ⟨by simp; omega, ?_, ?_, ?_, ?_, ⟨by rw [trctSet_length, htrct_len], ?_⟩⟩
      · simp
      · simp
      · simp [hgcard']
      · intro c hc1 hc2
        simp only [List.length_append, List.length_singleton] at hc2
        by_cases hc : c = gs0.length + 1 + 1
        · subst hc
          have he1 : gs0.length + 1 + 1 - 1 = (gs0 ++ [g]).length := by simp
          rw [he1, getD_snoc_eq]
          refine ⟨hmc, fun t ht1 ht2 => ?_⟩
          simp only [List.length_singleton] at ht2
          obtain rfl : t = 1 := by omega
          exact ⟨hmi, hmr⟩
        · have hc_le : c ≤ gs0.length + 1 := by omega
          have hc_lt : c - 1 < (gs0 ++ [g]).length := by
            rw [List.length_append, List.length_singleton]; omega
          rw [getD_snoc_lt _ _ _ _ hc_lt]
          obtain ⟨hc_old, ht_old⟩ := htab c hc1 (by rw [List.length_append, List.length_singleton]; omega)
          obtain ⟨hpc, hpt⟩ := hprev_c c hc1 (by omega)
          refine ⟨hpc.trans hc_old, fun t ht1 ht2 => ?_⟩
          have ht10 : t ≤ 10 := by
            have hmem : (gs0 ++ [g]).getD (c - 1) [] ∈ grp (r0 :: rs) := by
              rw [hgs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc_lt, Option.getD_some]
              exact List.getElem_mem _
            have := hT_pre _ hmem
            omega
          obtain ⟨hp1, hp2⟩ := hpt t ht1 ht10
          obtain ⟨ho1, ho2⟩ := ht_old t ht1 ht2
          exact ⟨hp1.trans ho1, hp2.trans ho2⟩
      · intro c hc1 hc2
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hc2
        have hc_lt : c - 1 < (gs0 ++ [g]).length := by
          rw [List.length_append, List.length_singleton]; omega
        rw [getD_snoc_lt _ _ _ _ hc_lt]
        by_cases hc : c = gs0.length + 1
        · subst hc
          rw [Nat.add_sub_cancel, getD_snoc_eq,
            trctGet_trctSet_same _ _ htrct_len (by omega) (by omega)]
        · rw [trctGet_trctSet_ne _ _ (by omega) (by omega) hc1 (by omega) (by omega)]
          exact htrct c hc1 (by omega)

theorem ldFin_of_inv {s : LdSt} {gs : List (List (List UInt8))}
    (hG : gs.length ≤ 50) (hinv : JLoadInv s gs) :
    1 ≤ gs.length ∧
    (ldFin s).cr = BitVec.ofNat 64 gs.length ∧
    JTableOk (ldFin s).m gs ∧
    JTrctOk (ldFin s).trct gs gs.length := by
  obtain ⟨hpos, hcr, htr, -, htab, htrct_len, htrct⟩ := hinv
  have hlast : (gs.getLastD []).length = (gs.getD (gs.length - 1) []).length := by
    rw [getLastD_eq_getD]
  unfold ldFin
  dsimp only
  refine ⟨hpos, hcr, htab, ⟨by rw [trctSet_length, htrct_len], fun c hc1 hc2 => ?_⟩⟩
  rw [hcr, htr, hlast]
  by_cases hc : c = gs.length
  · subst hc
    exact trctGet_trctSet_same _ _ htrct_len hc1 (by omega)
  · rw [trctGet_trctSet_ne _ _ (by omega) (by omega) hc1 (by omega) (Ne.symm hc)]
    exact htrct c hc1 (by omega)

theorem ldFin_ldAll_ok {r0 : List UInt8} {rs : List (List UInt8)}
    (htl : ∀ r ∈ r0 :: rs, r.length = 350)
    (hG : (grp (r0 :: rs)).length ≤ 50)
    (hT : ∀ g ∈ grp (r0 :: rs), g.length ≤ 10) :
    let trs := r0 :: rs
    let gs := grp trs
    let ld := ldFin (ldAll (ld0 (recOf (jeb r0) 350)) ((trs.map jeb).map (recOf · 350)))
    1 ≤ gs.length ∧
    ld.cr = BitVec.ofNat 64 gs.length ∧
    JTableOk ld.m gs ∧
    JTrctOk ld.trct gs gs.length := by
  have hr0 : r0.length = 350 := htl r0 (List.mem_cons_self ..)
  have hmap : ((r0 :: rs).map jeb).map (recOf · 350) = (r0 :: rs).map jeb := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    dsimp only [Function.comp_apply]
    exact recOf_jeb_350 (htl r hr)
  dsimp only
  rw [recOf_jeb_350 hr0, hmap]
  exact ldFin_of_inv hG (ldAll_inv r0 hr0 rs htl hG hT)

/-! ## 6. `ebcCmp`, `transOf`, and `cardsFrom` -/

set_option maxRecDepth 100000 in
theorem ebcIdx_cp037Unit_fin : ∀ n : Fin 256,
    ebcIdx (cp037Unit (UInt8.ofNat n.val)).toNat = n.val := by
  decide +kernel

theorem ebcIdx_cp037Unit (b : UInt8) :
    ebcIdx (cp037Unit b).toNat = b.toNat := by
  have h := ebcIdx_cp037Unit_fin ⟨b.toNat, b.toNat_lt⟩
  simpa only [UInt8.ofNat_toNat] using h

def ordInt : Ordering → Int
  | .lt => -1
  | .eq => 0
  | .gt => 1

theorem ebcScan_jeb : ∀ (a b : List UInt8), a.length = b.length →
    ebcScan (jeb a) (jeb b) = ordInt (Sem.cmpBytes a b)
  | [], [], _ => rfl
  | x :: xs, y :: ys, hlen => by
    rw [jeb_cons, jeb_cons, ebcScan, Sem.cmpBytes.eq_1, ebcIdx_cp037Unit, ebcIdx_cp037Unit]
    have hlen' : xs.length = ys.length := by simpa using hlen
    by_cases hxy : x = y
    · subst hxy
      simp [UInt8.lt_irrefl, ebcScan_jeb xs ys hlen']
    · have hunit : cp037Unit x ≠ cp037Unit y := fun e => hxy (cp037Unit_inj e)
      have hnat : x.toNat ≠ y.toNat := fun e => hxy (UInt8.toNat_inj.mp e)
      rw [ite_eq_left_iff.mpr fun h => absurd ⟨hunit, hnat⟩ h]
      by_cases hlt : x < y
      · have hlt' : x.toNat < y.toNat := UInt8.lt_iff_toNat_lt.mp hlt
        simp [hlt, hlt', ordInt]
      · have hgt : y < x := by rw [UInt8.lt_iff_toNat_lt] at hlt ⊢; omega
        have hnlt' : ¬ x.toNat < y.toNat := by rw [UInt8.lt_iff_toNat_lt] at hlt; exact hlt
        simp [hlt, hgt, hnlt', ordInt]

theorem ebcCmp_jeb {a b : List UInt8} (hlen : a.length = b.length) :
    ebcCmp (jeb a) (jeb b) = ordInt (Sem.cmpBytes a b) := by
  unfold ebcCmp
  by_cases h : jeb a = jeb b
  · have hab : a = b := jeb_inj.mp h
    subst hab
    rw [ite_eq_left_iff.mpr fun h' => absurd h h', Cobol.cmpBytes_self]
    rfl
  · rw [ite_eq_right_iff.mpr fun h' => absurd h' h]
    have hm : max (jeb a).length (jeb b).length = a.length := by simp [hlen]
    rw [hm, fixStr_eq_self (by simp), fixStr_eq_self (by simp [hlen]), ebcScan_jeb a b hlen]

theorem ebcCmp_pos_iff {a b : List UInt8} (hlen : a.length = b.length) :
    0 < ebcCmp (jeb a) (jeb b) ↔ Sem.cmpBytes a b = .gt := by
  rw [ebcCmp_jeb hlen]
  cases Sem.cmpBytes a b <;> simp [ordInt]

theorem toInt_ofInt64_small {x : Int} (hx : x.natAbs < 200000000000) :
    (BitVec.ofInt 64 x).toInt = x := by
  rw [BitVec.toInt_ofInt, Int.bmod_def]
  have h2 : ((2 : Nat) ^ 64 : Nat) = 18446744073709551616 := by decide
  simp only [h2]
  split <;> omega

theorem add_ofInt64_toInt {a b : Int} (ha : a.natAbs < 100000000000) (hb : b.natAbs < 100000000000) :
    (BitVec.ofInt 64 a + BitVec.ofInt 64 b).toInt = a + b := by
  rw [BitVec.toInt_add, toInt_ofInt64_small (by omega), toInt_ofInt64_small (by omega), Int.bmod_def]
  have h2 : ((2 : Nat) ^ 64 : Nat) = 18446744073709551616 := by decide
  simp only [h2]
  split <;> omega

theorem ofNat64_add_one_fin : ∀ n : Fin 100,
    BitVec.ofNat 64 n.val + 1 = BitVec.ofNat 64 (n.val + 1) := by
  decide

theorem ofNat64_add_one {n : Nat} (h : n < 100) :
    BitVec.ofNat 64 n + 1 = BitVec.ofNat 64 (n + 1) :=
  ofNat64_add_one_fin ⟨n, h⟩

def EncTrnxOk (r : List UInt8) : Prop :=
  r.length = 350 ∧
  (tAmt r).natAbs < 100000000000 ∧
  ((tRest r).drop 116).take 11 =
    encodeNum {} { digits := 11, scale := 2, signed := true } (tAmt r)

theorem encTrnxOk_of_valid {v : List EquivLean.Cobol.Rec.FVal} (hv : TrnxRecord.Valid v) :
    EncTrnxOk (TrnxRecord.encode v) := by
  have hlen := trnx_length hv
  have h6 := field_num_decode trnxRecord_contig hv 6 148 11
    { digits := 11, scale := 2, signed := true } (by decide) rfl rfl rfl
  have hh := (GlueKit.holds_display rfl).mp h6.2.2
  have hta := (trnx_fields hv).2.2.2.2.2.2.1
  have ha : ((tRest (TrnxRecord.encode v)).drop 116).take 11 =
      ((TrnxRecord.encode v).drop 148).take 11 := by
    simp [tRest, List.drop_drop]
  exact ⟨hlen, by rw [hta]; exact hh.1, by rw [ha, hta, h6.1]⟩

theorem zonedVal_tRest {r : List UInt8} (hr : EncTrnxOk r) :
    zonedVal (sub (jeb (tRest r)) 116 127) = tAmt r := by
  have hs : sub (jeb (tRest r)) 116 127 =
      jeb (encodeNum {} { digits := 11, scale := 2, signed := true } (tAmt r)) := by
    rw [sub_jeb_fld, show 127 - 116 = 11 from rfl]
    exact congrArg jeb hr.2.2
  rw [hs]
  exact zonedVal_encodeNum (by decide) hr.2.1

theorem transOf_take (m : Nat → JChar) (crJmp : I64) (g : List (List UInt8))
    (hg : ∀ r ∈ g, EncTrnxOk r)
    (hent : ∀ t, 1 ≤ t → t ≤ g.length →
      let tr := BitVec.ofNat 64 t
      memRd m (tranOffJ crJmp tr).toInt 16 = jeb (tId (g.getD (t - 1) [])) ∧
      memRd m (tranOffJ crJmp tr + 16).toInt 318 = jeb (tRest (g.getD (t - 1) []))) :
    ∀ k, k ≤ g.length → ∀ (o : JOut) (tot : Int), tot.natAbs < 100000000000 →
      transOf m crJmp k (o, BitVec.ofInt 64 tot) =
        (⟨o.disp,
          o.stmt ++ ((g.take k).map tranStmtR).map jeb,
          o.html ++ ((g.take k).flatMap tranHtmlR).map jeb,
          o.ab⟩,
         BitVec.ofInt 64 ((g.take k).foldl addAmt tot))
  | 0, _, o, tot, _ => by
    simp [transOf]
  | k + 1, hk, o, tot, htot => by
    have hlt : k < g.length := by omega
    have ih := transOf_take m crJmp g hg hent k (by omega) o tot htot
    set r := g[k]
    have hget : g.getD k [] = r := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    have hr : EncTrnxOk r := hg r (List.getElem_mem hlt)
    obtain ⟨htid, htrest⟩ := hent (k + 1) (by omega) hk
    simp only [Nat.add_sub_cancel, hget] at htid htrest
    set tot_k := (g.take k).foldl addAmt tot
    have htot_k : tot_k.natAbs < 100000000000 := foldl_addAmt_lt tot htot (g.take k)
    rw [transOf, ih]
    dsimp only
    rw [htid, htrest, zonedVal_tRest hr, toInt_ofInt64_small (by have := hr.2.1; omega),
      jWriteTrans_rec hr.1, add_ofInt64_toInt htot_k hr.2.1, trunc11Z_eq_fitNum]
    have htake : g.take (k + 1) = g.take k ++ [r] := List.take_succ_eq_append_getElem hlt
    rw [htake]
    simp [JOut.add, addAmt, tot_k, List.append_assoc]

theorem transOf_group (m : Nat → JChar) (crJmp : I64) (g : List (List UInt8))
    (hg : ∀ r ∈ g, EncTrnxOk r)
    (hent : ∀ t, 1 ≤ t → t ≤ g.length →
      let tr := BitVec.ofNat 64 t
      memRd m (tranOffJ crJmp tr).toInt 16 = jeb (tId (g.getD (t - 1) [])) ∧
      memRd m (tranOffJ crJmp tr + 16).toInt 318 = jeb (tRest (g.getD (t - 1) [])))
    (o : JOut) (tot : Int) (htot : tot.natAbs < 100000000000) :
    transOf m crJmp g.length (o, BitVec.ofInt 64 tot) =
      (⟨o.disp,
        o.stmt ++ (g.map tranStmtR).map jeb,
        o.html ++ (g.flatMap tranHtmlR).map jeb,
        o.ab⟩,
       BitVec.ofInt 64 (g.foldl addAmt tot)) := by
  have h := transOf_take m crJmp g hg hent g.length (Nat.le_refl _) o tot htot
  simpa only [List.take_length] using h

theorem gCard_length_of_ne_nil {g : List (List UInt8)} (hne : g ≠ [])
    (hg : ∀ r ∈ g, EncTrnxOk r) : (gCard g).length = 16 := by
  have hmem := getLastD_mem_of_ne_nil [] hne
  have hlen := (hg _ hmem).1
  unfold gCard tCard
  rw [List.length_take, hlen]
  rfl

theorem cardsFrom_vis (m : Nat → JChar) (trct : List Jimple.Value)
    (gs : List (List (List UInt8))) (hG : gs.length ≤ 50)
    (hgs : ∀ g ∈ gs, g ≠ [] ∧ g.length ≤ 10 ∧ ∀ r ∈ g, EncTrnxOk r)
    (htab : JTableOk m gs) (htrct : JTrctOk trct gs gs.length)
    (X : List UInt8) (hX : X.length = 16) :
    ∀ (n c : Nat), 1 ≤ c → c + n = gs.length + 1 →
      ∀ (o : JOut) (tot : Int), tot.natAbs < 100000000000 →
        cardsFrom m trct (BitVec.ofNat 64 gs.length) (jeb X) n (BitVec.ofNat 64 c)
            (o, BitVec.ofInt 64 tot) =
          let V := vis X (gs.drop (c - 1))
          (⟨o.disp,
            o.stmt ++ (V.flatMap (matchStmt X)).map jeb,
            o.html ++ (V.flatMap (matchHtml X)).map jeb,
            o.ab⟩,
           BitVec.ofInt 64 (V.foldl (accStep X) tot))
  | 0, c, hc1, hcn, o, tot, _ => by
    have hdrop : gs.drop (c - 1) = [] := List.drop_of_length_le (by omega)
    simp [cardsFrom, hdrop, vis]
  | n + 1, c, hc1, hcn, o, tot, htot => by
    have hcle : c ≤ gs.length := by omega
    have hclt : c - 1 < gs.length := by omega
    set g := gs[c - 1]
    have hget : gs.getD (c - 1) [] = g := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hclt, Option.getD_some]
    have hdrop : gs.drop (c - 1) = g :: gs.drop c := by
      conv => lhs; rw [List.drop_eq_getElem_cons hclt]
      rw [show c - 1 + 1 = c by omega]
    obtain ⟨hne, hgl, hg_ok⟩ := hgs g (List.getElem_mem hclt)
    have hgcard_len : (gCard g).length = 16 := gCard_length_of_ne_nil hne hg_ok
    obtain ⟨hcard_rd, hent_rd⟩ := htab c hc1 hcle
    rw [hget] at hcard_rd hent_rd
    have hcmp_le : ¬ ((BitVec.ofNat 64 gs.length).toInt < (BitVec.ofNat 64 c).toInt) := by
      rw [toInt_ofNat64_small (by omega), toInt_ofNat64_small (by omega)]
      omega
    rw [cardsFrom, ite_eq_right_iff.mpr fun h => absurd h hcmp_le]
    dsimp only
    rw [hcard_rd, hdrop]
    by_cases hgt : Sem.cmpBytes (gCard g) X = .gt
    · have hebc : 0 < ebcCmp (jeb (gCard g)) (jeb X) :=
        (ebcCmp_pos_iff (hgcard_len.trans hX.symm)).mpr hgt
      have hvis : vis X (g :: gs.drop c) = [] := by
        simp [vis, hgt]
      rw [ite_eq_left_iff.mpr fun h => absurd hebc h, hvis]
      simp
    · have hebc : ¬ (0 < ebcCmp (jeb (gCard g)) (jeb X)) :=
        mt (ebcCmp_pos_iff (hgcard_len.trans hX.symm)).mp hgt
      have hvis : vis X (g :: gs.drop c) = g :: vis X (gs.drop c) := by
        have hne_gt : (Sem.cmpBytes (gCard g) X != .gt) = true := bne_iff_ne.mpr hgt
        simp [vis, hne_gt]
      rw [ite_eq_right_iff.mpr fun h => absurd h hebc, hvis,
        ofNat64_add_one (by omega)]
      by_cases heq : gCard g = X
      · have hjeb : jeb X = jeb (gCard g) := by rw [heq]
        have hcnt := htrct.2 c hc1 hcle
        rw [hget] at hcnt
        have hcnt_nat : (BitVec.ofNat 64 g.length).toInt.toNat = g.length := by
          rw [toInt_ofNat64_small (by omega)]
          omega
        rw [ite_eq_left_iff.mpr fun h => absurd hjeb h, hcnt]
        dsimp only
        rw [hcnt_nat, transOf_group m (BitVec.ofNat 64 c) g hg_ok hent_rd o tot htot]
        have htot' : (g.foldl addAmt tot).natAbs < 100000000000 :=
          foldl_addAmt_lt tot htot g
        rw [cardsFrom_vis m trct gs hG hgs htab htrct X hX n (c + 1) (by omega) (by omega) _ _ htot']
        simp [matchStmt, matchHtml, accStep, heq, List.append_assoc]
      · have hjeb : jeb X ≠ jeb (gCard g) := fun h => heq (jeb_inj.mp h).symm
        rw [ite_eq_right_iff.mpr fun h => absurd h hjeb,
          cardsFrom_vis m trct gs hG hgs htab htrct X hX n (c + 1) (by omega) (by omega) o tot htot]
        simp [matchStmt, matchHtml, accStep, heq]

/-! ## 7. Connecting `trnxStmt` / `trnxHtml` on sorted encoded records to `Model` -/

theorem ofCard_encode {trs : List (List EquivLean.Cobol.Rec.FVal)}
    (htrs : ∀ r ∈ trs, TrnxRecord.Valid r) (card : List UInt8) :
    ofCard card (trs.map TrnxRecord.encode) = (ofCardF card trs).map TrnxRecord.encode := by
  unfold ofCard ofCardF
  induction trs with
  | nil => rfl
  | cons r rs ih =>
    have hr := trnx_fields (htrs r (List.mem_cons_self ..))
    have ih' := ih (fun x hx => htrs x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.filter_cons, hr.1]
    cases (strOf (r.getD 0 default) == card) <;> simp [ih']

theorem foldl_addAmt_encode {ts : List (List EquivLean.Cobol.Rec.FVal)}
    (hts : ∀ r ∈ ts, TrnxRecord.Valid r) :
    ∀ acc : Int, (ts.map TrnxRecord.encode).foldl addAmt acc = ts.foldl modelAddAmt acc := by
  induction ts with
  | nil => intro acc; rfl
  | cons r rs ih =>
    intro acc
    have htr := (tran_of_valid (hts r (List.mem_cons_self ..)) acc).2.2.2
    simp only [List.map_cons, List.foldl_cons, htr]
    exact ih (fun x hx => hts x (List.mem_cons_of_mem _ hx)) (modelAddAmt acc r)

theorem map_tranStmtR_encode {ts : List (List EquivLean.Cobol.Rec.FVal)}
    (hts : ∀ r ∈ ts, TrnxRecord.Valid r) :
    ((ts.map TrnxRecord.encode).map tranStmtR).map jeb = (ts.map modelTranStmt).map jline := by
  induction ts with
  | nil => rfl
  | cons r rs ih =>
    have htr := (tran_of_valid (hts r (List.mem_cons_self ..)) 0).1
    simp only [List.map_cons, htr, modelTranStmt, jeb, ih (fun x hx => hts x (List.mem_cons_of_mem _ hx))]

theorem flatMap_tranHtmlR_encode {ts : List (List EquivLean.Cobol.Rec.FVal)}
    (hts : ∀ r ∈ ts, TrnxRecord.Valid r) :
    ((ts.map TrnxRecord.encode).flatMap tranHtmlR).map jeb =
      (ts.flatMap modelTranHtml).map jline := by
  induction ts with
  | nil => rfl
  | cons r rs ih =>
    have htr := (tran_of_valid (hts r (List.mem_cons_self ..)) 0).2.1
    simp only [List.map_cons, List.flatMap_cons, List.map_append, htr, modelTranHtml,
      map_jline_cp037Code, ih (fun x hx => hts x (List.mem_cons_of_mem _ hx))]

theorem ofCardF_valid {trs : List (List EquivLean.Cobol.Rec.FVal)}
    (htrs : ∀ r ∈ trs, TrnxRecord.Valid r) (card : List UInt8) :
    ∀ r ∈ ofCardF card trs, TrnxRecord.Valid r := by
  intro r hr
  unfold ofCardF at hr
  exact htrs r (List.mem_filter.mp hr).1

theorem tailOf_cardsFrom_sorted {vals1 : List (List EquivLean.Cobol.Rec.FVal)}
    (hv1 : ∀ v ∈ vals1, TrnxRecord.Valid v)
    (hs : CardsSorted (vals1.map TrnxRecord.encode))
    (hG : (grp (vals1.map TrnxRecord.encode)).length ≤ 50)
    (hT : ∀ g ∈ grp (vals1.map TrnxRecord.encode), g.length ≤ 10)
    {ld : LdSt}
    (hcr : ld.cr = BitVec.ofNat 64 (grp (vals1.map TrnxRecord.encode)).length)
    (htab : JTableOk ld.m (grp (vals1.map TrnxRecord.encode)))
    (htrct : JTrctOk ld.trct (grp (vals1.map TrnxRecord.encode))
      (grp (vals1.map TrnxRecord.encode)).length)
    {card : List UInt8} (hcard : card.length = 16) (o : JOut) :
    let (o', total) := cardsFrom ld.m ld.trct ld.cr (jeb card) ld.cr.toInt.toNat 1 (o, 0)
    tailOf o' total =
      ⟨o.disp,
       o.stmt ++ ((ofCardF card vals1).map modelTranStmt ++
         modelTailStmt ((ofCardF card vals1).foldl modelAddAmt 0)).map jline,
       o.html ++ ((ofCardF card vals1).flatMap modelTranHtml ++ modelTailHtml).map jline,
       o.ab⟩ := by
  set trs := vals1.map TrnxRecord.encode
  set gs := grp trs
  obtain ⟨hflat, hne_gs, _⟩ := grp_props trs
  have hgs_ok : ∀ g ∈ gs, g ≠ [] ∧ g.length ≤ 10 ∧ ∀ r ∈ g, EncTrnxOk r := by
    intro g hg
    refine ⟨hne_gs g hg, hT g hg, fun r hr => ?_⟩
    have hmem : r ∈ trs := by rw [← hflat]; exact List.mem_flatten.mpr ⟨g, hg, hr⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hmem
    exact encTrnxOk_of_valid (hv1 v hv)
  have hcr_nat : ld.cr.toInt.toNat = gs.length := by
    rw [hcr, toInt_ofNat64_small (by omega)]
    omega
  have h1 : (1 : I64) = BitVec.ofNat 64 1 := rfl
  have h0 : (0 : I64) = BitVec.ofInt 64 0 := rfl
  have hcf := cardsFrom_vis ld.m ld.trct gs hG hgs_ok htab htrct card hcard
    gs.length 1 (by decide) (by omega) o 0 (by decide)
  dsimp only at hcf ⊢
  rw [hcr_nat, h1, h0, hcr, hcf]
  simp only [Nat.sub_self, List.drop_zero]
  rw [tailOf_eq]
  dsimp only
  have htot_int : (BitVec.ofInt 64 ((vis card gs).foldl (accStep card) 0)).toInt =
      (vis card gs).foldl (accStep card) 0 :=
    toInt_ofInt64_small (by have := foldl_accStep_lt card (vis card gs) 0 (by decide); omega)
  rw [htot_int]
  have hts_eq : (vis card gs).flatMap (matchStmt card) ++
      tailStmt ((vis card gs).foldl (accStep card) 0) = trnxStmt card gs := rfl
  have hth_eq : (vis card gs).flatMap (matchHtml card) ++ tailHtml = trnxHtml card gs := rfl
  have hof := ofCard_encode hv1 card
  have hts_v := ofCardF_valid hv1 card
  rw [List.append_assoc o.stmt, ← List.map_append, hts_eq, trnxStmt_sorted trs hs card, hof,
      List.map_append, map_tranStmtR_encode hts_v, foldl_addAmt_encode hts_v,
      List.append_assoc o.html, ← List.map_append, hth_eq, trnxHtml_sorted trs hs card, hof,
      List.map_append, flatMap_tranHtmlR_encode hts_v]
  unfold modelTailStmt modelTailHtml
  rw [List.map_append, List.map_append, map_jline_cp037Code, map_jline_cp037Code]

/-! ## 8. `custFind`, `acctFind`, `xrefStep`, `xrefAll`, and `jRunT_eq_model` -/

theorem zip_map_find?_snd {α β : Type} (f : α → β) (P : β → Bool) :
    ∀ l : List α, (((l.map f).zip l).find? (fun p => P p.1)).map (·.2) = l.find? (fun x => P (f x))
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.zip_cons_cons, List.find?_cons]
    cases P (f x) <;> simp [zip_map_find?_snd f P xs]

theorem custFind_eq {vals3 : List (List EquivLean.Cobol.Rec.FVal)}
    (hv3 : ∀ c ∈ vals3, CustomerRecord.Valid c)
    {cid : Int} (hcid : ({ digits := 9 } : NumFmt).Holds {} cid) :
    let custTexts := (vals3.map CustomerRecord.encode).map jeb
    custFind (custTexts.map (sub · 0 9)) custTexts (jeb (Sem.digitChars {} 9 cid.natAbs)) =
      (vals3.find? (fun c => numOf (c.getD 0 default) == cid)).map
        (fun c => jeb (CustomerRecord.encode c)) := by
  dsimp only
  unfold custFind
  rw [zip_map_find?_snd (sub · 0 9) (fun x => decide (x = jeb (Sem.digitChars {} 9 cid.natAbs))),
    List.map_map, List.find?_map]
  congr 1
  apply EquivLean.Modernize.GlueKit.find?_congr
  intro c hc
  have hkey := cust_key_beq (hv3 c hc) hcid
  simp only [Sem.keyOf, List.drop_zero] at hkey
  rw [← hkey, Bool.eq_iff_iff]
  simp [Function.comp_apply, sub_jeb, jeb_inj]

theorem acctFind_eq {vals4 : List (List EquivLean.Cobol.Rec.FVal)}
    (hv4 : ∀ a ∈ vals4, AccountRecord.Valid a)
    {aid : Int} (haid : ({ digits := 11 } : NumFmt).Holds {} aid) :
    let acctTexts := (vals4.map AccountRecord.encode).map jeb
    acctFind acctTexts (jeb (Sem.digitChars {} 11 aid.natAbs)) =
      (vals4.find? (fun a => numOf (a.getD 0 default) == aid)).map
        (fun a => jeb (AccountRecord.encode a)) := by
  dsimp only
  unfold acctFind
  rw [List.map_map, List.find?_map]
  congr 1
  apply EquivLean.Modernize.GlueKit.find?_congr
  intro a ha
  have hkey := acct_key_beq (hv4 a ha) haid
  simp only [Sem.keyOf, List.drop_zero] at hkey
  rw [← hkey, Bool.eq_iff_iff]
  simp [Function.comp_apply, sub_jeb, jeb_inj]

theorem sub_fixStr_jeb {bs : List UInt8} {a b : Nat}
    (hb : b ≤ bs.length) (h1000 : bs.length ≤ 1000) :
    sub (fixStr (jeb bs) 1000) a b = jeb ((bs.drop a).take (b - a)) := by
  unfold sub
  rw [fixStr_eq_append (by simp [h1000]),
    List.take_append_of_le_length (by simp [hb]),
    jeb_take, jeb_drop, List.drop_take]

theorem xref_sub_fields {x : List EquivLean.Cobol.Rec.FVal} (hx : CardXrefRecord.Valid x) :
    let X := CardXrefRecord.encode x
    let fldt := fixStr (jeb X) 1000
    sub fldt 0 16 = jeb (strOf (x.getD 0 default)) ∧
    (strOf (x.getD 0 default)).length = 16 ∧
    sub fldt 16 25 = jeb (Sem.digitChars {} 9 (numOf (x.getD 1 default)).natAbs) ∧
    ({ digits := 9 } : NumFmt).Holds {} (numOf (x.getD 1 default)) ∧
    sub fldt 25 36 = jeb (Sem.digitChars {} 11 (numOf (x.getD 2 default)).natAbs) ∧
    ({ digits := 11 } : NumFmt).Holds {} (numOf (x.getD 2 default)) := by
  dsimp only
  have hlen : (CardXrefRecord.encode x).length = 50 := xref_length hx
  obtain ⟨h0, h0l, -⟩ := xref_fields hx
  have h1 := field_num_decode cardXrefRecord_contig hx 1 16 9 { digits := 9 } (by decide) rfl rfl rfl
  have h2 := field_num_decode cardXrefRecord_contig hx 2 25 11 { digits := 11 } (by decide) rfl rfl rfl
  refine ⟨?_, h0l, ?_, h1.2.2, ?_, h2.2.2⟩
  · rw [sub_fixStr_jeb (by omega) (by omega), List.drop_zero, show 16 - 0 = 16 from rfl]
    exact congrArg jeb h0
  · rw [sub_fixStr_jeb (by omega) (by omega), show 25 - 16 = 9 from rfl,
      h1.1, StmBridge.encodeNum_unsigned_display (by decide)]
  · rw [sub_fixStr_jeb (by omega) (by omega), show 36 - 25 = 11 from rfl,
      h2.1, StmBridge.encodeNum_unsigned_display (by decide)]

set_option maxRecDepth 100000 in
theorem abend_cust_disp :
    [jl "ERROR READING CUSTFILE", jl "RETURN CODE: " ++ jl "23", jl "ABENDING PROGRAM"] =
      modelCustAbortDisp.map jline := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem abend_acct_disp :
    [jl "ERROR READING ACCTFILE", jl "RETURN CODE: " ++ jl "23", jl "ABENDING PROGRAM"] =
      modelAcctAbortDisp.map jline := by
  decide +kernel

theorem find?_mem {α : Type} {p : α → Bool} {l : List α} {x : α} (h : l.find? p = some x) :
    x ∈ l :=
  List.mem_of_find?_eq_some h

theorem xrefAll_eq_loop {vals1 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal)}
    (hv1 : ∀ v ∈ vals1, TrnxRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, CustomerRecord.Valid v)
    (hv4 : ∀ v ∈ vals4, AccountRecord.Valid v)
    (hs : CardsSorted (vals1.map TrnxRecord.encode))
    (hG : (grp (vals1.map TrnxRecord.encode)).length ≤ 50)
    (hT : ∀ g ∈ grp (vals1.map TrnxRecord.encode), g.length ≤ 10)
    {ld : LdSt}
    (hcr : ld.cr = BitVec.ofNat 64 (grp (vals1.map TrnxRecord.encode)).length)
    (htab : JTableOk ld.m (grp (vals1.map TrnxRecord.encode)))
    (htrct : JTrctOk ld.trct (grp (vals1.map TrnxRecord.encode))
      (grp (vals1.map TrnxRecord.encode)).length) :
    ∀ (xs : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ x ∈ xs, CardXrefRecord.Valid x) →
      ∀ (stmts htmls : List (List Nat)),
        let custTexts := (vals3.map CustomerRecord.encode).map jeb
        let acctTexts := (vals4.map AccountRecord.encode).map jeb
        let jo := xrefAll (custTexts.map (sub · 0 9)) custTexts acctTexts ld
          ⟨[], stmts.map jline, htmls.map jline, false⟩
          ((xs.map CardXrefRecord.encode).map jeb)
        let mo := Model.loop vals1 vals3 vals4 xs stmts htmls
        jo.disp = mo.disp.map jline ∧
        jo.stmt = mo.stmtWrites.map jline ∧
        jo.html = mo.htmlWrites.map jline ∧
        jo.ab = mo.abended
  | [], _, stmts, htmls => by
    simp [xrefAll, Model.loop]
  | x :: xs, hxs, stmts, htmls => by
    dsimp only
    have hx : CardXrefRecord.Valid x := hxs x (List.mem_cons_self ..)
    have hxs' : ∀ y ∈ xs, CardXrefRecord.Valid y := fun y hy => hxs y (List.mem_cons_of_mem _ hy)
    obtain ⟨hcard, hcard_len, hcid_sub, hcid_holds, haid_sub, haid_holds⟩ := xref_sub_fields hx
    rw [List.map_cons, List.map_cons, xrefAll, Model.loop]
    unfold xrefStep
    dsimp only
    rw [hcard, hcid_sub, haid_sub, custFind_eq hv3 hcid_holds, acctFind_eq hv4 haid_holds]
    cases hfc : vals3.find? (fun c => numOf (c.getD 0 default) == numOf (x.getD 1 default)) with
    | none =>
      simp only [Option.map_none, JOut.abend, List.nil_append, abend_cust_disp, and_self]
    | some c =>
      have hc : CustomerRecord.Valid c := hv3 c (find?_mem hfc)
      cases hfa : vals4.find? (fun a => numOf (a.getD 0 default) == numOf (x.getD 2 default)) with
      | none =>
        simp only [Option.map_some, Option.map_none, JOut.abend, List.nil_append, abend_acct_disp, and_self]
      | some a =>
        have ha : AccountRecord.Valid a := hv4 a (find?_mem hfa)
        simp only [Option.map_some]
        have hcs := jCreateStatement_eq hc ha
        have htc := tailOf_cardsFrom_sorted hv1 hs hG hT hcr htab htrct hcard_len
          (JOut.add ⟨[], stmts.map jline, htmls.map jline, false⟩
            (jCreateStatement (jeb (CustomerRecord.encode c)) (jeb (AccountRecord.encode a))))
        dsimp only at htc
        rw [htc, hcs]
        dsimp only [JOut.add]
        have hst_eq : stmts.map jline ++ (modelHeadStmt c a).map jline ++
            ((ofCardF (strOf (x.getD 0 default)) vals1).map modelTranStmt ++
              modelTailStmt ((ofCardF (strOf (x.getD 0 default)) vals1).foldl modelAddAmt 0)).map jline =
            (stmts ++ modelStmtOf vals1 (strOf (x.getD 0 default)) c a).map jline := by
          unfold modelStmtOf
          simp [List.map_append, List.append_assoc]
        have hht_eq : htmls.map jline ++ (modelHeadHtml c a).map jline ++
            ((ofCardF (strOf (x.getD 0 default)) vals1).flatMap modelTranHtml ++ modelTailHtml).map jline =
            (htmls ++ modelHtmlOf vals1 (strOf (x.getD 0 default)) c a).map jline := by
          unfold modelHtmlOf
          simp [List.map_append, List.append_assoc]
        rw [hst_eq, hht_eq]
        exact xrefAll_eq_loop hv1 hv3 hv4 hs hG hT hcr htab htrct xs hxs'
          (stmts ++ modelStmtOf vals1 (strOf (x.getD 0 default)) c a)
          (htmls ++ modelHtmlOf vals1 (strOf (x.getD 0 default)) c a)

/-- **`jRunT` on the CP037 texts of valid records in `Domain` equals `Model.run`.** -/
theorem jRunT_eq_model (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal))
    (hv1 : ∀ v ∈ vals1, TrnxRecord.Valid v)
    (hv2 : ∀ v ∈ vals2, CardXrefRecord.Valid v)
    (hv3 : ∀ v ∈ vals3, CustomerRecord.Valid v)
    (hv4 : ∀ v ∈ vals4, AccountRecord.Valid v)
    (hD : EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4) :
    let jt := jRunT
      ((vals1.map TrnxRecord.encode).map (fun r => jline (r.map cp037Code)))
      ((vals2.map CardXrefRecord.encode).map (fun r => jline (r.map cp037Code)))
      ((vals3.map CustomerRecord.encode).map (fun r => jline (r.map cp037Code)))
      ((vals4.map AccountRecord.encode).map (fun r => jline (r.map cp037Code)))
    let mr := Model.run vals1 vals2 vals3 vals4
    jt.disp = mr.disp.map jline ∧
    jt.stmt = mr.stmtWrites.map jline ∧
    jt.html = mr.htmlWrites.map jline ∧
    jt.ab = mr.abended := by
  dsimp only
  obtain ⟨hne1, hs, hG, hT, -⟩ := hD
  obtain ⟨v0, vs, rfl⟩ := List.exists_cons_of_ne_nil hne1
  have htl : ∀ r ∈ TrnxRecord.encode v0 :: vs.map TrnxRecord.encode, r.length = 350 := by
    intro r hr
    rw [← List.map_cons] at hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    exact trnx_length (hv1 v hv)
  have hgeb : (fun r : List UInt8 => jline (r.map cp037Code)) = jeb := rfl
  rw [hgeb]
  obtain ⟨_, hcr, htab, htrct⟩ := ldFin_ldAll_ok htl hG hT
  simp only [List.map_cons, jRunT]
  exact xrefAll_eq_loop hv1 hv3 hv4 hs hG hT hcr htab htrct vals2 hv2 [] []

#print axioms jRunT_eq_model

end EquivLean.Modernize.Cbstm03a.Java
