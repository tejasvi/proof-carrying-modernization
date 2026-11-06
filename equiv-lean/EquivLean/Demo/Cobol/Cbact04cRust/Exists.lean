import EquivLean.Demo.Cobol.Cbact04cRust.Sim

/-!
# The hypotheses of the COBOL → Rust theorem are satisfiable

For every input of coblean's `cbact04c_all` (accounts with distinct keys, each with its category
records, rates within `S9(4)V99` that agree on equal disclosure-group keys) there are Rust slices
holding its records (one `Cat` per category record, in file order; one `Account` per account; one
`Disc` per category record) and record functions `acctOf`, `rateOf` with the hypotheses `hcats`,
`Lookups`, `hracct`, `hrrate` of `cbact04c_rust_equiv` (`rust_inputs_exist`).  Hence the
equivalence is not vacuous (`cbact04c_rust_equiv_exists`), as `cbact04c_sim_exists` for Java.

The keys: the group id and the type code become integers by `beNat`, which is injective on lists
of one length (`beNat_inj`); the `i64`, `i32`, `u16`, `u128` fields are exact within the PIC
bounds (`mkI64_val`, …).
-/

open Aeneas Aeneas.Std Result
open Cobol CardDemo.Cbact04c

namespace EquivLean.Demo.Cbact04cRust

/-! ## Big-endian values of byte lists -/

theorem beNat_foldl : ∀ (bs : List UInt8) (acc : Nat),
    bs.foldl (fun acc b => acc * 256 + b.toNat) acc = acc * 256 ^ bs.length + beNat bs
  | [], acc => by simp [beNat]
  | b :: bs, acc => by
    have h1 := beNat_foldl bs (acc * 256 + b.toNat)
    have h2 := beNat_foldl bs b.toNat
    simp only [beNat, List.foldl_cons, Nat.zero_mul, Nat.zero_add] at h1 h2 ⊢
    rw [h1, h2, List.length_cons, Nat.pow_succ]
    ring

theorem beNat_cons (b : UInt8) (bs : List UInt8) :
    beNat (b :: bs) = b.toNat * 256 ^ bs.length + beNat bs := by
  have h := beNat_foldl bs b.toNat
  simp only [beNat, List.foldl_cons, Nat.zero_mul, Nat.zero_add] at h ⊢
  exact h

theorem beNat_lt : ∀ bs : List UInt8, beNat bs < 256 ^ bs.length
  | [] => by simp [beNat]
  | b :: bs => by
    rw [beNat_cons, List.length_cons, Nat.pow_succ]
    have h1 := beNat_lt bs
    have h2 : b.toNat * 256 ^ bs.length ≤ 255 * 256 ^ bs.length :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt_succ b.toNat_lt)
    omega

theorem div_mod_decomp {x r P : Nat} (hr : r < P) : (x * P + r) / P = x ∧ (x * P + r) % P = r := by
  have hP : 0 < P := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- `beNat` is injective on lists of one length. -/
theorem beNat_inj : ∀ {xs ys : List UInt8}, xs.length = ys.length → beNat xs = beNat ys → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [beNat_cons, beNat_cons, hl] at h
    have hx := beNat_lt xs
    have hy := beNat_lt ys
    rw [hl] at hx
    have e1 := (div_mod_decomp (x := x.toNat) hx).1
    have e2 := (div_mod_decomp (x := x.toNat) hx).2
    rw [h, (div_mod_decomp (x := y.toNat) hy).1] at e1
    rw [h, (div_mod_decomp (x := y.toNat) hy).2] at e2
    rw [UInt8.toNat_inj.mp e1.symm, beNat_inj hl e2.symm]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-! ## Rust scalars of integers -/

/-- The `i64` with value `x` (two's complement; exact for `x` in range, `mkI64_val`). -/
def mkI64 (x : Int) : Std.I64 := ⟨BitVec.ofInt 64 x⟩
def mkI32 (x : Int) : Std.I32 := ⟨BitVec.ofInt 32 x⟩
def mkU16 (n : Nat) : Std.U16 := ⟨BitVec.ofNat 16 n⟩
def mkU128 (n : Nat) : Std.U128 := ⟨BitVec.ofNat 128 n⟩

theorem mkI64_val {x : Int} (h : x.natAbs < 2 ^ 63) : (mkI64 x).val = x := by
  show (BitVec.ofInt 64 x).toInt = x
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem mkI32_val {x : Int} (h : x.natAbs < 2 ^ 31) : (mkI32 x).val = x := by
  show (BitVec.ofInt 32 x).toInt = x
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem mkU16_val {n : Nat} (h : n < 2 ^ 16) : (mkU16 n).val = n := by
  show (BitVec.ofNat 16 n).toNat = n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem mkU128_val {n : Nat} (h : n < 2 ^ 128) : (mkU128 n).val = n := by
  show (BitVec.ofNat 128 n).toNat = n
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem beNat_ty_lt {bs : List UInt8} (h : bs.length = 2) : beNat bs < 2 ^ 16 := by
  have := beNat_lt bs
  rw [h] at this
  exact Nat.lt_of_lt_of_le this (by decide)

theorem beNat_grp_lt {bs : List UInt8} (h : bs.length = 10) : beNat bs < 2 ^ 128 := by
  have := beNat_lt bs
  rw [h] at this
  exact Nat.lt_of_lt_of_le this (by decide)

/-! ## The Rust records of the input -/

/-- The Rust `Cat` of the category record `c` of the account `a`. -/
def rustCat (a : Acc) (c : Cat) : cbact04c.Cat :=
  ⟨mkI64 a.id, mkU16 (beNat c.ty), mkI32 c.cat, mkI64 c.bal⟩

/-- The Rust `Account` of the account `a`. -/
def rustAcct (a : Acc) : cbact04c.Account :=
  ⟨mkI64 a.id, mkI64 a.bal, mkI64 a.cc, mkI64 a.cd, mkU128 (beNat a.grp)⟩

/-- The Rust `Disc` of the disclosure group of the category record `c` of the account `a`. -/
def rustDisc (rate : Acc → Cat → Int) (a : Acc) (c : Cat) : cbact04c.Disc :=
  ⟨mkU128 (beNat a.grp), mkU16 (beNat c.ty), mkI32 c.cat, mkI64 (rate a c)⟩

theorem rustCat_ofRust {a : Acc} {c : Cat} (ha : a.valid) (hc : c.valid) :
    RCat.ofRust (rustCat a c) = rcat a c := by
  obtain ⟨hid, -, -, -, -, -, -, -, -, -, -, -, -⟩ := ha
  obtain ⟨hty, -, hcat, -, hbal⟩ := hc
  simp only [RCat.ofRust, rustCat, rcat, mkI64_val (show a.id.natAbs < 2 ^ 63 by omega),
    mkU16_val (beNat_ty_lt hty), mkI32_val (show c.cat.natAbs < 2 ^ 31 by omega),
    mkI64_val (show c.bal.natAbs < 2 ^ 63 by omega)]

theorem rustAcct_ofRust {a : Acc} (ha : a.valid) : RAcct.ofRust (rustAcct a) = racct a := by
  obtain ⟨hid, -, -, hbal, -, hcc, hcd, -, hgrp, -, -, -, -⟩ := ha
  simp only [RAcct.ofRust, rustAcct, racct, mkI64_val (show a.id.natAbs < 2 ^ 63 by omega),
    mkI64_val (show a.bal.natAbs < 2 ^ 63 by omega), mkI64_val (show a.cc.natAbs < 2 ^ 63 by omega),
    mkI64_val (show a.cd.natAbs < 2 ^ 63 by omega), mkU128_val (beNat_grp_lt hgrp)]

/-! ## Lists of accounts -/

theorem eq_of_pairwise_id {l : List Acc} (hd : l.Pairwise (fun a b => a.id ≠ b.id)) :
    ∀ {a b : Acc}, a ∈ l → b ∈ l → a.id = b.id → a = b := by
  induction l with
  | nil => intro a b ha; simp at ha
  | cons x xs ih =>
    intro a b ha hb hab
    rw [List.pairwise_cons] at hd
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · exact absurd hab (hd.1 b hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd hab.symm (hd.1 a ha')
      · exact ih hd.2 ha' hb' hab

theorem mem_items {accs : List Acc} {p : Acc × Cat} :
    p ∈ items accs ↔ p.1 ∈ accs ∧ p.2 ∈ p.1.cats := by
  obtain ⟨a, c⟩ := p
  simp only [items, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha', c', hc', rfl, rfl⟩; exact ⟨ha', hc'⟩
  · rintro ⟨ha, hc⟩; exact ⟨a, ha, c, hc, rfl, rfl⟩

theorem length_le_items : ∀ (accs : List Acc), (∀ a ∈ accs, a.cats ≠ []) →
    accs.length ≤ (items accs).length
  | [], _ => by simp [items]
  | a :: rest, h => by
    have h1 := length_le_items rest (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have h2 : a.cats ≠ [] := h a (List.mem_cons_self ..)
    have h3 : 1 ≤ a.cats.length := by
      cases hc : a.cats with
      | nil => exact absurd hc h2
      | cons _ _ => simp
    simp only [items, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons] at h1 ⊢
    omega

/-! ## The record functions -/

/-- The account record with this key (the values of the first account with the key). -/
def acctOfL (accs : List Acc) (id : Int) : RAcct :=
  match accs.find? (fun a => decide (a.id = id)) with
  | some a => racct a
  | none => default

/-- The rate of the disclosure group with this key (that of the first category record with the
key). -/
def rateOfL (accs : List Acc) (rate : Acc → Cat → Int) (g t : Nat) (k : Int) : Int :=
  match (items accs).find? (fun p => decide (beNat p.1.grp = g ∧ beNat p.2.ty = t ∧ p.2.cat = k)) with
  | some p => rate p.1 p.2
  | none => 0

theorem acctOfL_eq {accs : List Acc} (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) {a : Acc}
    (ha : a ∈ accs) : acctOfL accs a.id = racct a := by
  have hs : (accs.find? (fun b => decide (b.id = a.id))).isSome :=
    List.find?_isSome.2 ⟨a, ha, by simp⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hs
  have hbid : b.id = a.id := by simpa using List.find?_some hb
  have hba := eq_of_pairwise_id hdist (List.mem_of_find?_eq_some hb) ha hbid
  simp only [acctOfL, hb, hba]

theorem rateOfL_eq {accs : List Acc} (hval : ∀ a ∈ accs, a.valid) {rate : Acc → Cat → Int}
    (hkey : ∀ a ∈ accs, ∀ c ∈ a.cats, ∀ a' ∈ accs, ∀ c' ∈ a'.cats,
      a.grp = a'.grp → c.ty = c'.ty → c.cat = c'.cat → rate a c = rate a' c')
    {a : Acc} {c : Cat} (ha : a ∈ accs) (hc : c ∈ a.cats) :
    rateOfL accs rate (beNat a.grp) (beNat c.ty) c.cat = rate a c := by
  have hs : ((items accs).find? (fun p =>
      decide (beNat p.1.grp = beNat a.grp ∧ beNat p.2.ty = beNat c.ty ∧ p.2.cat = c.cat))).isSome :=
    List.find?_isSome.2 ⟨(a, c), mem_items.2 ⟨ha, hc⟩, by simp⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hs
  have hpk := List.find?_some hp
  simp only [decide_eq_true_eq] at hpk
  obtain ⟨hp1, hp2⟩ := mem_items.1 (List.mem_of_find?_eq_some hp)
  obtain ⟨-, -, -, -, -, -, -, -, hg1, -, -, -, hcs1⟩ := hval p.1 hp1
  obtain ⟨-, -, -, -, -, -, -, -, hga, -, -, -, hcsa⟩ := hval a ha
  have hg : p.1.grp = a.grp := beNat_inj (by rw [hg1, hga]) hpk.1
  have ht : p.2.ty = c.ty := beNat_inj (by rw [(hcs1 p.2 hp2).1, (hcsa c hc).1]) hpk.2.1
  simp only [rateOfL, hp]
  exact hkey p.1 hp1 p.2 hp2 a ha c hc hg ht hpk.2.2

/-- The rates of `cbact04c_all`'s `hdisc` depend only on the disclosure key (as
`EquivLean.Demo.Cbact04c.rate_of_key`, `Demo/Jimple/Cbact04c/KeyRate.lean`, restated here so that
the Rust proof does not import the Java side): equal keys give the same record, hence the same
rate. -/
theorem rate_of_key (accs : List Acc) (discs : List (List UInt8)) (rate : Acc → Cat → Int)
    (di : Acc → Cat → Nat) (dfill : Acc → Cat → List UInt8)
    (hdisc : ∀ a ∈ accs, ∀ c ∈ a.cats, Sem.findKey { off := 0, len := 16 }
        (a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat) discs = some (di a c) ∧
      discs.getD (di a c) [] = a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat ++
        encodeNum {} DIS_INT_RATE.fmt (rate a c) ++ dfill a c ∧
      (dfill a c).length = 28 ∧ (rate a c).natAbs < 1000000) :
    ∀ a ∈ accs, ∀ c ∈ a.cats, ∀ a' ∈ accs, ∀ c' ∈ a'.cats,
      a.grp = a'.grp → c.ty = c'.ty → c.cat = c'.cat → rate a c = rate a' c' := by
  intro a ha c hc a' ha' c' hc' hg ht hk
  obtain ⟨h1, h2, h3, h4⟩ := hdisc a ha c hc
  obtain ⟨h1', h2', h3', h4'⟩ := hdisc a' ha' c' hc'
  rw [hg, ht, hk] at h1 h2
  have hi : di a c = di a' c' := Option.some.inj (h1.symm.trans h1')
  rw [hi, h2'] at h2
  have hl : ∀ r, (encodeNum {} DIS_INT_RATE.fmt r).length = 6 := fun r =>
    length_encodeNum _ _ _ (by decide)
  simp only [List.append_assoc, List.append_cancel_left_eq] at h2
  have he : encodeNum {} DIS_INT_RATE.fmt (rate a' c') = encodeNum {} DIS_INT_RATE.fmt (rate a c) :=
    List.append_inj_left h2 (by rw [hl, hl])
  have d1 := decodeNum_encodeNum {} DIS_INT_RATE.fmt (rate a c) (by decide) (by decide)
    ⟨h4, fun h => by simp at h⟩
  have d2 := decodeNum_encodeNum {} DIS_INT_RATE.fmt (rate a' c') (by decide) (by decide)
    ⟨h4', fun h => by simp at h⟩
  rw [he, d1] at d2
  exact Option.some.inj d2

/-! ## The inputs exist -/

theorem usize_ge : 999999 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max_eq, U64.max_eq]

/-- **The Rust inputs exist**: for every input of `cbact04c_all` there are Rust slices holding
its records (one `Cat` per category record in file order, one `Account` per account, one `Disc`
per category record) and record functions with the hypotheses of `cbact04c_rust_equiv`. -/
theorem rust_inputs_exist (accs : List Acc) (hval : ∀ a ∈ accs, a.valid)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) (hlen : (items accs).length < 999999)
    (rate : Acc → Cat → Int) (hrate : ∀ a ∈ accs, ∀ c ∈ a.cats, (rate a c).natAbs < 1000000)
    (hkey : ∀ a ∈ accs, ∀ c ∈ a.cats, ∀ a' ∈ accs, ∀ c' ∈ a'.cats,
      a.grp = a'.grp → c.ty = c'.ty → c.cat = c'.cat → rate a c = rate a' c') :
    ∃ (cats : Slice cbact04c.Cat) (accounts : Slice cbact04c.Account)
      (rdiscs : Slice cbact04c.Disc) (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int),
      cats.val.map RCat.ofRust = rcats accs ∧ Lookups cats accounts rdiscs acctOf rateOf ∧
      (∀ a ∈ accs, acctOf a.id = racct a) ∧
      (∀ a ∈ accs, ∀ c ∈ a.cats, rateOf (beNat a.grp) (beNat c.ty) c.cat = rate a c) := by
  have hU := usize_ge
  have hm : accs.length ≤ (items accs).length :=
    length_le_items accs (fun a ha => (hval a ha).2.2.2.2.2.2.2.2.2.2.2.1)
  refine ⟨Slice.from ((items accs).map fun p => rustCat p.1 p.2) (by simp only [List.length_map]; omega),
    Slice.from (accs.map rustAcct) (by simp only [List.length_map]; omega),
    Slice.from ((items accs).map fun p => rustDisc rate p.1 p.2) (by simp only [List.length_map]; omega),
    acctOfL accs, rateOfL accs rate, ?_, ?_, fun a ha => acctOfL_eq hdist ha,
    fun a ha c hc => rateOfL_eq hval hkey ha hc⟩
  · -- the category records, in file order
    rw [Slice.from_val, List.map_map, rcats]
    apply List.map_congr_left
    intro p hp
    obtain ⟨ha, hc⟩ := mem_items.1 hp
    exact rustCat_ofRust (hval _ ha) ((hval _ ha).2.2.2.2.2.2.2.2.2.2.2.2 _ hc)
  · -- every lookup finds the account and the rate of the record
    intro c hc
    rw [Slice.from_val, List.mem_map] at hc
    obtain ⟨⟨a, cat⟩, hp, rfl⟩ := hc
    obtain ⟨ha, hcat⟩ := mem_items.1 hp
    have hav := hval a ha
    obtain ⟨hid, -, -, -, -, -, -, -, hgrp, -, -, -, hcs⟩ := hav
    obtain ⟨hty, -, hk, -, -⟩ := hcs cat hcat
    have eid : (mkI64 a.id).val = a.id := mkI64_val (by omega)
    have eacct : acctOfL accs (mkI64 a.id).val = racct a := by rw [eid]; exact acctOfL_eq hdist ha
    refine ⟨⟨rustAcct a, by rw [Slice.from_val]; exact List.mem_map_of_mem ha, rfl⟩, ?_,
      ⟨rustDisc rate a cat, by rw [Slice.from_val]; exact List.mem_map_of_mem (f := fun p => rustDisc rate p.1 p.2) hp, ?_, rfl, rfl⟩, ?_⟩
    · -- every account with the key is `a`
      intro acc hacc hacc_id
      rw [Slice.from_val, List.mem_map] at hacc
      obtain ⟨a', ha', rfl⟩ := hacc
      have hv' := hval a' ha'
      have hid' : a'.id = a.id := by
        have := congrArg IScalar.val hacc_id
        simp only [rustAcct, rustCat] at this
        rwa [mkI64_val (by have := hv'.1; omega), eid] at this
      rw [eq_of_pairwise_id hdist ha' ha hid', rustAcct_ofRust (hval a ha)]
      simp only [rustCat]
      rw [eacct]
    · -- its group id
      simp only [rustDisc, rustCat]
      rw [eacct, mkU128_val (beNat_grp_lt hgrp)]
      rfl
    · -- every disclosure record with the key has the rate
      intro d hd hdg hdt hdk
      rw [Slice.from_val, List.mem_map] at hd
      obtain ⟨⟨a', cat'⟩, hp', rfl⟩ := hd
      obtain ⟨ha', hcat'⟩ := mem_items.1 hp'
      obtain ⟨-, -, -, -, -, -, -, -, hgrp', -, -, -, hcs'⟩ := hval a' ha'
      obtain ⟨hty', -, hk', -, -⟩ := hcs' cat' hcat'
      simp only [rustDisc, rustCat] at hdg hdt hdk ⊢
      rw [eacct, mkU128_val (beNat_grp_lt hgrp')] at hdg
      have hg : a'.grp = a.grp := beNat_inj (by rw [hgrp', hgrp]) hdg
      have ht : cat'.ty = cat.ty := by
        have := congrArg UScalar.val hdt
        rw [mkU16_val (beNat_ty_lt hty'), mkU16_val (beNat_ty_lt hty)] at this
        exact beNat_inj (by rw [hty', hty]) this
      have hkk : cat'.cat = cat.cat := by
        have := congrArg IScalar.val hdk
        rwa [mkI32_val (by omega), mkI32_val (by omega)] at this
      rw [eacct, mkI64_val (by have := hrate a' ha' cat' hcat'; omega),
        mkU16_val (beNat_ty_lt hty), mkI32_val (by omega)]
      simp only [racct]
      rw [rateOfL_eq hval hkey ha hcat]
      exact hkey a' ha' cat' hcat' a ha cat hcat hg ht hkk

/-- **The COBOL → Rust equivalence is not vacuous**: for every input of coblean's `cbact04c_all`
there are Rust inputs holding the same records (`rust_inputs_exist`; the rates depend only on the
disclosure key, `rate_of_key`), and on them the equivalence `cbact04c_rust_equiv` holds. -/
theorem cbact04c_rust_equiv_exists (m : Mem) (hm : m.size = 1739) (clk : Nat → List UInt8)
    (hclk : ∀ k, ∃ pre mil post, pre.length = 14 ∧ post.length = 5 ∧ mil.natAbs < 100 ∧
      0 ≤ mil ∧ clk k = pre ++ encodeNum {} { digits := 2 } mil ++ post)
    (accs : List Acc) (hval : ∀ a ∈ accs, a.valid)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) (hlen : (items accs).length < 999999)
    (accts xrefs discs : List (List UInt8)) (ai xi : Acc → Nat)
    (hacct : ∀ a ∈ accs, Sem.findKey { off := 0, len := 11 } (encodeNum {} FD_ACCT_ID.fmt a.id)
      accts = some (ai a) ∧ accts.getD (ai a) [] = a.bytes)
    (hxref : ∀ a ∈ accs, Sem.findKey { off := 25, len := 11 }
      (encodeNum {} FD_XREF_ACCT_ID.fmt a.id) xrefs = some (xi a) ∧ xrefs.getD (xi a) [] = a.xrec)
    (rate : Acc → Cat → Int) (di : Acc → Cat → Nat) (dfill : Acc → Cat → List UInt8)
    (hdisc : ∀ a ∈ accs, ∀ c ∈ a.cats, Sem.findKey { off := 0, len := 16 }
        (a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat) discs = some (di a c) ∧
      discs.getD (di a c) [] = a.grp ++ c.ty ++ encodeNum {} DIS_TRAN_CAT_CD.fmt c.cat ++
        encodeNum {} DIS_INT_RATE.fmt (rate a c) ++ dfill a c ∧
      (dfill a c).length = 28 ∧ (rate a c).natAbs < 1000000)
    (n : Nat) (hn : (items accs).length < n) :
    ∃ (cats : Slice cbact04c.Cat) (accounts : Slice cbact04c.Account)
      (rdiscs : Slice cbact04c.Disc) (acctOf : Int → RAcct) (rateOf : Nat → Nat → Int → Int),
      cats.val.map RCat.ofRust = rcats accs ∧ Lookups cats accounts rdiscs acctOf rateOf ∧
      (∀ a ∈ accs, acctOf a.id = racct a) ∧
      (∀ a ∈ accs, ∀ c ∈ a.cats, rateOf (beNat a.grp) (beNat c.ty) c.cat = rate a c) ∧
      EquivLean.Equiv CbRelR (cbact04c.run cats accounts rdiscs)
        (EquivLean.Cobol.run CardDemo.Cbact04c { clock := clk } (n + 60)
          (CardDemo.Cbact04c.initState m [(1, (items accs).map (fun p => Cat.bytes p.1.id p.2)),
            (2, xrefs), (3, accts), (4, discs)])) := by
  obtain ⟨cats, accounts, rdiscs, acctOf, rateOf, hcats, hlook, hracct, hrrate⟩ :=
    rust_inputs_exist accs hval hdist hlen rate (fun a ha c hc => (hdisc a ha c hc).2.2.2)
      (rate_of_key accs discs rate di dfill hdisc)
  exact ⟨cats, accounts, rdiscs, acctOf, rateOf, hcats, hlook, hracct, hrrate,
    cbact04c_rust_equiv m hm clk hclk accs hval hdist hlen accts xrefs discs ai xi hacct hxref rate
      di dfill hdisc n hn cats accounts rdiscs acctOf rateOf hcats hlook hracct hrrate⟩

end EquivLean.Demo.Cbact04cRust

#print axioms EquivLean.Demo.Cbact04cRust.rust_inputs_exist
#print axioms EquivLean.Demo.Cbact04cRust.cbact04c_rust_equiv_exists
