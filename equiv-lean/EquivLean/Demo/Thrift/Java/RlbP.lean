import EquivLean.Demo.Thrift.Java.Rlb
import EquivLean.Demo.Thrift.Java.Ccrl
import EquivLean.Demo.Thrift.Java.Crba

/-!
# Thrift → Java (T4): the compact list header reader `readListBegin()` (D, M)

Under the transport contracts and `NoRedeclL` (no application subclass of `TCompactProtocol`
redeclares the methods `readListBegin()` calls). `readListBegin()` is verified against the
contracts of `readByte()`, `getTType(byte)`, `readVarint32()`, `checkContainerReadLength(int)` and
`checkReadBytesAvailable(TList)` (inherited from `TProtocol`), each proved for its body.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- No application subclass of `TCompactProtocol` redeclares the methods `readListBegin()` calls
(`checkReadBytesAvailable(TList)` is the `TProtocol` method). -/
def NoRedeclL (P : Program) : Prop :=
  NoRedecl P rbSig rbRef ∧ NoRedecl P gttSig gttRef ∧ NoRedecl P ccrlSig ccrlRef ∧
  NoRedecl P crbaSig crbaRef ∧ NoRedecl P rv32Sig rv32Ref ∧ NoRedecl P wv32Sig wv32Ref

theorem ccrl_sat {P : Program} (hF : Contains P [cpC, tpeC, teC]) : Sat P ccrlRef ccrlSpec :=
  BodyVCP.sat ccrl_body hF (fun sig S h => by simp [Contracts.env, List.lookup] at h)

theorem crbaA_sat (R : TRep) {P : Program} (hF : Contains P [cpC, tpC, ttC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) : Sat P crbaRef (crbaSpec P R) := by
  have hI := BodyVCP.sat (crba_body R) hF hV
  intro args σ o hpre hm
  obtain ⟨p, l, t, tmp, lfs, b, s, hargs, hH, hl, he, hs, hi⟩ := hpre
  have hC := CPAtH.elim hH
  exact hI args σ o ⟨p, l, t, tmp, lfs, b, s, hargs, hC, hH, classOK_of_cpAt hC, hl, he, hs, hi⟩ hm

/-- An instance method that `TCompactProtocol` inherits from `TProtocol`. -/
theorem chainN_tp {P : Program} (hF : P.findClass cpCls = some cpC) (hT : P.findClass tpCls = some tpC)
    (n : Nat) {sub : SubSig} {m : MethodDecl}
    (hm0 : Program.ClassDecl.findMethod cpC sub false = none)
    (hm : Program.ClassDecl.findMethod tpC sub false = some m) :
    P.chainN (n + 1 + 1) cpCls sub false = .jimple ⟨tpCls, m⟩ := by
  rw [Program.chainN.eq_2, hF]
  simp only [hm0]
  rw [show cpC.super = some tpCls from rfl]
  simp only []
  rw [Program.chainN.eq_2, hT]
  simp only [hm]

/-- A contract of a `TProtocol` instance method that `TCompactProtocol` inherits, from its proved
body and `NoRedecl`. -/
theorem contractOK_tp {P : Program} (hF : P.findClass cpCls = some cpC)
    (hT : P.findClass tpCls = some tpC) (hO : P.findClass "java.lang.Object" = none)
    {r : JType} {name : String} {ps : List JType} {m : MethodDecl} {S : Spec}
    (hm0 : Program.ClassDecl.findMethod cpC ⟨name, ps, r⟩ false = none)
    (hm : Program.ClassDecl.findMethod tpC ⟨name, ps, r⟩ false = some m)
    (hm1 : Program.ClassDecl.findMethod cpC ⟨name, ps, r⟩ true = none)
    (hm2 : Program.ClassDecl.findMethod tpC ⟨name, ps, r⟩ true = none)
    (hcl : name ≠ "<clinit>") (hsat : Sat P ⟨tpCls, m⟩ S)
    (hnr : NoRedecl P ⟨cpCls, r, name, ps⟩ ⟨tpCls, m⟩) :
    ContractOK P ⟨cpCls, r, name, ps⟩ S := by
  refine ⟨fun m' ht => ?_, fun c hc hs _ => vsat_of_jimple (hnr c hc hs) hsat⟩
  obtain ⟨hsel, -⟩ := ht
  rcases hsel with hs | hs | ⟨hc, -⟩
  · simp only [Program.selectStatic, MethodSig.sub] at hs
    rw [show Program.fuel P = 4093 + 1 + 1 + 1 from rfl, chainN_static_cp hF hT hO 4093 hm1 hm2] at hs
    cases hs
  · simp only [Program.selectSpecial, MethodSig.sub] at hs
    rw [show Program.fuel P = 4094 + 1 + 1 from rfl, chainN_tp hF hT 4094 hm0 hm] at hs
    simp only [Program.Target.jimple.injEq] at hs
    subst hs
    exact hsat
  · unfold clinitSig at hc
    simp only [MethodSig.mk.injEq] at hc
    exact absurd hc.2.2.1 hcl

theorem mem9 {d : ClassDecl} {cs : List ClassDecl}
    (h : ∀ d ∈ cs, d ∈ [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hd : d ∈ cs) : d ∈ [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC] := h d hd

/-- The contracts `readListBegin()` uses. -/
theorem valid_Γ6 (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) : Valid P (Γ6 P R) := by
  obtain ⟨hnb, hng, hnc, hnk, hn1, hn2⟩ := hn
  have hF7 : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC] := contains_sub hF (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    rcases hd with h | h | h | h | h | h | h <;> simp [h])
  have hcp : P.findClass cpCls = some cpC := hF.2 cpC (by simp)
  have htp : P.findClass tpCls = some tpC := hF.2 tpC (by simp)
  have hO : P.findClass "java.lang.Object" = none := findClass_of_noShadow hF.1 (by decide)
  have hV2 := valid_Γ2 R hF7 hV hn1 hn2
  intro sig S hS
  unfold Γ6 at hS
  by_cases h1 : sig = rbSig
  · rw [if_pos h1] at hS
    cases hS
    subst h1
    exact contractOK_cp hcp htp hO rfl rfl rfl (by decide)
      (rbA_sat R (contains_sub hF (by
        intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
        rcases hd with h | h | h <;> simp [h])) hV) hnb
  · rw [if_neg h1] at hS
    by_cases h2 : sig = gttSig
    · rw [if_pos h2] at hS
      cases hS
      subst h2
      exact contractOK_cp hcp htp hO rfl rfl rfl (by decide)
        (gtt_sat (contains_sub hF (by
          intro d hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
          rcases hd with h | h | h <;> simp [h]))) hng
    · rw [if_neg h2] at hS
      by_cases h3 : sig = ccrlSig
      · rw [if_pos h3] at hS
        cases hS
        subst h3
        exact contractOK_cp hcp htp hO rfl rfl rfl (by decide)
          (ccrl_sat (contains_sub hF (by
            intro d hd
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
            rcases hd with h | h | h <;> simp [h]))) hnc
      · rw [if_neg h3] at hS
        by_cases h4 : sig = crbaSig
        · rw [if_pos h4] at hS
          cases hS
          subst h4
          exact contractOK_tp hcp htp hO rfl rfl rfl rfl (by decide)
            (crbaA_sat R (contains_sub hF (by
              intro d hd
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
              rcases hd with h | h | h | h | h | h | h | h <;> simp [h])) hV) hnk
        · rw [if_neg h4] at hS
          exact hV2 sig S hS

theorem rlb_sat (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) : Sat P rlbRef (rlbSpecI P R) :=
  MethodVC.sat_of_valid (valid_Γ6 R hF hV hn) (rlb_body R P (contains_sub hF (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    rcases hd with h | h | h | h | h | h | h | h <;> simp [h])))

/-- **What `readListBegin()` does on a header byte `u` with a known type nibble** (and the size
`listSizeJ` reads): it returns a new `TList`, or throws a `TProtocolException` for a negative size
or one above the limit, or a `TTransportException` for an element type `getMinSerializedSize`
does not list. -/
theorem rlb_out (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) {σ : State} {p t tmp : Addr} {lim : I64}
    {u : UInt8} {rest0 rest : Bytes} {size : I32} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done)
    (hsrc : R.src σ t = u :: rest0) (hsz : listSizeJ u rest0 = some (size, rest))
    (hnib : (Spec.ttypeOfCompact (u.toNat % 16)).isSome = true)
    (hm : MExec P rlbRef [.ref p] σ o) :
    (∃ tt k σ' l lfs, Spec.ttypeOfCompact (u.toNat % 16) = some tt ∧ minSize tt = some k ∧
      0 ≤ size.toInt ∧ InLimit lim size ∧ o = .normal (some (.ref l)) σ' ∧
      σ'.heap l = some (.plain tlCls lfs) ∧
      Fields.get lfs (tlCls, "elemType") = some (.int (BitVec.ofNat 32 tt)) ∧
      Fields.get lfs (tlCls, "size") = some (.int size) ∧ R.src σ' t = rest ∧
      R.sink σ' t = R.sink σ t ∧ CPAt P R σ' p t tmp) ∨
    (∃ e σ' fs, o = .exc e σ' ∧ (size.toInt < 0 ∨ ¬ InLimit lim size) ∧
      σ'.heap e = some (.plain tpeCls fs)) ∨
    (∃ e σ' fs tt, o = .exc e σ' ∧ 0 ≤ size.toInt ∧ InLimit lim size ∧
      Spec.ttypeOfCompact (u.toNat % 16) = some tt ∧ minSize tt = none ∧
      σ'.heap e = some (.plain ttExcCls fs)) := by
  have hnibL : NibbleOKL (R.src σ t) := by
    intro u' rest' h
    rw [hsrc] at h
    injection h with e1 e2
    subst e1
    exact hnib
  have hpost := rlb_sat R hF hV hn [.ref p] σ o
    ⟨p, t, tmp, lim, rfl, hCP, CPAtH.intro hCP, hlim, h1, h2, h3, hnibL⟩ hm
  obtain ⟨fs, -, -, -, hp, htr, hte, -⟩ := hCP
  obtain ⟨fs', hp', hl⟩ := hlim
  rw [hp] at hp'
  simp only [Option.some.injEq, Obj.plain.injEq, true_and] at hp'
  subst hp'
  cases o with
  | normal r σ' =>
    simp only [rlbSpecI, Spec.of] at hpost
    unfold rlbN at hpost
    obtain ⟨u', rest', size', rest'', tt, k, l, lfs, hs1, hsz1, h0, hin, htt, hk, hsr, hsk, hC, hr, hl',
      hft, hfs, -⟩ := hpost p t tmp fs lim rfl hp htr hte hl
    rw [hsrc] at hs1
    injection hs1 with e1 e2
    subst e1 e2
    rw [hsz] at hsz1
    simp only [Option.some.injEq, Prod.mk.injEq] at hsz1
    obtain ⟨rfl, e3⟩ := hsz1
    exact Or.inl ⟨tt, k, σ', l, lfs, htt, hk, h0, hin, by rw [hr], hl', hft, hfs, by rw [hsr, e3], hsk, hC⟩
  | exc e σ' =>
    simp only [rlbSpecI, Spec.of] at hpost
    unfold rlbE at hpost
    rcases hpost p t tmp fs lim rfl hp htr hte hl with ⟨h0, -⟩ | ⟨u', rest', hs1, hnone, -⟩ |
      ⟨u', rest', size', rest'', hs1, hsz1, hc, w, hw⟩ |
      ⟨u', rest', size', rest'', tt, hs1, hsz1, h0, hin, htt, hms, w, hw⟩
    · rw [hsrc] at h0
      cases h0
    · rw [hsrc] at hs1
      injection hs1 with e1 e2
      subst e1 e2
      rw [hsz] at hnone
      cases hnone
    · rw [hsrc] at hs1
      injection hs1 with e1 e2
      subst e1 e2
      rw [hsz] at hsz1
      simp only [Option.some.injEq, Prod.mk.injEq] at hsz1
      obtain ⟨rfl, -⟩ := hsz1
      exact Or.inr (Or.inl ⟨e, σ', w, rfl, hc, hw⟩)
    · rw [hsrc] at hs1
      injection hs1 with e1 e2
      subst e1 e2
      rw [hsz] at hsz1
      simp only [Option.some.injEq, Prod.mk.injEq] at hsz1
      obtain ⟨rfl, -⟩ := hsz1
      exact Or.inr (Or.inr ⟨e, σ', w, tt, rfl, h0, hin, htt, hms, hw⟩)
  | wrong msg => simp only [rlbSpecI, Spec.of] at hpost

/-- The list header splits into its first byte (the type nibble `ety`) and the bytes `listSizeJ`
reads the size from. -/
theorem listHeader_cons {size ety : Nat} (hs : size < 2 ^ 31) (he : ety < 16) (rest : Bytes) :
    ∃ u rest0, Spec.listHeader size ety ++ rest = u :: rest0 ∧ u.toNat % 16 = ety ∧
      listSizeJ u rest0 = some (BitVec.ofNat 32 size, rest) := by
  by_cases h15 : size < 15
  · rw [Spec.listHeader_short h15 he]
    have hb : (UInt8.ofNat (16 * size + ety)).toNat = 16 * size + ety := by
      rw [UInt8.toNat_ofNat']; omega
    refine ⟨_, rest, rfl, by rw [hb]; omega, ?_⟩
    rw [listSizeJ_short (by rw [hb]; omega), hb, show (16 * size + ety) / 16 = size by omega]
  · rw [Spec.listHeader_long (by omega) he]
    have hb : (UInt8.ofNat (0xF0 + ety)).toNat = 0xF0 + ety := by
      rw [UInt8.toNat_ofNat']; omega
    exact ⟨_, Spec.varint size ++ rest, rfl, by rw [hb]; omega,
      listSizeJ_long (by rw [hb]; omega)
        (Spec.readVarint_varint 5 size rest (Spec.varint_length_le5 (by omega)))⟩

theorem ttypeOfCompact_dom : ∀ n tt, Spec.ttypeOfCompact n = some tt → n < 14 := by
  intro n tt h
  unfold Spec.ttypeOfCompact at h
  split at h <;> first | (cases h; decide) | cases h

theorem toInt_ofNat_nonneg {n : Nat} (h : n < 2 ^ 31) : 0 ≤ (BitVec.ofNat 32 n).toInt := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  split <;> omega

/-- **D for the list header**: on `Spec.listHeader size ety ++ rest` (`size < 2^31` within the
configured limit; `ety` a type nibble whose TType `tt` `getMinSerializedSize` lists: every known
nibble but 13, UUID), `readListBegin()` returns a new `TList` with element type `tt` and size
`size`, and leaves `rest`. -/
theorem rlb_D (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) {σ : State} {p t tmp : Addr} {lim : I64}
    {size ety tt : Nat} {rest : Bytes} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done)
    (hs : size < 2 ^ 31) (hin : InLimit lim (BitVec.ofNat 32 size))
    (htt : Spec.ttypeOfCompact ety = some tt) (hms : (minSize tt).isSome = true)
    (hsrc : R.src σ t = Spec.listHeader size ety ++ rest) (hm : MExec P rlbRef [.ref p] σ o) :
    ∃ σ' l lfs, o = .normal (some (.ref l)) σ' ∧ σ'.heap l = some (.plain tlCls lfs) ∧
      Fields.get lfs (tlCls, "elemType") = some (.int (BitVec.ofNat 32 tt)) ∧
      Fields.get lfs (tlCls, "size") = some (.int (BitVec.ofNat 32 size)) ∧
      R.src σ' t = rest ∧ R.sink σ' t = R.sink σ t ∧ CPAt P R σ' p t tmp := by
  have he : ety < 16 := Nat.lt_trans (ttypeOfCompact_dom _ _ htt) (by decide)
  obtain ⟨u, rest0, hcons, hmod, hsz⟩ := listHeader_cons hs he rest
  rw [hcons] at hsrc
  have hnib : (Spec.ttypeOfCompact (u.toNat % 16)).isSome = true := by rw [hmod, htt]; rfl
  rcases rlb_out R hF hV hn hCP hlim h1 h2 h3 hsrc hsz hnib hm with
    ⟨tt', k, σ', l, lfs, htt', -, -, -, ho, hl, hft, hfs, hsr, hsk, hC⟩ | ⟨e, σ', fs, -, hc, -⟩ |
    ⟨e, σ', fs, tt', -, -, -, htt', hms', -⟩
  · rw [hmod, htt] at htt'
    cases htt'
    exact ⟨σ', l, lfs, ho, hl, hft, hfs, hsr, hsk, hC⟩
  · rcases hc with hc | hc
    · exact absurd hc (Int.not_lt.mpr (toInt_ofNat_nonneg hs))
    · exact absurd hin hc
  · rw [hmod, htt] at htt'
    cases htt'
    rw [hms'] at hms
    cases hms

/-- **`exNegSize`** (`[0xF5, 0x80, 0x80, 0x80, 0x80, 0x08]`: long form, element type I32, size the
varint `2^31`): the specification rejects it (`NegSize`); Java reads the size as the `int` `-2^31`
and `readListBegin()` throws a `TProtocolException` (`checkContainerReadLength`). -/
theorem rlb_exNegSize (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) {σ : State} {p t tmp : Addr} {lim : I64}
    {rest : Bytes} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done)
    (hsrc : R.src σ t = Spec.exNegSize ++ rest) (hm : MExec P rlbRef [.ref p] σ o) :
    Spec.readListHeader Spec.exNegSize = none ∧
      ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain tpeCls fs) := by
  refine ⟨Spec.exNegSize_malformed.2.2, ?_⟩
  have hrv : Spec.readVarint 5 ([0x80, 0x80, 0x80, 0x80, 0x08] ++ rest) = some (2 ^ 31, rest) := by
    have h := Spec.readVarint_varint 5 (2 ^ 31) rest (by decide)
    rwa [show Spec.varint (2 ^ 31) = [0x80, 0x80, 0x80, 0x80, 0x08] by decide] at h
  have hsz := listSizeJ_long (u := 0xF5) (by decide) hrv
  rcases rlb_out R hF hV hn hCP hlim h1 h2 h3 hsrc hsz (by decide) hm with
    ⟨tt, k, σ', l, lfs, -, -, h0, -⟩ | ⟨e, σ', fs, ho, -, hw⟩ | ⟨e, σ', fs, tt, -, h0, -⟩
  · exact absurd h0 (by decide)
  · exact ⟨e, σ', fs, ho, hw⟩
  · exact absurd h0 (by decide)

/-- **A list header with element nibble 13 (UUID)**, e.g. the byte `0x0D` (no elements): the
specification reads it (`readListHeader`); Java's `readListBegin()` throws a `TTransportException`
(`getMinSerializedSize(16)` lists no UUID). -/
theorem rlb_uuid (R : TRep) {P : Program}
    (hF : Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tlC, tteC])
    (hV : Valid P (tContracts R).env) (hn : NoRedeclL P) {σ : State} {p t tmp : Addr} {lim : I64}
    {size : Nat} {rest : Bytes} {o : Outcome}
    (hCP : CPAt P R σ p t tmp) (hlim : LimitAt σ p lim) (h1 : σ.initOf tpeCls = .done)
    (h2 : σ.initOf tlCls = .done) (h3 : σ.initOf ttExcCls = .done)
    (hs : size < 2 ^ 31) (hin : InLimit lim (BitVec.ofNat 32 size))
    (hsrc : R.src σ t = Spec.listHeader size 13 ++ rest) (hm : MExec P rlbRef [.ref p] σ o) :
    Spec.readListHeader (Spec.listHeader size 13 ++ rest) = some ((size, 13), rest) ∧
      ∃ e σ' fs, o = .exc e σ' ∧ σ'.heap e = some (.plain ttExcCls fs) := by
  refine ⟨Spec.readListHeader_listHeader hs (by decide) rest, ?_⟩
  obtain ⟨u, rest0, hcons, hmod, hsz⟩ := listHeader_cons hs (by decide : 13 < 16) rest
  rw [hcons] at hsrc
  have hnib : (Spec.ttypeOfCompact (u.toNat % 16)).isSome = true := by rw [hmod]; rfl
  rcases rlb_out R hF hV hn hCP hlim h1 h2 h3 hsrc hsz hnib hm with
    ⟨tt, k, σ', l, lfs, htt, hk, -⟩ | ⟨e, σ', fs, -, hc, -⟩ | ⟨e, σ', fs, tt, ho, -, -, -, -, hw⟩
  · rw [hmod] at htt
    cases htt
    cases hk
  · rcases hc with hc | hc
    · exact absurd hc (Int.not_lt.mpr (toInt_ofNat_nonneg hs))
    · exact absurd hin hc
  · exact ⟨e, σ', fs, ho, hw⟩

end EquivLean.Demo.Thrift.Java
