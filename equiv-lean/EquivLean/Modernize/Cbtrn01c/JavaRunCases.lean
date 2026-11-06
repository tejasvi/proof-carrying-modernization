import EquivLean.Modernize.Cbtrn01c.JavaRunInj
import EquivLean.Modernize.Cbtrn01c.JavaRunExit
import EquivLean.Modernize.Cbtrn01c.JavaRunEof
import EquivLean.Modernize.Cbtrn01c.JavaRunRead
import EquivLean.Modernize.Cbtrn01c.JavaRunXrefNone
import EquivLean.Modernize.Cbtrn01c.JavaRunXrefNext
import EquivLean.Modernize.Cbtrn01c.JavaRunXrefFound
import EquivLean.Modernize.Cbtrn01c.JavaRunAcctNone
import EquivLean.Modernize.Cbtrn01c.JavaRunAcctNext
import EquivLean.Modernize.Cbtrn01c.JavaRunAcctFound

/-!
# CBTRN01C → Java: the cut points of `run`, by cases

`run_seg29`, `run_seg60`, `run_seg92`: from the invariant of the cut point (and the precondition),
the case of the path taken, with the facts each case theorem asks for (the input records read
through `dal_of_rec`, `xref_of_rec`, `acct_of_rec`; the string and `long` comparisons decided).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

theorem pow11_le_pow18 : (10 : Nat) ^ 11 ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) (by decide)
theorem pow9_le_pow18 : (10 : Nat) ^ 9 ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) (by decide)

theorem xref_valid_acct {xv : List EquivLean.Cobol.Rec.FVal} (hv : CardXrefRecord.Valid xv) :
    (Model.numOf (xv.getD 2 default)).natAbs < 10 ^ 11 := by
  have h2 := Forall2.getD hv 2 (by decide)
  have hk : (CardXrefRecord.fields.getD 2 default).desc.kind =
      .num CardDemo.Cbtrn01c.XREF_ACCT_ID.fmt := rfl
  cases e : xv.getD 2 default with
  | str bs => rw [e] at h2; obtain ⟨⟨j, hj⟩, -⟩ := h2; rw [hk] at hj; cases hj
  | num n =>
    rw [e] at h2
    obtain ⟨fmt, hk', -, -, hh, -⟩ := h2
    rw [hk] at hk'
    cases hk'
    exact natAbs_lt_of_holds' rfl hh rfl

theorem jint_ofBool_false : JInt.ofBool false = 0#32 := rfl
theorem jint_ofBool_true : JInt.ofBool true = 1#32 := rfl

set_option maxHeartbeats 0 in
/-- **The loop head**: end of file met (exit), a record left (read), or the end of file now. -/
theorem run_seg29 (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State)
    (hpre : runPreG a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 (runArgs a1 a2 a3 a4 a5 a6) σ0)
    (h : J29 a1 a3 a5 vals1 vals3 vals5 (runArgs a1 a2 a3 a4 a5 a6) σ0 fr σ) :
    RunWP a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 29 fr σ := by
  obtain ⟨-, ⟨⟨et1, xs1, h1a, h1len, h1f⟩, -, -, hv1, -, -⟩, -⟩ := hpre
  obtain ⟨k, e, d, res, l, ⟨f10, f35, f4, f9, f11, f17, hk, f7, f8, f5, he, f1, hcur,
    ⟨fsR, hR1, hR2, hR3⟩, hres0, hl0, hrl, ⟨hg1, hg2⟩, hinit⟩, ⟨ys, m, hl, hD⟩⟩ := h
  have hcur := Hide.elim hcur
  have hlen : xs1.length = vals1.length := h1f.length_eq
  have ha1 : σ.heap a1 = some (.array et1 xs1) := heap_of_grows ⟨hg1, hg2⟩ h1a
  cases e with
  | true =>
    have hkl := he rfl
    subst hkl
    exact run_seg29_exit a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ d res l fsR ys m
      (by rw [f5]; rfl) f9 f11 hR1 hR2 hR3 hrl hl hD
  | false =>
    rw [jint_ofBool_false] at f5 f7 f8
    by_cases hkl : k < vals1.length
    · have hkx : k < xs1.length := by omega
      have hrec : JRecAt DalytranRecord dalCls σ xs1[k] vals1[k] :=
        jrecAt_of_grows ⟨hg1, hg2⟩ (forall2_get h1f k hkx)
      obtain ⟨c, hc, hdal, hline, hcurk⟩ := dal_of_rec hrec (hv1 _ (List.getElem_mem hkl))
      obtain ⟨c', fsc, cs, ci, hcc, hcobj, hcard, hcs, hid, hci⟩ := hcurk
      have hcc' : c = c' := Value.ref.inj (hc.symm.trans hcc)
      subst hcc'
      exact run_seg29_read a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ k res l c cs ci et1 xs1
        fsc fsR ys m hkl f4 f35 f5 f7 f8 f9 f10 f11 f17 ha1 h1len hlen hkx hc _ rfl hdal hline
        hcobj hcard _ _ rfl rfl hcs hid hci hR1 hR2 hR3 hres0 hl0 hrl hg1 hg2 hl hD hinit
    · have hk' : k = vals1.length := by omega
      subst hk'
      obtain ⟨x, fsx, cs, ci, rfl, hx, hcard, hcs, hid, hci⟩ := hcur
      exact run_seg29_eof a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ res l x cs ci et1 xs1 fsx
        fsR ys m f1 f4 f35 f5 f7 f8 f9 f10 f11 f17 ha1 h1len hlen hx hcard hcs hid hci hR1 hR2
        hR3 hres0 hl0 hrl hg1 hg2 hl hD hinit

set_option maxHeartbeats 0 in
/-- **The cross-reference search**: no record left, a match, or the next record. -/
theorem run_seg60 (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State)
    (hpre : runPreG a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 (runArgs a1 a2 a3 a4 a5 a6) σ0)
    (h : J60 a1 a3 a5 vals1 vals3 vals5 (runArgs a1 a2 a3 a4 a5 a6) σ0 fr σ) :
    RunWP a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 60 fr σ := by
  obtain ⟨-, ⟨-, ⟨et3, xs3, h3a, h3len, h3f⟩, -, -, hv3, -⟩, -⟩ := hpre
  obtain ⟨k, e, d, res, l, i, cs, ⟨f10, f35, f4, f9, f11, f17, hk, f7, f8, f5, he, f1, hcur,
    ⟨fsR, hR1, hR2, hR3⟩, hres0, hl0, hrl, ⟨hg1, hg2⟩, hinit⟩, hek, ⟨ys, m, hl, hD⟩, f16, hi,
    f20, hcs20, f34, f12, hno⟩ := h
  have hcur := Hide.elim hcur
  obtain ⟨x, fsx, cc, ci, rfl, hx, hcard, hccs, hid, hci⟩ := hcur
  have hlen : xs3.length = vals3.length := h3f.length_eq
  have ha3 : σ.heap a3 = some (.array et3 xs3) := heap_of_grows ⟨hg1, hg2⟩ h3a
  by_cases hil : i < vals3.length
  · have hi3 : i < xs3.length := by omega
    have hrec : JRecAt CardXrefRecord xrefCls σ xs3[i] vals3[i] :=
      jrecAt_of_grows ⟨hg1, hg2⟩ (forall2_get h3f i hi3)
    obtain ⟨xr, fsx3, xc, hxeq, hxr, hxc, hxcs, hcu, hac, hcub, hacb⟩ :=
      xref_of_rec hrec (hv3 _ (List.getElem_mem hil))
    by_cases hm : cardMatch (curT vals1 k) vals3[i] = true
    · have heq := (cardMatch_iff _ _).1 hm
      exact run_seg60_found a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ k e res l x cs ci et3 xs3
        fsx fsR ys m _ _ _ hk he f1 f4 f35 f5 f7 f8 f9 f10 f11 f17 i hil f16 xr xc fsx3 hi3 hxeq
        hxr hxc hxcs heq _ _ hcu hac (by simpa using hcub) (by simpa using hacb) rfl rfl hm f34
        f12 ha3 h3len hlen hx cc hcard hccs rfl rfl rfl hcs20 hid hci hR1 hR2 hR3 hres0 hl0 hrl
        hg1 hg2 hl hD hek f20 hno hinit
    · have hm' : cardMatch (curT vals1 k) vals3[i] = false := by simpa using hm
      have hne : ¬ cp037Str (Model.strOf ((curT vals1 k).getD 10 default)) =
          cp037Str (Model.strOf (vals3[i].getD 0 default)) := fun h => hm ((cardMatch_iff _ _).2 h)
      exact run_seg60_next a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ k e res l x cs ci et3 xs3
        fsx fsR ys m _ _ _ hk he f1 f4 f35 f5 f7 f8 f9 f10 f11 f17 i hil f16 xr xc fsx3 hi3 hxeq
        hxr hxc hxcs hne hm' f34 f12 ha3 h3len hlen hx cc hcard hccs rfl rfl rfl hcs20 hid hci hR1
        hR2 hR3 hres0 hl0 hrl hg1 hg2 hl hD hek f20 hno hinit
  · have hi' : i = vals3.length := by omega
    subst hi'
    exact run_seg60_none a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ k e res l x cc ci et3 xs3
      fsx fsR ys m hk he f1 f4 f35 f5 f7 f8 f9 f10 f11 f17 f16 f34 f12 ha3 h3len hlen hx hcard
      hccs hid hci hR1 hR2 hR3 hres0 hl0 hrl hg1 hg2 hl hD hek hno hinit

set_option maxHeartbeats 0 in
/-- **The account search**: no record left, a match, or the next record. -/
theorem run_seg92 (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State)
    (hpre : runPreG a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 (runArgs a1 a2 a3 a4 a5 a6) σ0)
    (h : J92 a1 a3 a5 vals1 vals3 vals5 (runArgs a1 a2 a3 a4 a5 a6) σ0 fr σ) :
    RunWP a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 92 fr σ := by
  obtain ⟨-, ⟨-, -, ⟨et5, xs5, h5a, h5len, h5f⟩, -, hv3, hv5⟩, -⟩ := hpre
  obtain ⟨k, e, d, res, l, j, xv, ⟨f10, f35, f4, f9, f11, f17, hk, f7, f8, f5, he, f1, hcur,
    ⟨fsR, hR1, hR2, hR3⟩, hres0, hl0, hrl, ⟨hg1, hg2⟩, hinit⟩, hek, hfx, ⟨ys, m, hl, hD⟩, f18, hj,
    f13, f15, f14, f32, hno⟩ := h
  have hcur := Hide.elim hcur
  obtain ⟨x, fsx, cs, ci, rfl, hx, hcard, hcs, hid, hci⟩ := hcur
  have hlen : xs5.length = vals5.length := h5f.length_eq
  have ha5 : σ.heap a5 = some (.array et5 xs5) := heap_of_grows ⟨hg1, hg2⟩ h5a
  have hxv : xv ∈ vals3 := List.mem_of_find?_eq_some hfx
  have hacb := xref_valid_acct (hv3 _ hxv)
  by_cases hjl : j < vals5.length
  · have hj5 : j < xs5.length := by omega
    have hrec : JRecAt AccountRecord acctCls σ xs5[j] vals5[j] :=
      jrecAt_of_grows ⟨hg1, hg2⟩ (forall2_get h5f j hj5)
    obtain ⟨ar, fsa, hxeq, har, haid, haidb⟩ := acct_of_rec hrec (hv5 _ (List.getElem_mem hjl))
    have hu := Nat.lt_of_lt_of_le haidb pow11_le_pow18
    have hw := Nat.lt_of_lt_of_le hacb pow11_le_pow18
    by_cases hm : acctMatch xv vals5[j] = true
    · have heq := (acctMatch_iff _ _ hu hw).1 hm
      exact run_seg92_found a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ k e res l x cs ci et5 xs5
        fsx fsR ys m _ _ xv _ hk he f1 f4 f35 f5 f7 f8 f9 f10 f11 f17 j hjl f18 ar fsa _ hj5
        hxeq har haid heq hm f13 f15 f14 f32 ha5 h5len hlen rfl rfl rfl (by simpa using hacb) hx
        hcard hcs hid hci hR1 hR2 hR3 hres0 hl0 hrl hg1 hg2 hl hD hek hfx hno hinit
    · have hm' : acctMatch xv vals5[j] = false := by simpa using hm
      have hne : BitVec.ofInt 64 (Model.numOf (vals5[j].getD 0 default)) ≠
          BitVec.ofInt 64 (Model.numOf (xv.getD 2 default)) :=
        fun h => hm ((acctMatch_iff _ _ hu hw).2 h)
      exact run_seg92_next a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ k e res l x cs ci et5 xs5
        fsx fsR ys m _ _ xv _ hk he f1 f4 f35 f5 f7 f8 f9 f10 f11 f17 j hjl f18 ar fsa _ hj5
        hxeq har haid hne hm' f13 f15 f14 f32 ha5 h5len hlen rfl rfl rfl (by simpa using hacb) hx
        hcard hcs hid hci hR1 hR2 hR3 hres0 hl0 hrl hg1 hg2 hl hD hek hfx hno hinit
  · have hj' : j = vals5.length := by omega
    subst hj'
    exact run_seg92_none a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 fr σ k e res l x cs ci et5 xs5
      fsx fsR ys m _ _ xv _ hk he f1 f4 f35 f5 f7 f8 f9 f10 f11 f17 f18 f13 f15 f14 f32 ha5 h5len
      hlen rfl rfl rfl (by simpa using hacb) hx hcard hcs hid hci hR1 hR2 hR3 hres0 hl0 hrl hg1
      hg2 hl hD hek hfx hno hinit

end EquivLean.Modernize.Cbtrn01c.Java
