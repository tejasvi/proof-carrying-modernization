-- Termination package by JimpleLean's session: TermPk/Cbtrn01c/JavaTermRead.lean (sha256 baf162e0efe614ed...); only the module root renamed.
import EquivLean.Modernize.Cbtrn01c.JavaRunRead
import EquivLean.Modernize.Cbtrn01c.JavaTermDefs

/-!
# CBTRN01C → Java, termination: thin twin of `run_seg29_read` (`JavaRunRead`)

The statement and the preamble of the original, the cut assertions the variants (`runVs`),
calls by `callWPT` without preconditions (`callWPThin`); variant goals by the program variant closer.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple EquivLean.Modernize.TermCommon

namespace EquivLean.Modernize.Cbtrn01c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_tseg29_read (a1 a2 a3 a4 a5 a6 : Addr)
    (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State) (k : Nat) (res l c cs ci : Addr) (et1 : JType)
    (xs1 : List Value) (fsc fsR : List (FieldKey × Value)) (ys : List Value) (m : Nat)
    (hk : k < vals1.length)
    (f4 : fr.get 4 = some (.ref a5)) (f35 : fr.get 35 = some (.ref a3))
    (f5 : fr.get 5 = some (.int 0#32)) (f7 : fr.get 7 = some (.int 0#32))
    (f8 : fr.get 8 = some (.int 0#32)) (f9 : fr.get 9 = some (.ref res))
    (f10 : fr.get 10 = some (.ref a1)) (f11 : fr.get 11 = some (.ref l))
    (f17 : fr.get 17 = some (.int (BitVec.ofNat 32 k)))
    (ha1 : σ.heap a1 = some (.array et1 xs1)) (hlen1 : xs1.length < 2147483648)
    (hlen : xs1.length = vals1.length) (hkx : k < xs1.length) (hx : xs1[k]'hkx = .ref c)
    (L : JStr) (hL : L = jline (Model.DalytranRecord.textS vals1[k]))
    (hdal : DalOk σ c) (hline : dalLine σ c = L)
    (hc : σ.heap c = some (.plain dalCls fsc))
    (hcard : Fields.get fsc (dalCls, "dalytranCardNum") = some (.ref cs))
    (T I : List UInt8) (hT : T = Model.strOf (vals1[k].getD 10 default))
    (hI : I = Model.strOf (vals1[k].getD 0 default))
    (hcs : σ.heap cs = some (.str (cp037Str T)))
    (hid : Fields.get fsc (dalCls, "dalytranId") = some (.ref ci))
    (hci : σ.heap ci = some (.str (cp037Str I)))
    (hR1 : σ.heap res = some (.plain "Cbtrn01c$Result" fsR))
    (hR2 : Fields.get fsR ("Cbtrn01c$Result", "displays") = some (.ref l))
    (hR3 : Fields.get fsR ("Cbtrn01c$Result", "abended") = some (.int 0))
    (hres0 : σ0.next ≤ res) (hl0 : σ0.next ≤ l) (hrl : res ≠ l)
    (hg1 : σ0.next ≤ σ.next) (hg2 : ∀ x, x < σ0.next → σ.heap x = σ0.heap x)
    (hl : σ.heap l = some (.list .arrayList ys m))
    (hD : Hide (Forall2 (JStrAt σ) ys ((headL vals1 vals3 vals5 k false).map jline)))
    (hinit : σ.initOf "Cbtrn01c" = .done) :
    RunThinWP a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 29 fr σ := by

  have hcl : c ≠ l := by intro h; subst h; rw [hl] at hc; simp at hc
  have hcsl : cs ≠ l := by intro h; subst h; rw [hl] at hcs; simp at hcs
  have hcil : ci ≠ l := by intro h; subst h; rw [hl] at hci; simp at hci
  have hL' := Hide.intro hL
  have hT' := Hide.intro hT
  have hI' := Hide.intro hI
  clear hL hT hI
  have hdal' := Hide.intro hdal
  have hR1' := Hide.intro hR1
  have hg2' := Hide.intro hg2
  have hcs' := Hide.intro hcs
  have hci' := Hide.intro hci
  have hid' := Hide.intro hid
  clear hdal hR1 hg2 hcs hci hid
  unfold RunThinWP
  jvc [runInv, runSpecG, callees, spacesSig, digitsSig, formatDalytranSig, formatDalytranSpec,
    runArgs, inlineFuel, fields_get_cons, fields_get_nil, jstrLitT, dalOk_alloc2, dalLine_alloc2,
    dalCls, nat_mod_2_32, Grows]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip
  all_goals cbtrn01c_variant

end EquivLean.Modernize.Cbtrn01c.Java
