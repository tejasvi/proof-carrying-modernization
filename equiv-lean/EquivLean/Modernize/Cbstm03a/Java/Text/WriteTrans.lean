import EquivLean.Modernize.Cbstm03a.Java.Text.Callees2
import EquivLean.Modernize.Cbstm03a.Java.Text.SubLemma

/-!
# CBSTM03A → Java: `writeTrans`

Verified for every fixed choice of ghost values, `stmt` and `html` inlined (depth 1), against `fix` (`Iface0`),
`fmtZ` and `star` (`Iface1`: `fmtZSpec`, `starSpec`); then its contract `writeTransSpec` of `Iface3`.
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans Keeps keeps_refl keeps_setObj' keeps_alloc' keeps_grows')

namespace EquivLean.Modernize.Cbstm03a.Java.Txt

attribute [-simp] List.reduceReplicate

def writeTransSpecG (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (tv rv : Value) (amt : I64)
    (t tr : JStr) : Spec := Spec.of
  (fun args σ => args = [.ref res, tv, rv, .long amt] ∧ ResAtL σ res ld ls lh disp st ht ab ∧ JStrAt σ tv t ∧
     JStrAt σ rv tr ∧ 65 ≤ tr.length ∧ tr.length < 2147483648 ∧ t.length < 1000000 ∧
     -9223372036854775808 < amt.toInt ∧ σ.initOf "Cbstm03a" = .done)
  (fun _ σ r σ' => r = none ∧
     ResAtL σ' res ld ls lh disp (st ++ (jWriteTrans (argText σ tv) (argText σ rv) amt.toInt).1)
       (ht ++ (jWriteTrans (argText σ tv) (argText σ rv) amt.toInt).2) ab ∧
     KeepsRes res ld ls lh σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

theorem forall2_app {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β} {c : List α} {d : List β}, Forall2 R a b → Forall2 R c d → Forall2 R (a ++ c) (b ++ d)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h1 h2, h => .cons h1 (forall2_app h2 h)

theorem listAt_app {σ : State} {l : Addr} {xs zs : List Value} {m : Nat} {ss ts : List JStr}
    (hl : σ.heap l = some (.list .arrayList (xs ++ zs) m)) (h1 : Forall2 (JStrAt σ) xs ss)
    (h2 : Forall2 (JStrAt σ) zs ts) : ListAt σ l (ss ++ ts) :=
  ⟨_, _, hl, forall2_app h1 h2⟩

theorem strMono_step_setObj_list {σ0 σ : State} {l : Addr} {o : Obj} {xs : List Value} {m : Nat}
    (h : StrMono σ0 σ) (hl : σ.heap l = some (.list .arrayList xs m)) : StrMono σ0 (σ.setObj l o) :=
  strMono_step_setObj h (not_str_of_list hl)

/-- `txt_strmono` with the updated list looked up (`hsimpK`, then the entry facts). Reflexivity is tried only at a
state that is no update or allocation (cheap: two variables), before a callee step (else the walk passes the target). -/
macro "txt_strmono2" : tactic => `(tactic| repeat (first | (refine strMono_step_setObj_list ?_ (by hsimpK; first | rfl | assumption)) | (refine strMono_step_alloc ?_) | exact strMono_refl _ | (refine strMono_step_growsK ?_ (by assumption))))

attribute [local irreducible] fixStr

set_option maxRecDepth 8000 in
set_option maxHeartbeats 30000000 in
theorem writeTrans_vc (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (tv rv : Value) (amt : I64)
    (t tr : JStr) :
    MethodVC Gen.prog wtCallees.env 1 writeTransRef
      (writeTransSpecG res ld ls lh disp st ht ab tv rv amt t tr) [] 120 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩⟩
  obtain ⟨h0, hR, ⟨xt, htv, hxt⟩, ⟨xr, hrv, hxr⟩, hl1, hl2, hl3, hamt, hI⟩ := hpre
  have hK : Kept (ResAtL σ0 res ld ls lh disp st ht ab) := Kept.intro hR
  obtain ⟨fs, hres, gd, gs, gh, gab, n1, n2, n3, ⟨xd, md, hld, -⟩, ⟨xs, ms, hls, -⟩, ⟨xh, mh, hlh, -⟩⟩ := hR
  have e1 : res ≠ ls := ne_of_heap hres hls (by intro h; cases h)
  have e2 : res ≠ lh := ne_of_heap hres hlh (by intro h; cases h)
  have e3 : xt ≠ ls := ne_of_heap hxt hls (by intro h; cases h)
  have e4 : xt ≠ lh := ne_of_heap hxt hlh (by intro h; cases h)
  have e5 : xr ≠ ls := ne_of_heap hxr hls (by intro h; cases h)
  have e6 : xr ≠ lh := ne_of_heap hxr hlh (by intro h; cases h)
  have n3' : lh ≠ ls := Ne.symm n3
  simp only [writeTransSpecG, Spec.of]
  jvc [ite_nat_ne, wtCallees, fixSig, fmtZSig, starSig, fixSpec, fmtZSpec, starSpec, grows_split, fmtZStr_length, starStr_length, StrNN,
    StrOk, argText, strOf]
  all_goals (try (simp only [List.length_append, List.length_cons, List.length_nil, fmtZStr_length, starStr_length, List.length_replicate]; omega))
  all_goals have hR0 := Kept.elim hK
  · obtain ⟨-, -, -, -, -, -, -, -, -, Ld, ⟨xs0, ms0, hls0, fsl⟩, ⟨xh0, mh0, hlh0, fh⟩⟩ := hR0
    rw [hls] at hls0
    obtain ⟨⟩ := hls0
    rw [hlh] at hlh0
    obtain ⟨⟩ := hlh0
    refine resAtL_of (fs' := fs) (Kept.elim hK) ?_ gd gs gh gab ?_ ?_ ?_
    · (hsimpK; try exact hres)
    · exact listAt_mono Ld (by hsimpK) (by txt_strmono2)
    · refine listAt_app (xs := xs) (by hsimpK; try rfl) (forall2_jstr_mono (by txt_strmono2) fsl) ?_
      · simp only [jWriteTrans]
        refine .cons ⟨_, rfl, heap_of_strMono_eq (by assumption) (by txt_strmono2) ?_⟩ .nil
        first | (simp only [sl, sub_16_65 tr hl1, space, chDollar, fmtZI_eq, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]; done) | (simp [sl, sub_16_65 tr hl1, space, chDollar, fmtZI_eq]; done) | trace_state
    · refine listAt_app (xs := xh) (by hsimpK; try rfl) (forall2_jstr_mono (by txt_strmono2) fh) ?_
      · simp only [jWriteTrans]
        repeat (refine .cons ⟨_, rfl, heap_of_strMono_eq (by assumption) (by txt_strmono2) ?_⟩ ?_; rotate_left)
        all_goals first | exact .nil | rfl | (simp only [hl, jl, starT_eq, fmtZI_eq, sub_16_65 tr hl1]; done) | (simp [hl, jl, starT_eq, fmtZI_eq, sub_16_65 tr hl1]; done) | trace_state
  · exact keepsRes_of_keeps (by txt_keepsR)

theorem writeTrans_sat (hV : Valid Gen.prog wtCallees.env) :
    Sat Gen.prog writeTransRef writeTransSpec := by
  intro args σ o hpre hm
  obtain ⟨res, ld, ls, lh, disp, st, ht, ab, tv, rv, amt, t, tr, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpre
  have hG := MethodVC.sat_of_valid hV (writeTrans_vc res ld ls lh disp st ht ab tv rv amt t tr) args σ o
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ hm
  cases o with
  | normal r σ' =>
    intro res' ld' ls' lh' disp' st' ht' ab' tv' rv' amt' g0 g1
    rw [h0] at g0
    obtain ⟨hr, ht', hr', ha'⟩ : res = res' ∧ tv = tv' ∧ rv = rv' ∧ amt = amt' := by simpa using g0
    subst hr ht' hr' ha'
    exact MethodVC.sat_of_valid hV (writeTrans_vc res ld' ls' lh' disp' st' ht' ab' tv rv amt t tr) args σ
      (.normal r σ') ⟨h0, g1, h2, h3, h4, h5, h6, h7, h8⟩ hm
  | exc e σ' => exact hG.elim
  | wrong msg => exact hG.elim

end EquivLean.Modernize.Cbstm03a.Java.Txt

#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.writeTrans_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.writeTrans_sat
