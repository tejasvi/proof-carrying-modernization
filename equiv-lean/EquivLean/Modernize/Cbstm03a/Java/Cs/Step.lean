import EquivLean.Modernize.Cbstm03a.Java.Cs.Lib

/-!
# CBSTM03A → Java: `createStatement`, one call of `html` or `stmt`

A call `html(res, s)` / `stmt(res, s)` at statement `pc` (the argument a literal or a local), answered by the
contract of `Iface3`: the paths from `pc` hold when the paths from `pc + 1` hold for every state the contract
allows (the `Result` holding one more line, `KeepsRes`, the class state kept).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

theorem sel_html : Gen.prog.selectStatic htmlSig = .jimple htmlRef := by rfl
theorem sel_stmt : Gen.prog.selectStatic stmtSig = .jimple stmtRef := by rfl
theorem env_html : csCallees.env htmlSig = some htmlSpec := by rfl
theorem env_stmt : csCallees.env stmtSig = some stmtSpec := by rfl
theorem prog_cbstm : Gen.prog.isProgClass "Cbstm03a" = true := by rfl

set_option maxHeartbeats 1000000 in
theorem wp_html_lit {I : Cuts} {Post : Outcome → Prop} {n pc : Nat} {fr : Frame} {σ : State} {lit : String}
    {res ld ls lh : Addr} {disp st ht : List JStr} {ab : Bool}
    (hs : body.stmtAt pc = some (.invoke (.static htmlSig [.loc 22, .const (.str lit)])))
    (h22 : fr.get 22 = some (.ref res)) (hR : ResAtL σ res ld ls lh disp st ht ab)
    (hini : σ.initOf "Cbstm03a" = .done) (hlen : (JStr.ofString lit).length < 2147483648)
    (hk : ∀ σ', ResAtL σ' res ld ls lh disp st (ht ++ [hl (JStr.ofString lit)]) ab →
      KeepsRes res ld ls lh (σ.alloc (.str (JStr.ofString lit))).2 σ' → σ'.inits = σ.inits →
      σ'.statics = σ.statics →
      match I.lookup (pc + 1) with
      | some A => A fr σ'
      | none => bodyWP Gen.prog (callWP Gen.prog csCallees.env 1) body I Post n (pc + 1) fr σ') :
    bodyWP Gen.prog (callWP Gen.prog csCallees.env 1) body I Post (n + 1) pc fr σ := by
  rw [bodyWP_succ]
  simp only [step, hs, stepStmt, evalInvoke, evalArgs, evalImm, h22, Option.map_some, evalConst, allocStr,
    sel_html]
  have hcls : htmlRef.cls = "Cbstm03a" := rfl
  simp only [hcls, initThen, ensureInit, prog_cbstm, Bool.not_true, Bool.false_eq_true, ite_false,
    State.initOf_alloc, hini, Res.bind_ret, callM, Res.bind_call, wpR, callWP, env_html, State.alloc_fst]
  refine ⟨⟨Or.inl sel_html, rfl⟩, ⟨res, ld, ls, lh, disp, st, ht, ab, _, rfl, resAtL_alloc hR _,
    Or.inr ⟨σ.next, _, rfl, by simp [State.heap_alloc], hlen⟩, by rw [State.initOf_alloc]; exact hini⟩, ?_⟩
  intro o ho
  cases o with
  | normal r σ' =>
    simp only [htmlSpec, Spec.of] at ho
    obtain ⟨-, hR', hK', hi', hs'⟩ := ho res ld ls lh disp st ht ab _ rfl (resAtL_alloc hR _)
    have harg : argText (σ.alloc (.str (JStr.ofString lit))).2 (.ref σ.next) = JStr.ofString lit := by
      simp [argText, strOf, State.heap_alloc]
    rw [harg] at hR'
    simp only [Res.bind_ret, wpR, outToEv, afterEv, afterStep]
    exact hk σ' hR' hK' (by rw [hi']; rfl) (by rw [hs']; rfl)
  | exc e σ' => simp only [htmlSpec, Spec.of] at ho
  | wrong m => simp only [htmlSpec, Spec.of] at ho


set_option maxHeartbeats 1000000 in
theorem wp_html_loc {I : Cuts} {Post : Outcome → Prop} {n pc k : Nat} {fr : Frame} {σ : State} {x : Addr}
    {s : JStr} {res ld ls lh : Addr} {disp st ht : List JStr} {ab : Bool}
    (hs : body.stmtAt pc = some (.invoke (.static htmlSig [.loc 22, .loc k])))
    (h22 : fr.get 22 = some (.ref res)) (hkx : fr.get k = some (.ref x)) (hx : σ.heap x = some (.str s))
    (hR : ResAtL σ res ld ls lh disp st ht ab)
    (hini : σ.initOf "Cbstm03a" = .done) (hlen : s.length < 2147483648)
    (hk : ∀ σ', ResAtL σ' res ld ls lh disp st (ht ++ [hl s]) ab →
      KeepsRes res ld ls lh σ σ' → σ'.inits = σ.inits → σ'.statics = σ.statics →
      match I.lookup (pc + 1) with
      | some A => A fr σ'
      | none => bodyWP Gen.prog (callWP Gen.prog csCallees.env 1) body I Post n (pc + 1) fr σ') :
    bodyWP Gen.prog (callWP Gen.prog csCallees.env 1) body I Post (n + 1) pc fr σ := by
  rw [bodyWP_succ]
  simp only [step, hs, stepStmt, evalInvoke, evalArgs, evalImm, h22, hkx, Option.map_some, sel_html]
  have hcls : htmlRef.cls = "Cbstm03a" := rfl
  simp only [hcls, initThen, ensureInit, prog_cbstm, Bool.not_true, Bool.false_eq_true, ite_false,
    hini, Res.bind_ret, callM, Res.bind_call, wpR, callWP, env_html]
  refine ⟨⟨Or.inl sel_html, rfl⟩, ⟨res, ld, ls, lh, disp, st, ht, ab, _, rfl, hR,
    Or.inr ⟨x, s, rfl, hx, hlen⟩, hini⟩, ?_⟩
  intro o ho
  cases o with
  | normal r σ' =>
    simp only [htmlSpec, Spec.of] at ho
    obtain ⟨-, hR', hK', hi', hs'⟩ := ho res ld ls lh disp st ht ab _ rfl hR
    have harg : argText σ (.ref x) = s := by simp [argText, strOf, hx]
    rw [harg] at hR'
    simp only [outToEv, afterEv, afterStep]
    exact hk σ' hR' hK' hi' hs'
  | exc e σ' => simp only [htmlSpec, Spec.of] at ho
  | wrong m => simp only [htmlSpec, Spec.of] at ho

set_option maxHeartbeats 1000000 in
theorem wp_stmt_loc {I : Cuts} {Post : Outcome → Prop} {n pc k : Nat} {fr : Frame} {σ : State} {x : Addr}
    {s : JStr} {res ld ls lh : Addr} {disp st ht : List JStr} {ab : Bool}
    (hs : body.stmtAt pc = some (.invoke (.static stmtSig [.loc 22, .loc k])))
    (h22 : fr.get 22 = some (.ref res)) (hkx : fr.get k = some (.ref x)) (hx : σ.heap x = some (.str s))
    (hR : ResAtL σ res ld ls lh disp st ht ab)
    (hini : σ.initOf "Cbstm03a" = .done) (hlen : s.length < 2147483648)
    (hk : ∀ σ', ResAtL σ' res ld ls lh disp (st ++ [sl s]) ht ab →
      KeepsRes res ld ls lh σ σ' → σ'.inits = σ.inits → σ'.statics = σ.statics →
      match I.lookup (pc + 1) with
      | some A => A fr σ'
      | none => bodyWP Gen.prog (callWP Gen.prog csCallees.env 1) body I Post n (pc + 1) fr σ') :
    bodyWP Gen.prog (callWP Gen.prog csCallees.env 1) body I Post (n + 1) pc fr σ := by
  rw [bodyWP_succ]
  simp only [step, hs, stepStmt, evalInvoke, evalArgs, evalImm, h22, hkx, Option.map_some, sel_stmt]
  have hcls : stmtRef.cls = "Cbstm03a" := rfl
  simp only [hcls, initThen, ensureInit, prog_cbstm, Bool.not_true, Bool.false_eq_true, ite_false,
    hini, Res.bind_ret, callM, Res.bind_call, wpR, callWP, env_stmt]
  refine ⟨⟨Or.inl sel_stmt, rfl⟩, ⟨res, ld, ls, lh, disp, st, ht, ab, _, rfl, hR,
    Or.inr ⟨x, s, rfl, hx, hlen⟩, hini⟩, ?_⟩
  intro o ho
  cases o with
  | normal r σ' =>
    simp only [stmtSpec, Spec.of] at ho
    obtain ⟨-, hR', hK', hi', hs'⟩ := ho res ld ls lh disp st ht ab _ rfl hR
    have harg : argText σ (.ref x) = s := by simp [argText, strOf, hx]
    rw [harg] at hR'
    simp only [outToEv, afterEv, afterStep]
    exact hk σ' hR' hK' hi' hs'
  | exc e σ' => simp only [stmtSpec, Spec.of] at ho
  | wrong m => simp only [stmtSpec, Spec.of] at ho

end EquivLean.Modernize.Cbstm03a.Java.Cs
