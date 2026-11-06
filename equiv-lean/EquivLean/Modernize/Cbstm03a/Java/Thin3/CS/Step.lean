import EquivLean.Modernize.Cbstm03a.Java.Thin3.CS.Out

/-!
# CBSTM03A → Java, termination of `createStatement`: one call of `stmt`, `html` or `app`

The callee table `csT` (`stmt`/`html` on the heap, the rest from the frozen interfaces) and the handler `HT` of the
termination VC. `RJ res ls lh σS σ`: the `Result` object with its two lists (`ArrayList`s), the class initialized,
every string of `σS` kept. A call of `html`/`stmt` (argument a literal or a string local) or `app` (on a builder
of at most `cap` characters) keeps `RJ`: the paths from `pc` hold when those from `pc + 1` hold for every state
the contract allows (`jvc` cannot instantiate these postconditions: their premises are heap facts about the state
of the call, a fresh state after a literal or another call).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

open EquivLean.Modernize.Cbstm03a.Java

/-- The callee contracts of `createStatement` for its termination. -/
def csT : Contracts :=
  [(stmtSig, stmtSpecH), (htmlSig, htmlSpecH), (fixSig, fixSpecI), (spacesSig, spacesSpecI),
   (repeatSig, repeatSpec), (appSig, appSpec), (paraSig, paraSpec), (starSig, starSpec),
   (fmtCurrBalSig, fmtCurrBalSpec), (decodeZonedSig, decodeZonedSpec)]

abbrev csBody : Body := Gen.Cbstm03a.«createStatement(Cbstm03a$Result,java.lang.String,java.lang.String)»

/-- The handler of `createStatement`'s termination VC (rank 1, the callees at rank 0). -/
abbrev HT : Handler := callWPT Gen.prog csT.env 0

theorem csT_below : csT.env.below (fun _ => 0) 1 = csT.env := by
  funext sig; simp [SpecEnv.below]

theorem ne_of_heapCS {σ : State} {a b : Addr} {o1 o2 : Obj} (h1 : σ.heap a = some o1) (h2 : σ.heap b = some o2)
    (h : o1 ≠ o2) : a ≠ b := fun e => h (by rw [e] at h1; rw [h1] at h2; exact Option.some.inj h2)

theorem initOf_of_inits {σ σ' : State} (h : σ'.inits = σ.inits) (c : ClassName) : σ'.initOf c = σ.initOf c := by
  unfold State.initOf; rw [h]

/-- The `Result` object `res` with its statement list `ls` and HTML list `lh` (`ArrayList`s), the class
initialized, every string of `σS` kept. -/
def RJ (res ls lh : Addr) (σS σ : State) : Prop :=
  (∃ fs, σ.heap res = some (.plain resC fs) ∧ Fields.get fs (resC, "stmtFileWrites") = some (.ref ls) ∧
     Fields.get fs (resC, "htmlFileWrites") = some (.ref lh)) ∧
  (∃ xs m, σ.heap ls = some (.list .arrayList xs m)) ∧ (∃ xs m, σ.heap lh = some (.list .arrayList xs m)) ∧
  σ.initOf "Cbstm03a" = .done ∧ StrMono σS σ

theorem rj_alloc {res ls lh : Addr} {σS σ : State} (h : RJ res ls lh σS σ) (o : Obj) :
    RJ res ls lh σS (σ.alloc o).2 := by
  obtain ⟨⟨fs, h1, h2, h3⟩, ⟨xs, m, h4⟩, ⟨xs', m', h5⟩, h6, h7⟩ := h
  refine ⟨⟨fs, by rw [State.heap_alloc_of_lt (State.lt_next_of_heap h1)]; exact h1, h2, h3⟩,
    ⟨xs, m, by rw [State.heap_alloc_of_lt (State.lt_next_of_heap h4)]; exact h4⟩,
    ⟨xs', m', by rw [State.heap_alloc_of_lt (State.lt_next_of_heap h5)]; exact h5⟩,
    by rw [State.initOf_alloc]; exact h6, fun x s hx => ?_⟩
  have e := h7 x s hx
  rw [State.heap_alloc_of_lt (State.lt_next_of_heap e)]; exact e

theorem rj_grows {res ls lh : Addr} {σS σ σ' : State} (h : RJ res ls lh σS σ) (hg : Grows σ σ')
    (hi : σ'.inits = σ.inits) : RJ res ls lh σS σ' := by
  obtain ⟨⟨fs, h1, h2, h3⟩, ⟨xs, m, h4⟩, ⟨xs', m', h5⟩, h6, h7⟩ := h
  refine ⟨⟨fs, by rw [hg.2 _ (State.lt_next_of_heap h1)]; exact h1, h2, h3⟩,
    ⟨xs, m, by rw [hg.2 _ (State.lt_next_of_heap h4)]; exact h4⟩,
    ⟨xs', m', by rw [hg.2 _ (State.lt_next_of_heap h5)]; exact h5⟩,
    by rw [initOf_of_inits hi]; exact h6, fun x s hx => ?_⟩
  have e := h7 x s hx
  rw [hg.2 _ (State.lt_next_of_heap e)]; exact e

/-- After `html`: only the HTML list changed, and it is still an `ArrayList`. -/
theorem rj_html {res ls lh : Addr} {σS σ σ' : State} (h : RJ res ls lh σS σ) (hne : ls ≠ lh)
    (hk : Keeps (· = lh) σ σ') (hl : ∃ xs m, σ'.heap lh = some (.list .arrayList xs m))
    (hi : σ'.inits = σ.inits) : RJ res ls lh σS σ' := by
  obtain ⟨⟨fs, h1, h2, h3⟩, ⟨xs, m, h4⟩, ⟨xs', m', h5⟩, h6, h7⟩ := h
  have hrl : res ≠ lh := ne_of_heapCS h1 h5 (by simp)
  refine ⟨⟨fs, by rw [hk.2 _ (State.lt_next_of_heap h1) hrl]; exact h1, h2, h3⟩,
    ⟨xs, m, by rw [hk.2 _ (State.lt_next_of_heap h4) hne]; exact h4⟩, hl,
    by rw [initOf_of_inits hi]; exact h6, fun x s hx => ?_⟩
  have e := h7 x s hx
  rw [hk.2 _ (State.lt_next_of_heap e) (ne_of_heapCS e h5 (by simp))]; exact e

/-- After `stmt`: only the statement list changed, and it is still an `ArrayList`. -/
theorem rj_stmt {res ls lh : Addr} {σS σ σ' : State} (h : RJ res ls lh σS σ) (hne : ls ≠ lh)
    (hk : Keeps (· = ls) σ σ') (hl : ∃ xs m, σ'.heap ls = some (.list .arrayList xs m))
    (hi : σ'.inits = σ.inits) : RJ res ls lh σS σ' := by
  obtain ⟨⟨fs, h1, h2, h3⟩, ⟨xs, m, h4⟩, ⟨xs', m', h5⟩, h6, h7⟩ := h
  have hrl : res ≠ ls := ne_of_heapCS h1 h4 (by simp)
  refine ⟨⟨fs, by rw [hk.2 _ (State.lt_next_of_heap h1) hrl]; exact h1, h2, h3⟩, hl,
    ⟨xs', m', by rw [hk.2 _ (State.lt_next_of_heap h5) (Ne.symm hne)]; exact h5⟩,
    by rw [initOf_of_inits hi]; exact h6, fun x s hx => ?_⟩
  have e := h7 x s hx
  rw [hk.2 _ (State.lt_next_of_heap e) (ne_of_heapCS e h4 (by simp))]; exact e

/-- After `app` on the builder `d`: only the builder changed. -/
theorem rj_bld {res ls lh d : Addr} {σS σ σ' : State} {c : ClassName} {b : JStr} (h : RJ res ls lh σS σ)
    (hd : σ.heap d = some (.builder c b)) (hk : Keeps (fun y => y = d) σ σ') (hi : σ'.inits = σ.inits) :
    RJ res ls lh σS σ' := by
  obtain ⟨⟨fs, h1, h2, h3⟩, ⟨xs, m, h4⟩, ⟨xs', m', h5⟩, h6, h7⟩ := h
  refine ⟨⟨fs, by rw [hk.2 _ (State.lt_next_of_heap h1) (ne_of_heapCS h1 hd (by simp))]; exact h1, h2, h3⟩,
    ⟨xs, m, by rw [hk.2 _ (State.lt_next_of_heap h4) (ne_of_heapCS h4 hd (by simp))]; exact h4⟩,
    ⟨xs', m', by rw [hk.2 _ (State.lt_next_of_heap h5) (ne_of_heapCS h5 hd (by simp))]; exact h5⟩,
    by rw [initOf_of_inits hi]; exact h6, fun x s hx => ?_⟩
  have e := h7 x s hx
  rw [hk.2 _ (State.lt_next_of_heap e) (ne_of_heapCS e hd (by simp))]; exact e

/-! ## The calls -/

theorem sel_html : Gen.prog.selectStatic htmlSig = .jimple htmlRef := by rfl
theorem sel_stmt : Gen.prog.selectStatic stmtSig = .jimple stmtRef := by rfl
theorem sel_app : Gen.prog.selectStatic appSig = .jimple appRef := by rfl
theorem envT_html : csT.env htmlSig = some htmlSpecH := by rfl
theorem envT_stmt : csT.env stmtSig = some stmtSpecH := by rfl
theorem envT_app : csT.env appSig = some appSpec := by rfl
theorem prog_cbstm : Gen.prog.isProgClass "Cbstm03a" = true := by rfl

set_option maxHeartbeats 1000000 in
/-- `html(res, "lit")`. -/
theorem wpT_html_lit {n pc : Nat} {fr : Frame} {σS σ : State} {lit : String} {res ls lh : Addr}
    (hs : csBody.stmtAt pc = some (.invoke (.static htmlSig [.loc 22, .const (.str lit)])))
    (h22 : fr.get 22 = some (.ref res)) (hne : ls ≠ lh) (hlen : (JStr.ofString lit).length < 2147483648)
    (hJ : RJ res ls lh σS σ)
    (hk : ∀ σ', RJ res ls lh σS σ' → bodyWP Gen.prog HT csBody [] (fun _ => True) n (pc + 1) fr σ') :
    bodyWP Gen.prog HT csBody [] (fun _ => True) (n + 1) pc fr σ := by
  have hJ1 := rj_alloc hJ (.str (JStr.ofString lit))
  -- (witnesses by `choose`: `obtain`/`Exists.elim` on this goal unfold `bodyWP` at `n + 1` by `whnf`)
  have h1 := hJ1.1.choose_spec.1
  have h3 := hJ1.1.choose_spec.2.2
  have h5 := hJ1.2.2.1.choose_spec.choose_spec
  have h6 := hJ1.2.2.2.1
  rw [bodyWP_succ]
  simp only [step, hs, stepStmt, evalInvoke, evalArgs, evalImm, h22, Option.map_some, evalConst, allocStr,
    sel_html]
  have hcls : htmlRef.cls = "Cbstm03a" := rfl
  simp only [hcls, initThen, ensureInit, prog_cbstm, Bool.not_true, Bool.false_eq_true, ite_false, h6,
    Res.bind_ret, callM, Res.bind_call, wpR, callWPT, envT_html, State.alloc_fst]
  refine ⟨⟨Or.inl sel_html, rfl⟩, ⟨res, lh, _, _, _, _, rfl, h1, h3, h5,
    Or.inr ⟨σ.next, _, rfl, by simp [State.heap_alloc], hlen⟩, h6⟩, ?_⟩
  intro o ho
  cases o with
  | normal r σ' =>
    simp only [htmlSpecH, Spec.of] at ho
    obtain ⟨-, hK', hl', hi', -⟩ := ho res lh _ _ rfl h1 h3
    simp only [Res.bind_ret, wpR, outToEv, afterEv, afterStep, List.lookup]
    exact hk σ' (rj_html (rj_alloc hJ _) hne hK' hl' hi')
  | exc e σ' => simp only [htmlSpecH, Spec.of] at ho
  | wrong m => simp only [htmlSpecH, Spec.of] at ho

set_option maxHeartbeats 1000000 in
/-- `html(res, s)` with `s` a string local. -/
theorem wpT_html_loc {n pc k : Nat} {fr : Frame} {σS σ : State} {res ls lh x : Addr} {s : JStr}
    (hs : csBody.stmtAt pc = some (.invoke (.static htmlSig [.loc 22, .loc k])))
    (h22 : fr.get 22 = some (.ref res)) (hkx : fr.get k = some (.ref x)) (hne : ls ≠ lh)
    (hx : σ.heap x = some (.str s)) (hlen : s.length < 2147483648) (hJ : RJ res ls lh σS σ)
    (hk : ∀ σ', RJ res ls lh σS σ' → bodyWP Gen.prog HT csBody [] (fun _ => True) n (pc + 1) fr σ') :
    bodyWP Gen.prog HT csBody [] (fun _ => True) (n + 1) pc fr σ := by
  have h1 := hJ.1.choose_spec.1
  have h3 := hJ.1.choose_spec.2.2
  have h5 := hJ.2.2.1.choose_spec.choose_spec
  have h6 := hJ.2.2.2.1
  rw [bodyWP_succ]
  simp only [step, hs, stepStmt, evalInvoke, evalArgs, evalImm, h22, hkx, Option.map_some, sel_html]
  have hcls : htmlRef.cls = "Cbstm03a" := rfl
  simp only [hcls, initThen, ensureInit, prog_cbstm, Bool.not_true, Bool.false_eq_true, ite_false, h6,
    Res.bind_ret, callM, Res.bind_call, wpR, callWPT, envT_html]
  refine ⟨⟨Or.inl sel_html, rfl⟩, ⟨res, lh, _, _, _, _, rfl, h1, h3, h5, Or.inr ⟨x, s, rfl, hx, hlen⟩, h6⟩, ?_⟩
  intro o ho
  cases o with
  | normal r σ' =>
    simp only [htmlSpecH, Spec.of] at ho
    obtain ⟨-, hK', hl', hi', -⟩ := ho res lh _ _ rfl h1 h3
    simp only [Res.bind_ret, wpR, outToEv, afterEv, afterStep, List.lookup]
    exact hk σ' (rj_html hJ hne hK' hl' hi')
  | exc e σ' => simp only [htmlSpecH, Spec.of] at ho
  | wrong m => simp only [htmlSpecH, Spec.of] at ho

set_option maxHeartbeats 1000000 in
/-- `stmt(res, s)` with `s` a string local. -/
theorem wpT_stmt_loc {n pc k : Nat} {fr : Frame} {σS σ : State} {res ls lh x : Addr} {s : JStr}
    (hs : csBody.stmtAt pc = some (.invoke (.static stmtSig [.loc 22, .loc k])))
    (h22 : fr.get 22 = some (.ref res)) (hkx : fr.get k = some (.ref x)) (hne : ls ≠ lh)
    (hx : σ.heap x = some (.str s)) (hlen : s.length < 2147483648) (hJ : RJ res ls lh σS σ)
    (hk : ∀ σ', RJ res ls lh σS σ' → bodyWP Gen.prog HT csBody [] (fun _ => True) n (pc + 1) fr σ') :
    bodyWP Gen.prog HT csBody [] (fun _ => True) (n + 1) pc fr σ := by
  have h1 := hJ.1.choose_spec.1
  have h2 := hJ.1.choose_spec.2.1
  have h4 := hJ.2.1.choose_spec.choose_spec
  have h6 := hJ.2.2.2.1
  rw [bodyWP_succ]
  simp only [step, hs, stepStmt, evalInvoke, evalArgs, evalImm, h22, hkx, Option.map_some, sel_stmt]
  have hcls : stmtRef.cls = "Cbstm03a" := rfl
  simp only [hcls, initThen, ensureInit, prog_cbstm, Bool.not_true, Bool.false_eq_true, ite_false, h6,
    Res.bind_ret, callM, Res.bind_call, wpR, callWPT, envT_stmt]
  refine ⟨⟨Or.inl sel_stmt, rfl⟩, ⟨res, ls, _, _, _, _, rfl, h1, h2, h4, Or.inr ⟨x, s, rfl, hx, hlen⟩, h6⟩, ?_⟩
  intro o ho
  cases o with
  | normal r σ' =>
    simp only [stmtSpecH, Spec.of] at ho
    obtain ⟨-, hK', hl', hi', -⟩ := ho res ls _ _ rfl h1 h2
    simp only [Res.bind_ret, wpR, outToEv, afterEv, afterStep, List.lookup]
    exact hk σ' (rj_stmt hJ hne hK' hl' hi')
  | exc e σ' => simp only [stmtSpecH, Spec.of] at ho
  | wrong m => simp only [stmtSpecH, Spec.of] at ho

theorem appStr_length_le (b : JStr) (cap : Int) (src : JStr) (d : Option JStr) (hb : b.length ≤ cap.toNat) :
    (appStr b cap src d).length ≤ cap.toNat := by
  unfold appStr
  split
  · exact hb
  · simp only [List.length_append, List.length_take]; omega

set_option maxHeartbeats 1000000 in
/-- `app(d, cap, s, "lit")` with `s` a string local. -/
theorem wpT_app_loc_lit {n pc kd ks : Nat} {fr : Frame} {σS σ : State} {lit : String} {res ls lh d x : Addr}
    {cap : Int} {b s : JStr}
    (hs : csBody.stmtAt pc = some (.invoke (.static appSig [.loc kd, .const (.int cap), .loc ks, .const (.str lit)])))
    (hd : fr.get kd = some (.ref d)) (hkx : fr.get ks = some (.ref x)) (hJ : RJ res ls lh σS σ)
    (hb : σ.heap d = some (.builder "java.lang.StringBuilder" b))
    (hc0 : 0 ≤ (BitVec.ofInt 32 cap).toInt) (hbl : b.length ≤ (BitVec.ofInt 32 cap).toInt.toNat)
    (hx : σ.heap x = some (.str s)) (hsl : s.length < 2147483648)
    (hlen : (JStr.ofString lit).length < 2147483648)
    (hk : ∀ σ' b', RJ res ls lh σS σ' → σ'.heap d = some (.builder "java.lang.StringBuilder" b') →
      b'.length ≤ (BitVec.ofInt 32 cap).toInt.toNat →
      bodyWP Gen.prog HT csBody [] (fun _ => True) n (pc + 1) fr σ') :
    bodyWP Gen.prog HT csBody [] (fun _ => True) (n + 1) pc fr σ := by
  have h6 := hJ.2.2.2.1
  have hb1 : (σ.alloc (.str (JStr.ofString lit))).2.heap d = some (.builder "java.lang.StringBuilder" b) := by
    rw [State.heap_alloc_of_lt (State.lt_next_of_heap hb)]; exact hb
  have hx1 : (σ.alloc (.str (JStr.ofString lit))).2.heap x = some (.str s) := by
    rw [State.heap_alloc_of_lt (State.lt_next_of_heap hx)]; exact hx
  have hcl : (BitVec.ofInt 32 cap).toInt < 2147483648 := by
    have := BitVec.toInt_lt (x := BitVec.ofInt 32 cap); simpa using this
  rw [bodyWP_succ]
  simp only [step, hs, stepStmt, evalInvoke, evalArgs, evalImm, hd, hkx, Option.map_some, evalConst, allocStr,
    sel_app]
  have hcls : appRef.cls = "Cbstm03a" := rfl
  simp only [hcls, initThen, ensureInit, prog_cbstm, Bool.not_true, Bool.false_eq_true, ite_false,
    State.initOf_alloc, h6, Res.bind_ret, callM, Res.bind_call, wpR, callWPT, envT_app, State.alloc_fst]
  refine ⟨⟨Or.inl sel_app, rfl⟩, ⟨d, _, _, _, b, rfl, hb1, by omega, hc0, ⟨x, s, rfl, hx1, hsl⟩,
    Or.inr ⟨σ.next, _, rfl, by simp [State.heap_alloc], hlen⟩⟩, ?_⟩
  intro o ho
  cases o with
  | normal r σ' =>
    simp only [appSpec, Spec.of] at ho
    obtain ⟨-, hd', hK', hi', -⟩ := ho d _ _ _ b rfl hb1
    simp only [Res.bind_ret, wpR, outToEv, afterEv, afterStep, List.lookup]
    exact hk σ' _ (rj_bld (rj_alloc hJ _) hb1 hK' hi') hd' (appStr_length_le _ _ _ _ hbl)
  | exc e σ' => simp only [appSpec, Spec.of] at ho
  | wrong m => simp only [appSpec, Spec.of] at ho

set_option maxHeartbeats 1000000 in
/-- `app(d, cap, "lit", null)`. -/
theorem wpT_app_lit_null {n pc kd : Nat} {fr : Frame} {σS σ : State} {lit : String} {res ls lh d : Addr}
    {cap : Int} {b : JStr}
    (hs : csBody.stmtAt pc = some (.invoke (.static appSig [.loc kd, .const (.int cap), .const (.str lit),
      .const .null])))
    (hd : fr.get kd = some (.ref d)) (hJ : RJ res ls lh σS σ)
    (hb : σ.heap d = some (.builder "java.lang.StringBuilder" b))
    (hc0 : 0 ≤ (BitVec.ofInt 32 cap).toInt) (hbl : b.length ≤ (BitVec.ofInt 32 cap).toInt.toNat)
    (hlen : (JStr.ofString lit).length < 2147483648)
    (hk : ∀ σ' b', RJ res ls lh σS σ' → σ'.heap d = some (.builder "java.lang.StringBuilder" b') →
      b'.length ≤ (BitVec.ofInt 32 cap).toInt.toNat →
      bodyWP Gen.prog HT csBody [] (fun _ => True) n (pc + 1) fr σ') :
    bodyWP Gen.prog HT csBody [] (fun _ => True) (n + 1) pc fr σ := by
  have h6 := hJ.2.2.2.1
  have hb1 : (σ.alloc (.str (JStr.ofString lit))).2.heap d = some (.builder "java.lang.StringBuilder" b) := by
    rw [State.heap_alloc_of_lt (State.lt_next_of_heap hb)]; exact hb
  have hcl : (BitVec.ofInt 32 cap).toInt < 2147483648 := by
    have := BitVec.toInt_lt (x := BitVec.ofInt 32 cap); simpa using this
  rw [bodyWP_succ]
  simp only [step, hs, stepStmt, evalInvoke, evalArgs, evalImm, hd, Option.map_some, evalConst, allocStr,
    sel_app]
  have hcls : appRef.cls = "Cbstm03a" := rfl
  simp only [hcls, initThen, ensureInit, prog_cbstm, Bool.not_true, Bool.false_eq_true, ite_false,
    State.initOf_alloc, h6, Res.bind_ret, callM, Res.bind_call, wpR, callWPT, envT_app, State.alloc_fst]
  refine ⟨⟨Or.inl sel_app, rfl⟩, ⟨d, _, _, _, b, rfl, hb1, by omega, hc0,
    ⟨σ.next, _, rfl, by simp [State.heap_alloc], hlen⟩, Or.inl rfl⟩, ?_⟩
  intro o ho
  cases o with
  | normal r σ' =>
    simp only [appSpec, Spec.of] at ho
    obtain ⟨-, hd', hK', hi', -⟩ := ho d _ _ _ b rfl hb1
    simp only [Res.bind_ret, wpR, outToEv, afterEv, afterStep, List.lookup]
    exact hk σ' _ (rj_bld (rj_alloc hJ _) hb1 hK' hi') hd' (appStr_length_le _ _ _ _ hbl)
  | exc e σ' => simp only [appSpec, Spec.of] at ho
  | wrong m => simp only [appSpec, Spec.of] at ho

end EquivLean.Modernize.Cbstm03a.Java.Thin3
