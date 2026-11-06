import EquivLean.Modernize.Cbstm03a.Java.Term2.OutH
import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03A → Java, termination: `writeTrans`

No loops: `trest.substring(16, 65)`, `fmtZ(amt)`, one concatenation, then `stmt` once, `star` three times and
`html` twelve times. Callee contracts `wtCallees`: `stmtSpecH`, `htmlSpecH` (this package), `starSpec`, `fmtZSpec`
(`CbANum.Iface1`). `writeTransSpecB`: `writeTransSpec` with `t.length ≤ 2^30` (the statement line
`tid + " " + … ` has `t.length + 64` characters, which `stmt`'s contract needs below `2^31`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space zpadStr zpadStr_length fixStr_length
  grows_split)

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

open EquivLean.Modernize.Cbstm03a.Java

theorem lead0_le : ∀ s : JStr, lead0 s ≤ s.length
  | [] => by simp [lead0]
  | c :: s => by
    have := lead0_le s
    unfold lead0; split <;> simp <;> omega

theorem signStr_length (v : Int) : (signStr v).length = 1 := by
  unfold signStr; split <;> rfl

theorem fmtZStr_length (v : Int) : (fmtZStr v).length = 13 := by
  unfold fmtZStr
  have h1 := lead0_le (zpadStr (v.natAbs / 100) 9)
  rw [zpadStr_length] at h1
  have h2 : (JStr.ofString ".").length = 1 := rfl
  simp only [List.length_append, List.length_replicate, List.length_drop, zpadStr_length, signStr_length, h2]
  omega

/-- `writeTrans` with the transaction id of at most `2^30` characters. -/
def writeTransSpecB : Spec where
  pre := fun args σ => ∃ (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (tv rv : Value) (amt : I64)
       (t tr : JStr),
     args = [.ref res, tv, rv, .long amt] ∧ ResAtL σ res ld ls lh disp st ht ab ∧ JStrAt σ tv t ∧
     JStrAt σ rv tr ∧ 65 ≤ tr.length ∧ tr.length < 2147483648 ∧ t.length ≤ 1073741824 ∧
     -9223372036854775808 < amt.toInt ∧ σ.initOf "Cbstm03a" = .done
  post := writeTransSpec.post

@[simp] theorem starStr_length (p f : JStr) : (starStr p f).length = 100 := fixStr_length _ _

/-- The callees of `writeTrans` (`stmt` and `html` inlined). -/
def wtCallees : Contracts := [(fixSig, fixSpecI), (fmtZSig, fmtZSpec), (starSig, starSpec)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 30000000 in
set_option jimple.modelContracts true in
theorem writeTrans_tvc : TermVC Gen.prog wtCallees.env (fun _ => 0) 1 1 writeTransRef writeTransSpecB [] 120 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, fun p hp => by simp at hp⟩⟩
  obtain ⟨res, ld, ls, lh, disp, st, ht, ab, tv, rv, amt, t, tr, h0, hR, ⟨xt, htv, hxt⟩, ⟨xr, hrv, hxr⟩, hl1, hl2,
    hl3, hamt, hI⟩ := hpre
  obtain ⟨fs, hres, gd, gs, gh, gab, n1, n2, n3, ⟨xd, md, hld, -⟩, ⟨xs, ms, hls, -⟩, ⟨xh, mh, hlh, -⟩⟩ := hR
  jvc [ite_nat_ne, wtCallees, fixSig, fmtZSig, starSig, fixSpecI, fmtZSpec, starSpec, grows_split, fmtZStr_length,
    starStr_length, StrNN, StrOk, argText, strOf]
  all_goals (try (simp only [List.length_append, List.length_cons, List.length_nil, fmtZStr_length, starStr_length,
    List.length_replicate, List.length_drop, List.length_take]; omega))

end EquivLean.Modernize.Cbstm03a.Java.Term2

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term2.writeTrans_tvc
