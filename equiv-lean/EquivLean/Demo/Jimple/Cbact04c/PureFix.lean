import EquivLean.Demo.Jimple.Cbact04c.Pure

/-!
# The loop's final state on CBACT04C's input, and the fixed port

After all records, the state is `S` of the accounts but the last, with the last account current and
its interest accumulated (`jRun_final`).  A port that posts the current account after the loop
therefore rewrites every account (`jRunFix_cbact04c`): exactly the account the COBOL program misses.
-/

open Cobol CardDemo.Cbact04c Jimple

namespace EquivLean.Demo.Cbact04c

theorem jRun_final (rate : Acc → Cat → Int) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (accs : List Acc) (hne : accs ≠ []) (hok : ∀ a ∈ accs, AccOk rate acctOf rateOf a)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) :
    jRun acctOf rateOf (jcats accs) =
      S rate accs.dropLast (accs.getLast hne) (accs.getLast hne).cats := by
  cases accs with
  | nil => exact absurd rfl hne
  | cons a rest =>
    have ha := hok a (List.mem_cons_self ..)
    obtain ⟨c0, cs, hcs⟩ : ∃ c0 cs, a.cats = c0 :: cs := by
      cases h : a.cats with
      | nil => exact absurd h ha.1.2.2.2.2.2.2.2.2.2.2.2.1
      | cons c0 cs => exact ⟨c0, cs, rfl⟩
    have hc0 := ha.2.2 c0 (by rw [hcs]; exact List.mem_cons_self ..)
    have hc0v : c0.valid := ha.1.2.2.2.2.2.2.2.2.2.2.2.2 c0 (by rw [hcs]; exact List.mem_cons_self ..)
    simp only [jRun]
    rw [jcats_cons, List.foldl_append, hcs, List.map_cons, List.foldl_cons, jStep_eq,
      chg_first rate acctOf a c0 ha.2.1, rate_step rate rateOf [] a [] c0 hc0v hc0.1 hc0.2,
      List.nil_append, fold_cats rate acctOf rateOf [] a cs [c0] (fun c hc =>
        ⟨ha.1.2.2.2.2.2.2.2.2.2.2.2.2 c (by rw [hcs]; exact List.mem_cons_of_mem _ hc),
         ha.2.2 c (by rw [hcs]; exact List.mem_cons_of_mem _ hc)⟩),
      show [c0] ++ cs = a.cats by rw [hcs]; rfl,
      fold_accounts rate acctOf rateOf rest [] a hok hdist, List.nil_append]

/-- **The fixed port** (post the current account after the loop) rewrites every account. -/
theorem jRunFix_cbact04c (rate : Acc → Cat → Int) (acctOf : I64 → JAcct)
    (rateOf : JStr → JStr → I32 → I64) (accs : List Acc) (hok : ∀ a ∈ accs, AccOk rate acctOf rateOf a)
    (hdist : accs.Pairwise (fun a b => a.id ≠ b.id)) :
    (let s := jRun acctOf rateOf (jcats accs)
     if s.first then s.rewrites else s.rewrites ++ [jPost s.acct s.total]) =
      accs.map (fun a => jposted a (totalInt (rate a) a.cats)) := by
  by_cases hne : accs = []
  · subst hne; simp [jRun, jcats, items, jInit]
  · rw [jRun_final rate acctOf rateOf accs hne hok hdist]
    have hl := hok _ (List.getLast_mem hne)
    simp only [S, Bool.false_eq_true, ↓reduceIte]
    have hpost : jPost (jacct (accs.getLast hne))
        (BitVec.ofInt 64 (totalInt (rate (accs.getLast hne)) (accs.getLast hne).cats)) =
        jposted (accs.getLast hne) (totalInt (rate (accs.getLast hne)) (accs.getLast hne).cats) := by
      simp only [jPost, jacct, jposted]
      rw [jpost_bal _ _ hl.1.2.2.2.1 (totalInt_bound _ _)]
    rw [hpost]
    conv => rhs; rw [← List.dropLast_concat_getLast hne]
    simp

end EquivLean.Demo.Cbact04c
