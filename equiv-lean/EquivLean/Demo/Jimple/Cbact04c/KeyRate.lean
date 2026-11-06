import EquivLean.Demo.Jimple.Cbact04c.Pure

/-!
# The rates of `cbact04c_all` depend only on the disclosure key

Its hypothesis `hdisc` finds, for each category of each account, the disclosure-group record by
key (group, type, category) and reads the rate from it: equal keys give the same record, hence
the same rate.
-/

open Cobol CardDemo.Cbact04c Jimple

namespace EquivLean.Demo.Cbact04c

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
  -- equal records: strip the common key prefix, then compare the rate fields
  have hl : ∀ r, (encodeNum {} DIS_INT_RATE.fmt r).length = 6 := fun r => length_encodeNum _ _ _ (by decide)
  simp only [List.append_assoc, List.append_cancel_left_eq] at h2
  have he : encodeNum {} DIS_INT_RATE.fmt (rate a' c') = encodeNum {} DIS_INT_RATE.fmt (rate a c) :=
    List.append_inj_left h2 (by rw [hl, hl])
  have d1 := decodeNum_encodeNum {} DIS_INT_RATE.fmt (rate a c) (by decide) (by decide) ⟨h4, fun h => by simp at h⟩
  have d2 := decodeNum_encodeNum {} DIS_INT_RATE.fmt (rate a' c') (by decide) (by decide) ⟨h4', fun h => by simp at h⟩
  rw [he, d1] at d2
  exact Option.some.inj d2

end EquivLean.Demo.Cbact04c
