import EquivLean.Demo.XLang.Jsmn.ModelLemmas

/-!
# jsmn → model, C side: the errors of `parseString` are negative (the C tests `r < 0`)
-/

open EquivLean.Demo.XLang.Jsmn (St strScan parseString ERROR_INVAL ERROR_PART ERROR_NOMEM)

namespace EquivLean.Demo.XLang.Jsmn.C

theorem parseString_err_neg {js : List Nat} {n : Nat} {st : St} {e : Int} (h : parseString js n st = .error e) :
    e < 0 := by
  unfold parseString at h
  split at h
  · rename_i e' he
    injection h with h
    subst h
    rcases Jsmn.strScan_err he with h | h <;> (rw [h]; decide)
  · split at h
    · injection h with h; subst h; decide
    · injection h

end EquivLean.Demo.XLang.Jsmn.C
