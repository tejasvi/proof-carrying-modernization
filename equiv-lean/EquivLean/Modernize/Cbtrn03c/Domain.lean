import EquivLean.Modernize.Cbtrn03c.Model

/-!
# CBTRN03C: the domain of the statement (written by hand)

coblean's `cbtrn03c_every` covers every transaction file of fewer than 10^7 records (empty included;
dates out of range end the report early, failed lookups abend, leading blank card numbers count as
the initial current card: all in the model) with a date parameter record.  The statement carries
this domain.  This is the one part of the CBTRN03C statements that is not generated.
-/

open EquivLean.Cobol.Rec EquivLean.Modernize.Cbtrn03c.Model

namespace EquivLean.Modernize.Cbtrn03c

/-- The domain of `cbtrn03c_every` on field values.  The arguments are the transaction,
cross-reference, transaction type, category and date parameter records (in `SELECT` order). -/
def Domain (trans _xrefs _types _catgs parms : List (List FVal)) : Prop :=
  trans.length < 10000000 ∧ parms ≠ []

end EquivLean.Modernize.Cbtrn03c
