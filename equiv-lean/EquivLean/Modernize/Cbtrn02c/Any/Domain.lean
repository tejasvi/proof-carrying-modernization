import EquivLean.Modernize.Cbtrn02c.Model

/-!
# CBTRN02C on any input: the domain of the statement (written by hand)

coblean's `cbtrn02c_any` covers every run with fewer than 10^9 daily transactions (the transaction
and reject counters are PIC 9(9)); repeated transaction ids are allowed: the WRITE of a transaction
whose id was already posted in this run fails (status 22) and the program abends.  This is the one
part of the statements that is not generated.
-/

open EquivLean.Cobol.Rec EquivLean.Modernize.Cbtrn02c.Model

namespace EquivLean.Modernize.Cbtrn02c.Any

/-- The domain of `cbtrn02c_any` on field values: fewer than 10^9 daily transactions.  The arguments
are the daily transaction, cross-reference, account and category balance records. -/
def Domain (trans _xrefs _accts _cats : List (List FVal)) : Prop :=
  trans.length < 1000000000

end EquivLean.Modernize.Cbtrn02c.Any
