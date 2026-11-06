import EquivLean.Modernize.Cbtrn02c.Model

/-!
# CBTRN02C: the domain of the statement (written by hand)

coblean's `cbtrn02c_posts` covers the runs whose daily transactions have distinct ids
(`DALYTRAN-ID`, the key `FD-TRANS-ID` of the transaction file): with a repeated id, the WRITE of
the second valid transaction fails (`INVALID KEY`) and the program abends.  Until that path is
proved, the statement carries this domain.  It also bounds the number of daily transactions below
10^9, as `cbtrn02c_posts` does (`hlen`): the transaction and reject counters are PIC 9(9).  This is
the one part of the CBTRN02C statements that is not generated.
-/

open EquivLean.Cobol.Rec EquivLean.Modernize.Cbtrn02c.Model

namespace EquivLean.Modernize.Cbtrn02c

/-- The daily transactions have distinct ids, and there are fewer than 10^9 of them.  The arguments
are the daily transaction, cross-reference, account and category balance records. -/
def Domain (trans _xrefs _accts _cats : List (List FVal)) : Prop :=
  (trans.map tId).Nodup ∧ trans.length < 1000000000

end EquivLean.Modernize.Cbtrn02c
