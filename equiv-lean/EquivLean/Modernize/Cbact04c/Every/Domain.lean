import EquivLean.Modernize.Cbact04c.Model

/-!
# CBACT04C on every input: the domain of the statement (written by hand)

coblean's `cbact04c_every` covers every run whose category balance file lists each account's
records together (the file is the accounts' categories in turn, the accounts distinct: `items accs`
with `accs.Pairwise (·.id ≠ ·.id)`, as a file read in key order is) with fewer than 999999 records.
No lookup is assumed to succeed: a missing account or cross-reference record abends, a missing
disclosure group is retried with the group `DEFAULT` (CardDemo's own data takes that path), a
missing `DEFAULT` group abends.  This is the one part of the statements that is not generated.
-/

open EquivLean.Cobol.Rec EquivLean.Modernize.Cbact04c.Model

namespace EquivLean.Modernize.Cbact04c.Every

/-- The domain of `cbact04c_every` on field values: fewer than 999999 category records, each
account's records contiguous.  The arguments are the category balance, cross-reference, account and
disclosure group records (in `SELECT` order) and the linkage record. -/
def Domain (tcat _xrefs _accts _discs : List (List FVal)) (_link : List FVal) : Prop :=
  tcat.length < 999999 ∧
  ∀ i j k, i < j → j < k → k < tcat.length →
    tAcct (tcat.getD i []) = tAcct (tcat.getD k []) → tAcct (tcat.getD j []) = tAcct (tcat.getD i [])

end EquivLean.Modernize.Cbact04c.Every
