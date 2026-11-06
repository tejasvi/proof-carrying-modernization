import EquivLean.Modernize.Cbact04c.Model

/-!
# CBACT04C: the domain of the statement (written by hand)

coblean's `cbact04c_events` covers the runs in which every keyed READ succeeds. In those runs,
each category record has:
- its account;
- its card cross-reference, found by account id;
- the disclosure group record of the account's group with the record's type and category.

The INVALID KEY paths (an abend, or the `DEFAULT` group) are not in coblean's theorem yet. Until
they are, the statement carries this domain. The domain also requires fewer than 999999 category
records: the 6-digit transaction suffix wraps after that, and coblean's theorem assumes it does
not. This is the one part of the CBACT04C statements that is not generated.
-/

open EquivLean.Cobol.Rec EquivLean.Modernize.Cbact04c.Model

namespace EquivLean.Modernize.Cbact04c

/-- Every keyed READ of CBACT04C succeeds, and there are fewer than 999999 category records. The
arguments are the category, cross-reference, account and disclosure group records, then the
linkage record. -/
def Domain (tcat xrefs accts discs : List (List FVal)) (_link : List FVal) : Prop :=
  tcat.length < 999999 ∧
  ∀ t ∈ tcat, (∃ a ∈ accts, aId a = tAcct t) ∧ (∃ x ∈ xrefs, xAcct x = tAcct t) ∧
    ∃ d ∈ discs, dGrp d = aGrp (findAcct accts (tAcct t)) ∧ dType d = tType t ∧ dCat d = tCat t

end EquivLean.Modernize.Cbact04c
