# recpun: type punning on record members

Since 2d65713 a scalar load or store is undefined ("type-punned access") when
its type does not match the element type that the block's type gives through
array elements (`Mem.punnedAccess`). Accesses to record members were not
checked: `Mem` has no record declarations, so `Ty.atPath` stops at a record,
and `*(char *)&s.i = 7` wrote one element while `*(long long *)&c.use` on
`struct { int use; int weak; }` read one member (the libstdc++ shared_ptr
counters pattern).

The loads and stores of `evalSimple` (load, store, copy, atomic
read-modify-write, bit-field storage units, catch parameters) now go through
`Ctx.typedLoad` / `Ctx.typedStore`, which also check record members: for a
path through a record, `Ctx.punnedMember` takes the type at the path from the
record declarations (`Ctx.typeAt`), with the same rule (`Ty.accessCompatible`:
same-width integers of either signedness, pointers to anything, the same float
kind); paths through array elements only stay `Mem.punnedAccess`'s, so
symbolic execution evaluates the array check once. A union
member is checked as a member; a union's reinterpretation of another member's
scalar (`.unionMember`, `unionInit`) is unchanged. `loadTy` / `storeTy`, and so
the library models, keep the array check only.

## Narrowings (hypothesis changed)

| Theorem | Old hypothesis | New hypothesis | Why |
|---|---|---|---|
| `Examples.Tokens.fill_token_spec` | `(hty : ∃ r tlen, ty = .array (.record r) tlen)` | `(hty : ∃ tlen, ty = .array (.record "tok") tlen)` | the stores to the four members of `toks[i]` are checked against the member types of the element's record; with the record name free, its declaration is unknown and the check cannot be discharged. The array holds the source's `struct tok`. |

Conclusions are unchanged; the proof's `obtain` line changes accordingly. The
other Examples and the eight CJ examples build unchanged: their records are
the module's, and the closed lookups reduce (`reduceCtxRecord`).
