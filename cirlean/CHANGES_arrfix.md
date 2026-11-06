# arrfix: arrnew's conversions decided by the types first

The FH bundle print_array_step (e6ac99a) failed at next3 4a91e0c: arrnew's arm of `castVal`
(`.ptr (.loc b path), .ptr (.array _ 1), _`, and `.ptr (.array (.record _) 1)` in the version merged at
171082a) looked at the converted value before the types, so for a cast whose value is a symbolic pointer
(the `item->next` of `cJSON$ensure`) the VCG could not reduce `castVal` and split on whether the value is
a `.loc`, leaving a goal with the hypothesis `… = Val.ptr (Ptr.loc b path) → (Ty.record "cJSON").ptr =
(elem.array 1).ptr → False`. The arm now matches on the source type only (`_, .ptr (.array (.record _) 1),
_`) and leaves the value to a helper, `decayOne` (in the `cir_exec` simp set), so a cast from any other
source type reduces as before arrnew; `Ctx.convertPtr` likewise matches on the destination type before
the pointer (`match k, dst, x`). The rules themselves are arrnew's at 491f1cc: for arrays of records only,
so that a vector access over an array of scalars stays the access element by element (vecstore's
`u_load_uninit`, UB as labelled, which the earlier version of arrnew for every array made read 1).

## Narrowings

None.

## Test labels changed

None.
