# punning2: examples at the type-punning semantics

Commit 2d65713 makes a scalar load or store undefined when its type does not
match the element type that the block's type gives through array paths
(`Mem.punnedAccess`). Eight example specs left the block's type free. Under
the new semantics their claims are false as stated: for example, with
`ty = .array (.float .double) n` a `char` access is punned, so it is undefined.
No lemma can discharge `punnedAccess … = false` without knowing the element
type. CIR has no invariant tying a block's value to its type, so "the element
value fits" would not be sound.

Each narrowed spec therefore gains one hypothesis. It states the element type
that the C code assumes. Conclusions are unchanged. Each proof gains one
`obtain … rfl` line.

## Narrowings (hypothesis added)

| Theorem | Added hypothesis | Meaning |
|---|---|---|
| `Examples.TwoLoops.fill_after_count_spec` | `(hty : ∃ es tlen, ty = .array (.int es 32) tlen)` | the array written through `int *a` holds 32-bit integers |
| `Examples.Carray.sum_arr_spec` | `(hty : ∃ es tlen, ty = .array (.int es 32) tlen)` | the array read through `const int *a` holds 32-bit integers |
| `Examples.Carray.find_first_spec` | `(hty : ∃ es tlen, ty = .array (.int es 32) tlen)` | as above |
| `Examples.Tokens.fill_token_spec` | `(hty : ∃ r tlen, ty = .array (.record r) tlen)` | the token array holds records (structs) |
| `Examples.PtrLoop.str_len_spec` | `(hty : ∃ es tlen, ty = .array (.int es 8) tlen)` | the string is a `char` array (either signedness) |
| `Examples.PtrLoop.count_char_spec` | `(hty : ∃ es tlen, ty = .array (.int es 8) tlen)` | as above |
| `Examples.PtrLoop.has_char_spec` | `(hty : ∃ es tlen, ty = .array (.int es 8) tlen)` | as above |
| `Examples.PtrArgs.fill_buf_spec` | `(hty : ∃ es tlen, ty = .array (.int es 8) tlen)` | the buffer is a `char` array |
| `Examples.PtrArgs.skip_spaces_spec` | `(hty : ∃ es tlen, ty = .array (.int es 8) tlen)`, `(hpty : ∃ t, pty = .ptr t)` | the string is a `char` array; the caller's variable `p` has a pointer type |
| `Examples.PtrArgs.copy_nonspace_spec` | `(hts : ∃ es tlen, ts = .array (.int es 8) tlen)`, `(hto : ∃ es tlen, to = .array (.int es 8) tlen)` | source and destination are `char` arrays |
| `Examples.CJScan.string_scan_spec` | `(htyc : ∃ es tlen, tyc = .array (.int es 8) tlen)` | the parse buffer's content is a `char` array |
| `Examples.CJStrings.skip_whitespace_spec` | `(htyc : ∃ es tlen, tyc = .array (.int es 8) tlen)` | as above |
| `Examples.CJStrings.skip_whitespace_ub` | `(htyc : ∃ es tlen, tyc = .array (.int es 8) tlen)` | as above |
| `Examples.CJHex4.parse_hex4_ub` | `(hty : ∃ es tlen, ty = .array (.int es 8) tlen)` | the four hex digits lie in a `char` array |
| `Examples.CJHex4Tight.parse_hex4_spec` | `(hty : ∃ es tlen, ty = .array (.int es 8) tlen)` | as above |
| `Examples.CJParseString.parse_string_not_quote` | `(htyc : ∃ es tlen, tyc = .array (.int es 8) tlen)` | the parse buffer's content is a `char` array |
| `Examples.CJParseString.parse_string_unterminated` | `(htyc : ∃ es tlen, tyc = .array (.int es 8) tlen)` | as above |
| `Examples.CJParseString.parse_string_noub` | `(htyc : ∃ es tlen, tyc = .array (.int es 8) tlen)` | as above |
| `Examples.CJDelete.delete_spec` | premise `AllCJSON ts` (new definition in `Examples/CJDelete.lean`) | every item of the forest, children included, is a `cJSON` record (`rt = .record "cJSON"`) |
| `Examples.CJDelete.delete_forest` | `(hrec : AllCJSON ts)` | as above |

CJHex4, CJHex4Tight, CJParseString and CJDelete are not imported by
`Examples.lean`. They also failed at 2d65713, and are narrowed in the same way.
In CJDelete, the proof also splits on whether the item owns its two strings.
In each case it states the item's and the strings' blocks to be distinct as
plain disequalities, which the lookups after a `free` need.

## Re-proved without narrowing

- `Examples.CJAppend.build_array_spec`: the statement is unchanged. The loop
  invariant in the proof gains `∀ j (h : j < ts.length), ts[j].rt = .record "cJSON"`:
  every item the loop builds is a `cJSON` record. With it, the accesses to the
  items' members are known not to be punned.
- `Examples.CJStrings.skip_bom_off`, `skip_bom_short`, `skip_bom_main` and
  `skip_utf8_bom_spec` are unchanged. They make no typed access to the content
  buffer.
