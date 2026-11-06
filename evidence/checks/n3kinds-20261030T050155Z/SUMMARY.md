RESULT: At the frozen next3 pin 7c73739 (cirrun sha256 2995b7945381822e300cfccf98cc7a7802bb8612b0904d45ddbc3ddab6cf8101), K1, K2, K3, K4, K6, K7, K10, K12 and the member-level width defect are fixed, K5, K8, K9 and K11 are partly fixed, and K13 is UB, as at c17690c. Of the 73 probes, 50 give the native value, 19 report UB where C has UB, the 2 declared-only reads (K12) report UB instead of 0, the K11 probe t_self_ref_return still reports UB (native 1) because its class is the labelled gap g_elided_copy, and the control c_va_int_of_int gives the c17690c value; no probe gives another value than native or a defined result where C has UB (28 outcomes changed against c17690c). cirlean's own case files behave as labelled: the 7 that t1expo ran 182/182 (LIB=libstdcxx), 8 more for the kinds next3 changes 248/248 with LIB=libcxx (run.sh's default) and 240/248 with libstdcxx (the other 8 are by-value std::list/map/set/string/shared_ptr/vector-of-vector cases that report UB), and 7 sets holding labelled gaps 185/185. The shapes still open are labelled gaps: va_arg and printf-family calls through function pointers, non-literal printf formats (M9, F4), the long/long long and char erasure (M10/N3), stores to const parameters, const members (M15), C++ class objects, compound literals, const unions and const ints without initializer, const locals that outlive their scope (c_scope, a gap next3 introduces), and the NRVO-elided copy constructor (g_elided_copy). In the paper's list (sec-limits.tex l.59-82), next3 fixes the width and member-level sentences, pointer arithmetic, the whole-object store, union activation, the 64-bit access over two 32-bit members, the record copy through another type, memcpy with a null pointer and size 0, the by-value parameter and the declared-only global; it fixes va_arg, printf argument types and the const-local store outside the labelled gaps, and the by-value return except for g_elided_copy, the shape of the paper's own probe.
# Check by an agent: status of the cirlean C-semantics defect kinds at the frozen next3 pin 7c73739
Written 2026-10-30T05:31:53Z (date -u). Dir: this directory (n3kinds-20261030T050155Z, created by mkdir with a date -u stamp).
Inputs, read only (sha256 of each in cited_sha256.txt, 50 files): the frozen tree ~/cirlean_frozen/next3_7c73739_20261030
(worktree HEAD 7c73739c0cb655d07f4a452cc3317cafb2b1bcb4; its .lake/build/bin/cirrun has the brief's sha256, checked
again by every run script; nothing rebuilt; CHANGES_next3.md sha256 prefix d1e7e695e9f9049b, sections "Deviations of
earlier pins that next3 fixes", "Memory, pointers ...", "Objects and lifetimes", "Variadics and formatted I/O",
"Modelling choices and known gaps"; tests/difftest/run.sh and case files); t1expo's probe kit
~/fv_paper/evidence/checks/t1expo-20261029T172130Z/kinds (9 CIR files, results.tsv, own_*.out) and its SUMMARY.md
(sha256 prefix 2b3a6724606df558), section "Status of each kind at c17690c" for the kind definitions; the paper's list
~/fv_paper/paper_v2/sec-limits.tex (sha256 prefix 0c971964a94c88f3), paragraph "Defects of the C semantics" (l.59-82).
For the C status of each probe also the SUMMARY.md files of the original probe checks (coresnd, libsnd, byval,
extglob) and the probe sources ret.cpp and use.c.

Status terms. fixed: every probe of the kind gives the native value or reports UB where C has UB, and the kind's own
case files behave as labelled; reports of UB where C is defined may remain and are listed. partly fixed: the same for
the probes and most labelled shapes, but labelled gaps of the kind keep shapes in which the semantics still defines
what C leaves undefined or keeps the old mechanism. UB: the access is reported as undefined. These are test outcomes
at 7c73739. No theorem was re-checked here: no obligation was discharged at next3, no bound of a statement (the
executions it relates) was re-derived, and the proof status of every claim in the paper is unchanged by this check.

## Status of each kind at next3 7c73739
Evidence per kind: (i) the CHANGES_next3.md item, (ii) the code at 7c73739 (code_sites.txt; file:line under
~/cirlean_frozen/next3_7c73739_20261030), (iii) cirlean's own case files run with the tree's tests/difftest/run.sh
(own/own_SET.LIB.out; own_labels_*.tsv, own_summary_*.txt), (iv) t1expo's 73 probes (results_next3.tsv).
| kind | c17690c | next3 | evidence at next3 | labelled gaps under the kind |
|---|---|---|---|---|
| K1 pointer arithmetic/difference in element units | fixed | fixed | (i) "Pointer arithmetic in the pointer's units" and the strict subobject rule agreed with the evidence-owner session; (ii) Ctx.stride?/Ctx.diff? CIR/Semantics/Basic.lean l.2383, l.2396, used at Eval.lean l.1039-1040; (iv) the char/short strides and differences, heap strides and controls at k = 1 and 3 and the C maintainer session's two cases give the native values; c_char_over_struct now gives 1 and 3 (c17690c: UB "byte access not modelled"); c_int_over_struct is UB at k = 1 (type-punned access) and k = 3 (pointer arithmetic out of bounds), UB in C under the strict reading; c_wide_over_char UB (C: UB, 6.5p7); (iii) bytes 69/69 (52 MATCH + 17 UB). | g_heap_char_pool: structs in heap storage first cast to char * (UB where C is defined; a report of UB). Modelling choice: the strict subobject rule (c_int_over_struct). |
| K2 scalar store at the address of a whole aggregate | open | fixed | (i) G5, "a scalar access at an aggregate path descends to the initial element"; (iv) g5_byte_struct/array/nested/heap 305419783 and 305419784 = native (c17690c: 7 and 8), g5_byte_then_member 2 = native (c17690c: UB invalid memory read), g5_ll_struct UB type-punned access (c17690c: 6 and 7; C: UB); (iii) aggpath 34/34 with both header sets (byte, int and atomic stores through struct, array, union and row addresses MATCH; long long over two int members or elements UB). | none |
| K3 aggregate copy through another record type | open | fixed | (i) G4, "record access through another record type is UB unless the object starts with that type"; (iv) g4_copy_other UB type-punned access (c17690c: 2 and 3; C: UB); (iii) aggpath (copy through another struct type UB, through a pointer to an object that starts with the type MATCH) and aggclause 12/12 (the 6.5p7 aggregate clause member by member; G4 UB). | none |
| K4 strtol end pointer | fixed | fixed (unchanged) | (iv) g2_strtol_end_into_int UB type-punned access, control c_strtol_end_ok 59 and 60; (iii) modelstore 19/19 (the five ub_strto*_end_into_* UB, t_* MATCH). | none |
| K5 va_arg or scanf type mismatch | partly fixed | partly fixed (unchanged) | (ii) Eval.lean l.843, l.849; (iv) l_va_long_of_int and l_va_after_end UB, controls match; (iii) vastruct 15/15, vafmt 24/24, vprintf 23/23, sscanfi 64/64, auditva 17/17, modelstore's four ub_sscanf_* UB. | t_gap_va_fnptr (an int read as long through a function pointer gives 5: defined where C has UB), vprintf t_gap_vsprintf_fnptr (a long read by %d through a function pointer, not caught) and t_gap_callee_then_vsprintf (the owner's vsprintf after a callee's va_arg, 7.16p3, not caught), t_indirect_struct (a structure through a function pointer: UB where C is defined), sscanfi i_value and i_count (%i of 0b...: not modelled, UB); CHANGES gap M10/N3: CIR erases long/long long and char/signed char/char8_t, so va_arg and conversion checks cannot tell them apart. |
| K6 union member pointer kept and used later | open | fixed | (i) unionact3/4b/5b, unionfix3: the member last stored is the active one, whichever pointer the store went through; (ii) Ctx.unionOnPath Basic.lean l.1400; (iv) u1_stale 0 = native (c17690c 1000), u1_stale_ints 7 and 8 = native (c17690c 5); (iii) unionact 48/48 with both header sets (the U1 cases MATCH), unionbyte 6/6. | unionact u_const_array_other (an array member of a const union read through another array member: UB where C gives 1065353216; CHANGES gap list), unionbyte u_formed_before (a pointer formed while no member held a value stays a byte view: UB where C gives 5) and u_past_active (UB; C: unspecified). Trust-base choice: C++ modules read unions as C does (ISO C++ leaves it undefined; T2 0132, 0254, 0566 depend on it). |
| K7 bit-field read through a union member | open | fixed | (iv) u2_bits_after_float 133169152 = native (c17690c 0); (iii) the unionact U2 cases MATCH (a bit-field unit stored after a float or an unsigned member, also through an earlier pointer). | the C++ union choice of K6 |
| K8 library calls the models treat differently from C | partly fixed | partly fixed (unchanged) | (ii) Std/Models.lean l.1788, l.1805, l.1827 (mem* pointers also at length 0), fmtArgsBad l.820-842 (argument types of printf calls with a literal format, checked by the frontend); (iv) l_memcpy/memset/memcmp_null0, l_sprintf_fmt_overlap and l_sprintf_d_long UB, controls match; (iii) modelstore2 17/17, overlap 13/13, vafmt, vprintf, auditva. | M9: non-literal printf formats unchecked (auditva v_fnptr_sprintf: sprintf through a function pointer is not checked against its format [M9]); F4: auditva v_fmt_mutable_ub (a mutable format array changed to "%ld" with an int argument; only constant globals count as literal formats); M10/N3. |
| K9 store through const | open | partly fixed | (i) constobj2 + constobj3 option (c): const-qualified locals are read-only once initialized (6.7.3p6); (ii) Mem.write? Basic.lean l.249-256, l.1498, l.1560; (iv) l_const_local_store and l_const_local_store2 UB "modification of a const object (C11 6.7.3p6, 6.4.5p7)" (c17690c: 1 and 2; the first, which libsnd set aside because the front end folds its read, now exercises the rule, since the store itself is refused); (iii) constobj 44/44 (23 MATCH + 21 UB) with both header sets, constlife 14/14. | c_scope (introduced by next3: a const local no longer ends at its scope's exit, so a dangling read gives the stale 4, which next2 reported as UB; next3.1 item; intptr i_const_scope the same), c_gap_param (const parameters), c_gap_member and q_const_member_store (M15: CIR drops a member's const), c_gap_class (C++ class objects are not read-only), c_gap_noinit (a store into a const int without initializer is taken for its initialization), c_gap_compound_literal, c_gap_union, constlife c_reuse_const (a const local's storage reused by placement new after its destructor, [basic.life]p10). Each gives the native value where C has UB. |
| K10 by-value parameter of a non-trivial class | open | fixed | (i) byval: the callee uses the caller's temporary (one object, Itanium); other shapes are "a by-value argument of a class non-trivial for calls, not modelled" (Frontend/ByValue.lean l.131); (iv) t_move_from_param 0 = native (c17690c -1), controls match; (iii) byval 13/13 with libcxx; with libstdcxx the user RAII, unique_ptr, trivial and b_shared_leaked_count cases MATCH, while b_list and g_list_return (std::list by value) and b_shared_member_count report UB type-punned access and b_power (k = 0 and 3) reports UB "a return value of a class non-trivial for calls, not modelled" (own/full_*.out). | b_shared_member_scope and b_shared_local (the last owner's release: libc++'s __release_weak has no model; with libstdc++ type-punned access). The five libstdc++ runs named above carry labels written for libc++; each reports UB, none another value. |
| K11 record returned by value holding a pointer into itself | open | partly fixed | (i) retslot: the caller's destination is the result object (hidden result pointer, Itanium); other shapes are "a return value of a class non-trivial for calls, not modelled" (Frontend/RetSlot.lean l.33); (iii) retslot 15/15 with libcxx (self-pointing classes from a prvalue or a named result, chains, members, parameters, virtual calls, registered addresses, map, set and string MATCH; g_elided_copy UB as labelled); with libstdcxx 12/15 (r_map, r_set UB type-punned access; r_string UB "object is not a live std::vector / std::string"); (iv) t_self_ref_return still UB "invalid memory read" (native 1), as at c17690c: ret.cpp is the class of the labelled gap g_elided_copy (tests/difftest/retslot.cpp l.151-170 cites this probe). | g_elided_copy: a class whose only non-trivial member is a user copy constructor that NRVO elides, with no destructor, is not recognised (the CIR record carries nothing about it; the fix needs a ClangIR record attribute), so the result is still copied out of the callee's slot; the read through the dangling pointer is reported as UB, no other value. |
| K12 read of a global the unit only declares | open | fixed | (i) externglob2/3: reads and writes of a global the module only declares are UB unless modelled; (ii) Semantics/Init.lean l.3-30 (the block of such a global is external and not alive), Basic.lean l.1726, l.1743, l.1818, l.1842; (iv) t_ext_scalar UB "external object without a model", t_ext_array UB "element access into a non-array" (Eval.lean l.1033) (c17690c: 1 and 1, i.e. zeros), control t_defined 8; (iii) externglob 11/11 with both header sets (the modelled objects MATCH; environ, program_invocation_name and a field of std::cout UB). | none labelled. The trust base lists the modelled objects: stdin, stdout and stderr, the fundamental typeinfo objects, __libc_single_threaded = 1, optind = opterr = 1, signgam, and the C++ stream objects as live objects of indeterminate value. |
| K13 libstdc++'s 64-bit read of the two 32-bit shared_ptr counters | UB (since 424e821) | UB (unchanged) | (ii) Ctx.punnedMember Basic.lean l.609, typed loads and stores l.1715-1745; (iii) recpun 25/25: r_pun_ll_over_ints, r_pun_atomic_ll_over_ints ("libstdc++ shared_ptr _M_release"), the volatile, atomic-store and fetch_add variants UB; aggpath's long long over two int members UB; (iv) g5_ll_struct UB. With libstdc++, byval's b_shared_member_count (its local owner is destroyed with use count 2) reports UB type-punned access while b_shared_leaked_count (no owner destroyed) matches, consistent with the _M_release read (not traced). | none (UB by design) |
| width, member level | fixed | fixed (unchanged) | character accesses read and write the bytes of int, float, bool and record objects (byteOf Basic.lean l.933, l.1098-1107); other-width scalar accesses are UB (Ctx.punnedMember); (iv) c_byte_member 305419783 and 305419784 = native (t1expo's table gives this probe the kind K13; its SUMMARY uses it for this row); (iii) recpun r_pun_char_into_int and r_pun_char_into_nested MATCH, the other-width member cases UB; memb 71/71 and byterepr 15/15 with the byte cases MATCH. | byte-representation gaps, all reports of UB: memb u_uninit_partial, u_ptr_via_bytes, u_ptr_to_long, u_memset_nan, u_padding_byte (CHANGES: "padding bytes UB"), u_union_bytes; byterepr r_nan_double_read; M10/N3 (Ty.isChar is any 8-bit integer, Basic.lean l.627). |

## Probes (results_next3.tsv: t1expo's seven columns plus next3_7c73739, the C status and the outcome)
- 73/73 runs exit 0 (out/rc.tsv). Outcomes: 50 native value; 19 UB where C has UB (c_int_over_struct and
  c_wide_over_char at k = 1, 3; g5_ll_struct, g4_copy_other, g2_strtol_end_into_int at k = 1, 2; the five K8 cases;
  l_va_after_end, l_va_long_of_int; both K9 cases); 2 UB reports for the declared-only objects (K12); 1 UB where C++
  defines the result (t_self_ref_return, g_elided_copy); 1 control without a native value at k = 1 (c_va_int_of_int 5,
  as at c17690c and 424e821). None gives another value than native or a defined result where C has UB.
- Changed against c17690c: 28 outcomes (c_char_over_struct x2, the 8 g5_byte cases, g5_byte_then_member x2,
  g5_ll_struct x2, g4_copy_other x2, u1_stale and u1_stale_ints x4, u2_bits_after_float x2, both K9 cases,
  t_move_from_param, t_ext_scalar, t_ext_array, and c_int_over_struct at k = 3, whose report changes from a
  type-punned access to pointer arithmetic out of bounds).
- C status per case (scripts/cstatus.tsv): from the original checks' SUMMARY.md files (coresnd: g5_ll_struct, G4 and
  G2 undefined in C; libsnd: mem* with null and 0, sprintf overlap and %d with a long, va_arg after va_end or of
  another type, the const-local stores undefined) and from the bytes case labels for the evidence-owner session stride cases
  (d_int_over_struct UB under the strict reading, d_char_over_struct MATCH, d_wide_over_char UB).

## cirlean's own case files at next3 (run.sh of the frozen tree)
Required (the sets t1expo ran, LIB=libstdcxx as there): bytes 69/69 (52 MATCH + 17 UB), recpun 25/25 (16 + 9),
modelstore 19/19 (10 + 9), modelstore2 17/17 (6 + 11), vastruct 15/15 (9 + 6), vafmt 24/24 (8 + 16), overlap 13/13
(7 + 6): 182/182 as labelled. bytes has grown since c17690c (t1expo ran 38 cases: 30 MATCH + 8 UB); the other six
have t1expo's counts.
Extra, for the kinds next3 changes, with both header sets: aggpath 34, aggclause 12, unionact 48, constobj 44, byval
13, retslot 15, externglob 11, memb 71: 248/248 as labelled with LIB=libcxx; with LIB=libstdcxx 240/248, the 8 others
(labels written for libc++, all reports of UB, full messages in own/full_*.out): byval b_power 0 and 3 ("a return
value of a class non-trivial for calls, not modelled"), b_list, g_list_return, b_shared_member_count, retslot r_map,
r_set ("type-punned access (byte-level access not modelled)"), r_string ("object is not a live std::vector /
std::string").
Sets holding labelled gaps under the kinds (LIB=libstdcxx): unionbyte 6/6, vprintf 23/23, auditva 17/17, sscanfi
64/64, intptr 46/46 (i_dead_reuse labelled MISMATCH: addresses are never reused), constlife 14/14, byterepr 15/15:
185/185. Total 863 case runs, 855 as labelled. Every case labelled UB that ran with that status printed a "UB:" report.

## Labelled gaps of CHANGES_next3.md, by kind
(Modelling choices and known gaps, plus the limits named in the other sections; the case that carries each and its
outcome at next3 in brackets; inventory of all 62 gap-labelled case lines in gap_labels.tsv.)
- K1: none in the gap list; bytes.cpp's labelled gap g_heap_char_pool [UB, as labelled]; the strict subobject rule is
  a choice (Memory section).
- K5: CIR erases char/signed char/char8_t and long/long long (M10/N3) [no case]; the function-pointer and va_list
  ownership cases of vafmt, vastruct and vprintf and sscanfi's %i of 0b are case-file gaps [all as labelled].
- K6, K7: an array member of a const union read through another array member (UB) [unionact u_const_array_other, UB
  as labelled]; the C++ union reading in the trust base.
- K8: non-literal printf formats unchecked (M9) [auditva v_fnptr_sprintf MATCH as labelled; v_fmt_mutable_ub, F4,
  MATCH as labelled]; M10/N3.
- K9: const locals do not end at scope exit (c_scope) [constobj c_scope 4 = native stale value, MATCH as labelled;
  intptr i_const_scope the same]; const members of non-const structs [c_gap_member, q_const_member_store, MATCH as
  labelled]. Further case-file gaps under the Objects section's const-objects item, all MATCH as labelled: const
  parameters (c_gap_param), C++ class objects (c_gap_class), compound literals (c_gap_compound_literal), const unions
  (c_gap_union), a const int without initializer (c_gap_noinit), placement new into a destroyed const local's storage
  (constlife c_reuse_const).
- K10: none in the gap list (byval's two shared_ptr gaps are case-file gaps [UB as labelled]).
- K11: a class with only an NRVO-elided user copy constructor (retslot; g_elided_copy) [UB as labelled; the K11 probe].
- K12, K13, K2, K3, K4: none.
- width, member level: padding bytes UB [memb u_padding_byte, UB as labelled]; M10/N3.
- Under no kind: if (p) of a pointer whose object ended (intptr i_bool_dead_local), addresses never reused, the C rule
  for dead pointers in C++ modules, pointer exposure not tracked, libc++ vector<bool> bit iterators, front/back/flip,
  temporaries without a destructor after their full expression (L1/L2), __builtin_longjmp to a buffer a caller set,
  the array cookie of new T[n] with a non-trivial destructor, misaligned vector conversions never used.

## The paper's list (sec-limits.tex, paragraph "Defects of the C semantics", l.59-82) at next3
1. l.59-61, memory of typed elements: a load or store of another width reads or writes one element where C reads or
   writes bytes. Fixed: a character access reads and writes the bytes of the object (c_char_over_struct,
   c_byte_member, bytes, memb); a wider or other-type access is UB (c_wide_over_char, recpun, bytes u_short_read), as
   in C (6.5p7). No access keeps the one-element meaning. Gaps: the byte-representation gaps of the width row (reports
   of UB), g_heap_char_pool (UB), M10/N3.
2. l.61-64, record members keep the one-element meaning on the revised semantics; member-strict makes such reads UB.
   Fixed (as at c17690c): character accesses to members read bytes, other widths are UB (c_byte_member native, recpun).
3. l.67-70, pointer arithmetic by elements of the object reached. Fixed (K1); gap g_heap_char_pool (UB); the strict
   subobject rule makes (int *)s + 1 over records UB, as C does read strictly.
4. l.70-72, a scalar stored at the address of a whole record or array replaces the whole object. Fixed (K2).
5. l.72-73, a union member becomes active when a pointer to it is formed. Fixed (K6); gaps u_formed_before,
   u_past_active, u_const_array_other (reports of UB); C++ unions read as in C (trust base).
6. l.73-76, operations defined that C leaves undefined:
   (a) a 64-bit access through the address of a record of two 32-bit members: UB (K13 row; recpun, aggpath,
       g5_ll_struct). Fixed.
   (b) a copy of a record through a pointer to another record type: UB (K3). Fixed.
   (c) va_arg of another type than the argument's: UB on direct calls (l_va_long_of_int, vastruct). Fixed except the
       labelled gaps: calls through function pointers (t_gap_va_fnptr, t_gap_vsprintf_fnptr), va_list ownership
       (t_gap_callee_then_vsprintf), and the types CIR erases (M10/N3).
   (d) printf arguments of other types than their conversions: UB with literal formats (l_sprintf_d_long, vafmt,
       vprintf). Fixed except non-literal formats (M9), mutable format arrays (F4), calls through function pointers
       (v_fnptr_sprintf) and M10/N3.
   (e) memcpy with a null pointer and a size of zero: UB (K8 probes, modelstore2). Fixed.
   (f) a store to a const local: UB once the local is initialized (both K9 probes, constobj). Fixed except a const
       int without initializer (c_gap_noinit); other const objects stay writable (parameters, members (M15), C++ class
       objects, compound literals, unions), and next3 adds c_scope: a const local that outlives its scope.
7. l.77-80, by-value parameter: the callee gets a second, bitwise copy. Fixed (K10); case-file gaps
   b_shared_member_scope, b_shared_local (UB); with libstdc++ headers std::list and shared_ptr by-value cases report UB.
8. l.80-81, return by value: copied out of the callee's frame, so a pointer into itself dangles. Partly fixed (K11):
   classes the frontend recognises as non-trivial for calls are built in the caller's object; the class of the
   paper's probe (user copy constructor elided by NRVO, no destructor) is the labelled gap g_elided_copy, still copied
   out, and its dangling read is reported as UB, no other value; with libstdc++ headers map, set and string results
   report UB.
9. l.81-82, a global that a unit only declares reads as zeros. Fixed (K12): reads report UB.
10. l.82, "Our C and C++ results hold only for code without such accesses and operations": at next3 the shapes in
   which the semantics still defines what C leaves undefined are the labelled gaps of 6(c), 6(d), 6(f) and c_scope;
   every other item gives the native value or a report of UB.
Not in the paper's list: K4 (fixed since c17690c) and K7 (fixed at next3). Outside l.59-82: the shared_ptr 64-bit read
of l.86-91 is UB at next3 (K13), as at c17690c (the 12 T3 verdicts were not re-run here); the musl word paths of
l.95-98 are non-character accesses of another type, UB at next3 as on the revised semantics.

## Method
- Probes: scripts/probes_next3.sh copies the 9 CIR files with cp -L from t1expo's kinds/ (sha256sum -c against its
  kinds/inputs_sha256.txt: 9/9 OK, probes_check.txt), then runs each row of t1expo's results.tsv on the next3 cirrun
  with the same file, function and k, stdin /dev/null, timeout 120 s; the table keeps the first output line, tabs as
  spaces, 90 characters, as t1expo's script (full outputs out/NN_case_k.out). scripts/classify_v2.awk adds the C
  status (scripts/cstatus.tsv) and the outcome.
- Own case files: scripts/own_one.sh runs the frozen tree's tests/difftest/run.sh (read only) with DIFF_W =
  scratch/SET.LIB, TMPDIR inside it, DIFF_CORE 360-382, CASES = SET_cases.txt, LIB as named; scripts/labels_v2.awk
  pairs each case line with its output line and its label (the "# expect" comment above it, which covers the following
  case lines; for modelstore and modelstore2 the name prefixes ub_ and t_, as their headers say).
- Full messages: scripts/rerun_full.sh (cirrun on the CIR files run.sh built, for the 8 cases run.sh cut at 60
  characters). Gap inventory: scripts/scan_gaps.sh (gap_labels.tsv, m9_lines.txt). Code sites: scripts/scan_code.sh
  (code_sites.txt) and single-file reads of Init.lean l.1-30, Std/Models.lean l.815-842, Basic.lean l.596-640.
- Every script, scan, interpreter and cirrun or run.sh run went through pjobs_v3.py (CMDFILE N 450 150 2 LOG) with
  coreh_guard_v2 command lines (cmds_*.txt, logs/pjobs_*.log, guard/*.log), at most 8 jobs at once. Core-hours
  (coreh.txt): 78.2 core-s = 0.0217 core-h over 46 guarded jobs, each guard log ending "command exited" with live 0;
  the zz_ jobs (syntax checks of cited.sh and sums.sh, cited hashes, the tally, SHA256SUMS) are not included.

## Deviations and limits
- Bare-shell reads: some ls commands listed several directories at once, and one wc -c read two empty logs; all other
  bare reads were single-file reads.
- The 15 extra case-file sets (and their libcxx runs) go beyond the brief's step 2; they supply evidence (iii) for
  the kinds next3 changes and the labelled gaps. Their labels are written for run.sh's default LIB=libcxx; the
  required sets ran with LIB=libstdcxx as in t1expo.
- The 8 libstdcxx cases that do not behave as labelled were not traced; b_power's message is the retslot frontend's
  "not modelled", and b_shared_member_count's UB is consistent with the K13 read (inferred from the case shapes, not
  traced). They are reports of UB, not other values.
- Native values are copied from the original checks (t1expo's column), not re-run; c_va_int_of_int has no native
  value at k = 1. t_ext_array's report names the element access, not the declared-only rule; both K12 reads report UB.
- SUMMARY.md was written twice: the first version (05:29:50Z) said all seven required sets had grown since c17690c,
  where only bytes has; this version replaces it before any hash was taken.
- Superseded files, written but never run: scripts/labels.awk (v2 appends its summary), scripts/classify.awk (v2
  writes counts to a file, not /dev/stderr), scripts/coreh.sh with cmds_bashn7.txt and cmds_coreh.txt (v2 skips its
  own guard log). PROGRESS.md is this check's checkpoint file, kept here because no write may leave this directory.
- SHA256SUMS leaves out itself and the files its own job is still writing (guard/zz_sums.log, logs/pjobs_sums.log,
  logs/sums.out); logs/sums_check.txt (its sha256sum -c) is written after it.

## Files
SUMMARY.md; results_next3.tsv (73 rows; results_next3_raw.tsv before classification; classify_counts.txt);
own_labels_req.tsv, own_labels_extra.tsv, own_labels_gapsets.tsv and own_summary_*.txt (one row per case, one line
per set); own/own_SET.LIB.out (run.sh outputs), own/full_*.out; out/ (probe outputs, rc.tsv); probes/ (the 9 CIR
copies), probes_expected.sha256, probes_check.txt; scratch/ (run.sh builds: drivers, native binaries, CIR); gap_labels.tsv,
m9_lines.txt; code_sites.txt; cited_sha256.txt; coreh.txt; scripts/; cmds_*.txt; logs/; guard/; PROGRESS.md; SHA256SUMS.
