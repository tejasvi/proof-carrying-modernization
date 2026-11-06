# d0 reproduction of the reported core-memory gaps of cirlean (stamp 20261028T183958Z, written 2026-10-28T18:41:50Z by date -u)

Inputs: the gap descriptions of ~/cirlean_work/scratch/soundaudit_core/FINDINGS.md (sha16 29898c7fd89cf9ed; the C maintainer session/rog,
73 cases at 424e821); own cases probe/d0s_cases.c (sha8 828f508c; 15 functions, k = 1 and 2; written from the
descriptions, not from the audit's test files); native gcc -O0; CIR from the toolchain clang (upstream-4955d32b);
cirrun of the 10 frozen builds (266d1ed, 28e2380, 90b9c2f, c4ef58d, ffab71e, ilp32 e00113f, d8afb97, e6ac99a, f107f53,
424e821). Script scripts/probe.sh (ulimit -v 32 GiB, timeouts). Results probe_results.tsv (sha8 f38428b8).

RESULT: CONFIRMED (gap by gap, with the builds where each shows):
- G5, all 10 builds: a byte store at the address of a whole record, array, nested record or heap record, followed by
  an int read at that address, gives 7 (8 for k=2); native 305419783 (305419784). A member read after such a store
  reports an invalid read (native 2). A 64-bit store and load over two ints is defined (C: undefined).
- Member-level contrast: a byte store at the first member then a read of it gives 7 at the first 8 builds (the
  one-element meaning) and a type-punned-access report at f107f53 and 424e821 (member-strict).
- G4, all 10 builds: an aggregate copy through another record type of the same layout is defined (C: undefined).
- G2, f107f53 and 424e821 (earlier builds stop at strtol as an external function): strtol's end pointer stored into
  an int member leaves the next member unchanged (2; native 24189, bits of the pointer; C: undefined).
- U1, 90b9c2f to 424e821: union member pointers formed before the stores; a read through the earlier-formed float
  pointer gives 1000 (native 0); the int/unsigned variant gives 5 (native 7). U2, same builds: a bit-field of a union
  member read after the float member was written gives 0 (native 133169152). At 266d1ed and 28e2380 every union write
  reports an invalid write (control c_union_expr too).
- Controls: plain struct members match at all builds; member access expressions on a union match from 90b9c2f;
  strtol with a char* end pointer matches at f107f53 and 424e821.

## Addendum (2026-10-28T18:44:29Z by date -u): three more versions named in the paper
scripts/probe_extra.sh ran the stride cases (checks/stride-20261028T182920Z/probe) and these core-gap cases (k = 1) on the
built interpreters of the replay copies of cirlean 88e6008 (vo-C), d9ae8e5 and ec40522 (vo-2); results
probe_results_extra.tsv (sha8 c37c687b), binaries hashed in SHA256SUMS.extra. All three behave like the six older frozen
builds: stride and difference defects, G5, G4, U1 and U2 as above, the member-level byte store with the one-element
meaning, strtol not modelled (G2 not applicable). Over the 13 versions: the stride defect, G5 and G4 at all 13; G2 at
f107f53 and 424e821; U1/U2 at all but 266d1ed and 28e2380, where every union store is reported as an invalid write.
