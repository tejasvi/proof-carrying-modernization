# d0 check of the reported pointer-stride defect of cirlean (stamp 20261028T182920Z, written 2026-10-28T18:31:15Z by date -u)

Inputs: the C maintainer session's minimal cases (copied to probe/s_f7.c from ~/cirlean_work/scratch/stridecheck/s.c, read only) and an own
probe probe/d0_cases.c (sha8 557feb2e; 10 functions, each called with k = 1 and k = 3); native gcc -O0 runs; CIR emitted with
the toolchain's clang (upstream-4955d32b, -fclangir -emit-cir); cirrun of the 10 frozen builds in ~/cirlean_frozen
(266d1ed, 28e2380, 90b9c2f, c4ef58d, ffab71e, ilp32 e00113f, next d8afb97 dry, revised e6ac99a, next2int f107f53,
member-strict 424e821). Script scripts/probe.sh (ulimit -v 32 GiB, per-call timeouts). Results probe_results.tsv (sha8 4f0281af).

RESULT: the defect is CONFIRMED at all 10 builds. Pointer stride and pointer difference count elements of the object the
pointer reaches, not sizeof of the pointee type, when the two sizes differ.
- Wrong defined values: char stride 4k over an int array, cast back and read: k=1 gives element 4 (native element 1);
  short stride 2k: elements 2 and 6 (native 1 and 3); char pointer difference of &a[k] and &a[0]: 1 and 3 (native 4 and
  12); char stride over a malloc'd int array: 40 (native 10). The C maintainer session's two cases give 4 and 2 at every build (native 1, 1).
- False reports of undefined behaviour: char stride 4k with k=3 over int arrays (stack and heap) reports pointer
  arithmetic out of bounds (native 3 and 30); an int pointer over an array of two-int records reports a read of an
  indeterminate or ill-typed value (native defined); a char pointer over the records reports an invalid read or an
  out-of-bounds stride (native defined).
- Wider pointee over a char buffer (unsigned short over bytes): the six older builds return the element values 1 and 3
  (native 770 and 1798); d8afb97, e6ac99a, f107f53 and 424e821 report a type-punned access (the revised rule).
- Controls: same-size reinterpretation (unsigned over int), plain int stride and plain heap indexing match native at
  every build.
Consequence for the paper: C claims hold only for code whose pointer arithmetic uses the element size of the object it
reaches; reports of out-of-bounds arithmetic and of ill-typed reads can be artefacts of the defect. Exposure of the
claimed closures and of the reported findings: the C maintainer session's scan (requested), then our own check.

## Note (2026-10-28T21:38:06Z by date -u): reading of subobject bounds
The case c_int_over_struct (an int pointer over an array of two-int records, read at k = 1 and 3) is listed above among the false reports of undefined behaviour because the native run is defined. Under the strict reading that cirlean next3 adopts (the C maintainer session, 21:4xZ: (int*)s points to s[0].x, 6.7.2.1p15; x is an array of one, 6.5.6p7; reading past it is undefined, 6.5.6p8), that read is undefined in ISO C, so the report is not a false alarm under that reading. The char-pointer cases (c_char_over_struct, char strides and differences) stay defined under it. The paper uses only the char-stride examples.
