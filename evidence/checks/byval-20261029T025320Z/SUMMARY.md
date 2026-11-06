RESULT: CONFIRMED. A user-written RAII class passed by value and moved from in the callee gives -1 on cirrun at all six
builds run (266d1ed, 28e2380, c4ef58d, ffab71e, e6ac99a, 424e821), where native C++ gives 0: the callee works on a
bitwise second object, and the caller's temporary still owns the resource and releases it again. A parameter the callee
leaves untouched gives 0 at every build (the callee's copy is not destroyed), and a trivially copyable record passed by
value matches native (41).
# d0 check of the C maintainer session's by-value report (written 2026-10-29T02:53:37Z by date -u); probe/bv.cpp (no library headers), scripts/probe.sh,
# results.txt; native g++ -O0; CIR from the toolchain clang++ (-fclangir); frozen cirrun builds.

## Addendum (2026-10-29T04:59:01Z by date -u): return by value
probe/ret.cpp (no library headers): a class whose pointer member points into its own buffer, returned by value, then read
through that pointer: native 1; cirrun stops with "invalid memory read" at 28e2380, ffab71e, e6ac99a and 424e821 (the
returned object still points into the callee's ended buffer). A trivially copyable record returned by value matches native
(12). results_ret.txt.
