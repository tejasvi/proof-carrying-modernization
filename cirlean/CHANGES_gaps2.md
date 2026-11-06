# gaps2: x86 SIMD intrinsics; `__builtin_setjmp` and `__builtin_longjmp`

The next static census gaps by the programs they block: the x86 intrinsics that CIR calls by name (3
programs) and GCC's non-local jump builtins (3).

- `cir.call_llvm_intrinsic` of `x86.sse2.packssdw.128`, `x86.sse2.pslli.w`, `x86.sse2.psrli.w`,
  `x86.sse.max.ps` and `x86.sse.movmsk.ps` (Regression/C/SSE packssdw-1, UnitTests/Vector/SSE sse.isamax
  and sse.shift) is `Op.x86Intrinsic`, a function of its operands that computes what the instruction does
  (`Std.x86Intrinsic`, `CIR/Std/X86.lean`; Intel SDM vol. 2): PACKSSDW packs the eight 32-bit elements of
  its operands into 16 bits with signed saturation; PSLLW and PSRLW shift each 16-bit element by the count,
  an unsigned 32-bit number, and give zeros for a count above 15; MAXPS gives each element of its first
  operand that is greater than the second's, else the second's (so for a NaN in either and for two zeros
  of any sign); MOVMSKPS gives the sign bits of the four elements. The sign of a NaN element is not modelled
  (`Float` has one NaN), so MOVMSKPS of a NaN is undefined. Any other intrinsic stays `Op.unknown`.
- `__builtin_setjmp` (`cir.eh.setjmp`) and `__builtin_longjmp` (`cir.eh.longjmp`, value 1 as GCC
  requires) (gcc-c-torture built-in-setjmp, pr64242, pr84521): the parser makes them calls of
  `__builtin_setjmp`, which `nestSetjmps` nests as it does `setjmp`, and `__builtin_longjmp`, declared by
  the frontend (`builtinJmpDecls`) with the models `setjmp` and `longjmp`. The invocation's token goes in
  the second word of the buffer, an array of pointers (as an integer address, `Ptr.addr`) or of `intptr_t`,
  where GCC keeps the resume address (`Std.jmpTokenAt`; a `jmp_buf` keeps it in its first `long` as
  before). CIR stores the frame address and the stack pointer in the first and third words before the
  `cir.eh.setjmp`; those six operations are dropped (`dropSetjmpWordOps`): the semantics needs neither, has
  no model of the frame address, and an `intptr_t` buffer could not hold the pointers. `cir.frame_address`
  elsewhere (`__builtin_frame_address`) stays unknown. GCC's manual rules out a `__builtin_longjmp` in the
  function that calls `__builtin_setjmp` ("it can only be called from a function called (directly or
  indirectly) from the function calling `__builtin_setjmp`"): in a function that calls both, each
  `__builtin_longjmp` is an `Op.fail`.

Pin census: 1179 of the 1812 programs without a static blocker, against 1173 at gaps1 (the six programs
above; none lost); the 193 dynamic mains as at gaps1 (172 run to their end, 17 UB, 4 timeouts).

## Narrowings

None.

## Test labels changed

None. New: `tests/difftest/gaps2.c` (`CASES=gaps2_cases.txt`, a C source, every case labelled: 13 MATCH, 4 UB:
a `__builtin_longjmp` in the function of its `__builtin_setjmp`, a buffer that holds no `__builtin_setjmp`,
and the gaps `g_movmsk_nan` and `g_frame_address`).
