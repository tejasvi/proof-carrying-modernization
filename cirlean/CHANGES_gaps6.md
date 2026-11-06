# gaps6: `main(int)`; `__builtin_setjmp`'s five-word buffer; the builtins' limits labelled

- `main(int)` receives `argc` = 1 (lead's GO, 10-29): C11 5.1.2.2.1p1 allows implementation-defined forms of
  `main`, and GCC and glibc pass it `argc`. `cirrun FILE main`, for a `main` with parameters run without
  arguments, now passes those of the runner's harness (`mainArgs` in `CirRun.lean`): `argc` = 1 for
  `main(int)`, and `argc` = 1 with `argv` = `{"prog", NULL}` (a modifiable string, p2) for
  `main(int, char **)`, which needed explicit arguments before. The census agrees: `pin_census_v2.sh`
  (census_driver_v4, census_summarize_v2) takes `main(int)` as an entry through the harness, calling `main(1)`
  as it calls `main(1, {"prog", NULL})` for `main(argc, argv)`; UnitTests TestLoop is the one census program
  with `main(int)`. README, trust base: the arguments `main` receives, beside the empty standard input.
- `__builtin_setjmp`'s buffer must hold GCC's five words from the pointer (`intptr_t buf[5]`; LLVM documents
  the same for `llvm.eh.sjlj.setjmp`, and CIR's code for the builtin stores words 0 and 2, which
  `dropSetjmpWordOps` removes): a shorter buffer is undefined ("setjmp: invalid jmp_buf", `Std.jmpTokenAt`,
  whose signature is unchanged), and only arrays of pointers or of 64-bit integers are such buffers (a `char`
  or `int` array is not modelled). From lookup's review (10-29).
- Labelled, not changed (lookup's review): GCC forbids a `__builtin_longjmp` only to the buffer that the same
  function's `__builtin_setjmp` set; the parser's rule (`Op.fail` for every `__builtin_longjmp` in a function
  that calls `__builtin_setjmp`) also reports a re-raise to a caller's buffer as undefined, which GCC allows:
  not modelled (README, the parser's note, its message). The precise rule needs the activation that set the
  buffer, an Eval-side check (lookup offered to write it, after the pin). Also labelled: the builtins and the
  library functions are not interchangeable (GCC's manual), but a token records no pair, so `longjmp` to a
  buffer of `__builtin_setjmp`, or the reverse, jumps.
- README: adding a model (`Std.runModel`'s `match` is at the heartbeat limit of `WF_runModel`; new models go
  into `LibOp` or a helper of their own with a well-formedness lemma and a head-checked rule).

Pin census (`pin_census_v2.sh`): 1188 of the 1812 programs without a static blocker, against 1187 at gaps5
(UnitTests TestLoop, through the harness; none lost); the 193 dynamic mains as at gaps5 (172 run to their end,
17 UB, 4 timeouts).

## Narrowings

`__builtin_setjmp` with a buffer of fewer than five pointer or 64-bit words, or of another element type,
is undefined (it ran before as if the buffer were large enough).

## Test labels changed

None. The message of gaps2's `u_bsj_same_fn` (UB) now says that a re-raise to a caller's buffer is not
modelled. New: `tests/difftest/main_int.c`, `main_argv.c` (`MODE=status CASES=mainargs_cases.txt`: 2 MATCH; a
status-mode case file, as `exit_cases.txt`), `tests/difftest/gaps6.c` (`CASES=gaps6_cases.txt`, a C source,
every case labelled: 1 MATCH, 2 UB: a two-word buffer, and the gap `g_bsj_reraise`).
