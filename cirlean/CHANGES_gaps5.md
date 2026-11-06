# gaps5: the static census's two-blocker programs

Four programs that two library functions each kept out: BenchmarkGame fasta (`fputs`, `fwrite`), UnitTests
2005-05-11-Popcount-ffs-fls (`ffs`, `ffsl`), McGill exptree (`ungetc`, `fscanf`) and McGill misr (`lrand48`,
`seed48`). All are operations of `LibOp` (`Std.libModel`), so `Std.runModel`'s `match` is unchanged apart
from `scanf`'s alternative, whose body moved into `Std.scanfStdin`, which `fscanf` shares.

- `fputs(s, stream)` and `fwrite(ptr, size, n, stream)` to `stdout` or `stderr`: the output is not modelled,
  and the results are glibc's for everything written: 1 for `fputs` (its C string is read), the count for
  `fwrite`, 0 when the size or the count is 0. `fwrite`'s `size * n` bytes must lie in one object (C11
  7.21.8.2p2); indeterminate ones are allowed, as `fwrite` writes them as `unsigned char`s. Any other stream
  is not modelled.
- `ffs(i)` (POSIX) and glibc's `ffsl`, `ffsll`: the position, from 1, of the least significant bit set in
  `i` taken as 32 or 64 bits, 0 for 0. Their names are not reserved by C, so a program's own definition
  wins (`nonReservedModel`).
- `ungetc(c, stdin)`: for `c` = EOF the operation fails and returns EOF (C11 7.21.7.10p3); a character
  pushed back onto standard input is not modelled (undefined here: the reads after it would return it).
  `fscanf(stdin, fmt, ...)` (also glibc's `__isoc99_fscanf`, `__isoc23_fscanf`) is `scanf` on the empty
  standard input. Other streams are not modelled.
- `lrand48()` and `seed48(seed16v)` (POSIX): glibc's 48-bit generator, `X = (a X + c)` mod 2^48 with
  `a` = 0x5DEECE66D and `c` = 0xB, the result `X >> 17`, from `X` = 0 (glibc's zeroed data); `seed48`
  sets `X` from the three `unsigned short`s, least significant first, and returns a pointer to glibc's
  static copy of the previous `X`. The state and that copy live in two blocks allocated at the first use
  (`Std.drand48State`, found later as `atexit`'s registrations are); `lcong48`, which changes `a` and `c`,
  is not modelled.

Pin census: 1187 of the 1812 programs without a static blocker, against 1183 at gaps4 (the four programs
above; none lost; three programs that still need files lost their `fscanf` blocker); the 193 dynamic mains as
at gaps4 (172 run to their end, 17 UB, 4 timeouts).

## Narrowings

None.

## Test labels changed

None. New: `tests/difftest/gaps5.c` (`CASES=gaps5_cases.txt`, a C source, every case labelled: 13 MATCH, 2 UB:
`fwrite` past the end of its object, a character pushed back onto `stdin`). The runner reads results from the
native output, so the writes in the cases show nothing: empty strings, null bytes (dropped by its shell).
