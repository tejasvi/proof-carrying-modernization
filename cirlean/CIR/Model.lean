import CIR.Syntax

/-
  Native models of C++ standard library functions.

  ClangIR modules contain the bodies of every library template the program
  instantiates (`std::vector<int>::push_back`, its allocator traits, split
  buffers, ...). Verifying those bodies would mean verifying libc++. Instead a
  call to a recognised library function is executed by a Lean model over
  abstract values (`std::vector<T>` holds a `List`, `std::optional<T>` an
  `Option`, ...), see `CIR.Std`.

  A `Model` is pure data: which library operation a function symbol denotes,
  with the element type when the model needs it. The frontend attaches it to
  the function declaration (`FuncDecl.model`) using `Model.recognize`; the
  semantics never looks at library bodies of modelled functions.
-/

namespace CIR

/-- The members of `std::vector<bool>` whose models differ from `std::vector<T>`'s. The vector is
`Val.vec g bs` of `bool`s like any modelled vector; `operator[]` and `at` return libc++'s reference
proxy (`__bit_reference`, for `const` `__bit_const_reference`), here the record
`{element pointer, 1}`, which the proxy's members read and write. -/
inductive VecBoolOp where
  /-- `operator[]`, also `const` -/
  | index
  /-- `at`: throws `std::out_of_range` outside the vector -/
  | checkedIndex
  /-- `resize(n, x)`, which takes `x` by copy -/
  | resize
  /-- the proxy's `operator bool()` -/
  | get
  /-- the proxy's `operator=(bool)`: returns the proxy -/
  | set
  /-- the proxy's `operator=(const __bit_reference&)`: the other element's value -/
  | assign
  /-- the proxy's `flip()` -/
  | flip
  /-- `operator==` of two vectors (libc++'s walks their iterators) -/
  | eq
  deriving Repr, Inhabited

/-- Library functions whose models `Std.libModel` runs, behind one alternative of
`Std.runModel` (`Model.lib`): with one more alternative of its own, the automatic proof that
`runModel` preserves well-formedness (`WF_runModel`) runs out of heartbeats. -/
inductive LibOp where
  /-- `std::__1::__hash_memory(p, n)` in libc++'s library (what `std::hash` of strings and
  `__gnu_cxx::hash<const char *>` call): libc++'s CityHash64 of the `n` bytes from `p`
  (`Std.City.hash64`), the bytes of the representation of the object `p` points into
  (`Std.readBytes?`), undefined past its end, for an indeterminate byte or a pointer's byte. -/
  | hashMemory
  /-- `std::__1::__next_prime(n)` in libc++'s library (the bucket counts of the unordered
  containers): 0 for 0, else the smallest prime not below `n` (`Std.nextPrime`); its
  `overflow_error` above `2^64 - 59` is not modelled. -/
  | nextPrime
  /-- `fread(ptr, size, n, stream)` from `stdin`, which is at its end (as for `getchar`): nothing is
  read, the result is 0 (C11 7.21.8.1p3; the end-of-file indicator is not modelled), and `ptr` must
  still be valid (7.1.4p1). Any other stream is not modelled (no file is ever opened). -/
  | fread
  /-- `fputs(s, stream)` to `stdout` or `stderr`: the output is not modelled; the C string `s` is
  read and the result is glibc's for a string written in full, 1. Any other stream is not
  modelled. -/
  | fputs
  /-- `fwrite(ptr, size, n, stream)` to `stdout` or `stderr`: the output is not modelled; the
  `size * n` bytes from `ptr` must lie in one object (C11 7.21.8.2p2, indeterminate ones included:
  they are written as `unsigned char`), and the result is `n`, glibc's for everything written (0
  when `size` or `n` is 0). Any other stream is not modelled. -/
  | fwrite
  /-- POSIX `ffs(i)` (`bits` 32), glibc's `ffsl` / `ffsll` (64): the position, from 1, of the
  least significant bit set in `i` taken as `bits` bits, 0 for 0. -/
  | ffs (bits : Nat)
  /-- `ungetc(c, stream)` on `stdin`: for `c` = EOF the operation fails and the result is EOF
  (C11 7.21.7.10p3); a character pushed back onto standard input is not modelled (the reads
  after it would return it). Any other stream is not modelled. -/
  | ungetc
  /-- `fscanf(stream, fmt, ...)` (also glibc's `__isoc99_fscanf`, `__isoc23_fscanf`) on `stdin`,
  which is at its end: as `scanf` (`Std.scanfStdin`). Any other stream is not modelled. -/
  | fscanf
  /-- POSIX `lrand48()`: glibc's generator, `X = (a X + c) mod 2^48` (`a` = 0x5DEECE66D, `c` = 0xB
  until `lcong48`, which is not modelled), the result `X >> 17`; the state starts at 0 (glibc's
  zeroed data) and lives in a block of its own (`Std.drand48State`). -/
  | lrand48
  /-- POSIX `seed48(seed16v)`: `X` from the three `unsigned short`s (least significant first),
  `a` and `c` back to their defaults; the result points to glibc's static copy of the previous
  `X` (a block of three `unsigned short`s). -/
  | seed48
  deriving Repr, Inhabited

/-- Library operations with a native model. `elem` is the element type of
the container (used to check loads and stores of elements). -/
inductive Model where
  -- std::vector<T>
  | vecCtor (elem : Ty)
  | vecCopyCtor (elem : Ty)
  | vecMoveCtor (elem : Ty)
  | vecInitListCtor (elem : Ty)
  | vecSizeCtor (elem : Ty)
  | vecFillCtor (elem : Ty)
  /-- `vector(first, last[, alloc])` over `T*` / `const T*` or contiguous iterators: the
  elements of the range, which lies within one array or container -/
  | vecRangeCtor (elem : Ty)
  /-- the members of `std::vector<bool>` and of its reference proxy whose models differ from
  `std::vector<T>`'s; its other members are `std::vector<T>`'s with `elem = .bool` -/
  | vecBool (op : VecBoolOp)
  | vecDtor (elem : Ty)
  | vecCopyAssign (elem : Ty)
  | vecMoveAssign (elem : Ty)
  /-- `operator=(std::initializer_list<T>)` -/
  | vecAssignInitList (elem : Ty)
  /-- `assign(n, x)` -/
  | vecAssignFill (elem : Ty)
  /-- `assign(first, last)` over `T*` / `const T*` or `__wrap_iter<T*>` iterators -/
  | vecAssignRange (elem : Ty)
  | vecSize (elem : Ty)
  | vecEmpty (elem : Ty)
  | vecIndex (elem : Ty)
  | vecAt (elem : Ty)
  | vecFront (elem : Ty)
  | vecBack (elem : Ty)
  | vecData (elem : Ty)
  | vecBegin (elem : Ty)
  | vecEnd (elem : Ty)
  /-- `push_back(const T&)`, `push_back(T&&)`, and `emplace_back` of one element when it returns
  `void` (before C++17) -/
  | vecPushBack (elem : Ty)
  /-- `emplace_back` of one element (`T&`, `const T&`, `T&&`): `push_back`'s element path, and a
  reference to the new element (C++17) -/
  | vecEmplaceBack (elem : Ty)
  /-- `emplace_back` with other constructor arguments (none, several, or of another type than the
  element's): not modelled -/
  | vecEmplaceOther (elem : Ty)
  | vecPopBack (elem : Ty)
  | vecClear (elem : Ty)
  | vecResize (elem : Ty)
  | vecReserve (elem : Ty)
  | vecSwap (elem : Ty)
  -- iterators over contiguous storage (`std::__1::__wrap_iter<T*>`,
  -- `__gnu_cxx::__normal_iterator<T*, C>`): a struct holding one pointer
  | iterDeref (elem : Ty)
  | iterInc (elem : Ty)
  | iterDec (elem : Ty)
  | iterEq (elem : Ty)
  | iterNe (elem : Ty)
  | iterLt (elem : Ty)
  | iterDiff (elem : Ty)
  | iterAdd (elem : Ty)
  | iterBase (elem : Ty)
  -- std::basic_string<char>
  | strCtorCStr
  | strCtorDefault
  | strCopyCtor
  | strMoveCtor
  | strDtor
  | strSize
  | strEmpty
  | strIndex
  | strAt
  | strPushBack
  | strAppend
  | strAppendCStr
  | strCStr
  | strEq
  | strBegin
  | strEnd
  | strCopyAssign
  | strMoveAssign
  | strSwap
  /-- `basic_string(first, last[, alloc])` over `char` pointers or contiguous iterators, or (`rev`)
  over their `std::reverse_iterator`s -/
  | strCtorRange (rev : Bool)
  /-- libc++'s `basic_string(n, c[, alloc])`: `n` copies of `c` (its body calls `__init(n, c)` from
  libc++'s library) -/
  | strCtorFill
  /-- libc++'s `__concatenate_strings(alloc, string_view, string_view)`: its `operator+` of a string
  and a string, a C string or a character -/
  | strConcat
  /-- `operator+(const char*, const string&)`, which libc++ exports from its library -/
  | strConcatCStr
  /-- `compare(const char*) const` -/
  | strCompareCStr
  /-- `compare(pos, n1, const char*, n2) const` -/
  | strCompareSub
  -- std::optional<T>
  | optCtorNull (elem : Ty)
  | optCtorValue (elem : Ty)
  | optCopyCtor (elem : Ty)
  | optHasValue (elem : Ty)
  | optDeref (elem : Ty)
  | optValue (elem : Ty)
  | optValueOr (elem : Ty)
  -- std::unique_ptr<T> (default deleter)
  | uptrCtorNull (elem : Ty)
  | uptrCtorPtr (elem : Ty)
  | uptrMoveCtor (elem : Ty)
  | uptrDtor (elem : Ty)
  | uptrGet (elem : Ty)
  | uptrDeref (elem : Ty)
  | uptrReset (elem : Ty)
  | uptrRelease (elem : Ty)
  | uptrBool (elem : Ty)
  -- <algorithm> / <utility> on scalars
  | stdMin (ty : Ty)
  | stdMax (ty : Ty)
  | stdSwap (ty : Ty)
  | stdMove (ty : Ty)
  -- C/C++ runtime
  | abort
  | assertFail
  /-- `exit`: program termination with the status (`Exit.halt`); the exit
  sequence, the `atexit` handlers and the static destructors, follows as after
  a return from `main` (`CIR.endProgram`). -/
  | exit
  /-- `_Exit` and `quick_exit` (`quick`): program termination with the status
  without the exit sequence; `quick_exit` runs the `at_quick_exit` handlers
  first (`CIR.endProgram`); a read-only block of type `_Exit` / `quick_exit`
  records the call (`CIR.exitNowBy`). -/
  | exitNow (quick : Bool)
  /-- libstdc++'s `std::__throw_*` (noreturn): throw the named library exception
  (its typeinfo symbol; the object's contents are not modelled). -/
  | libThrow (typeinfo : String)
  | operatorNew
  | operatorDelete
  -- C library
  | malloc
  | calloc
  | free
  | strlen
  /-- `memset`, `memcpy`, `memmove`, `memcmp`: a pointer argument must be valid also when the
  length is 0 (C11 7.24.1p2: not null, into a live object or just past its end, a
  destination not read-only; `Std.validMemArg`). -/
  | memset
  /-- `memcpy(d, s, n)`: undefined between overlapping objects (`Std.memcpyOverlap`);
  `memmove` copies them. -/
  | memcpy
  | memmove
  | memcmp
  /-- `memcpy`, `memmove`, `memset` and `memcmp` called by the C++ standard library's own code (the
  body of a `std::` or `__gnu_cxx::` function, by its demangled name; `Frontend.tagStdMemCalls`):
  with length 0 nothing is read or written and the pointers are not checked, as its platform's
  functions do. C11 7.24.1p2 binds the program's calls, not the implementation's own (libc++
  relocates and copies empty ranges through null pointers). -/
  | memcpyStd
  | memmoveStd
  | memsetStd
  | memcmpStd
  | strcmp
  | strncmp
  /-- C math functions on `double` (`sqrt`, `pow`, ...) and their `float`
  versions (`single`: `sqrtf`, ...), computed with Lean's `Float` (IEEE
  double; the transcendental ones call the C library). -/
  | libm (fn : String) (single : Bool)
  /-- The runtime library's complex multiplication and division, `__muldc3` / `__divdc3` and
  their `float` versions `__mulsc3` / `__divsc3` (`single`): four parts in, a complex value
  `.arr [re, im]` out, as libgcc computes them (`Std.mulc3`, `Std.divdc3`, `Std.divsc3`). -/
  | mulc3 (single : Bool)
  | divc3 (single : Bool)
  /-- `hypot(x, y)` and `hypotf` (`single`): glibc 2.43's results on the reference machine, bit for
  bit (`Std.hypotF`, `Std.hypotfF`). -/
  | hypot (single : Bool)
  /-- `expm1(x)`: glibc 2.43's result on the reference machine, bit for bit (`Std.expm1F`). -/
  | expm1
  /-- `log1p(x)`: glibc 2.43's result on the reference machine, bit for bit (`Std.log1pF`). -/
  | log1p
  /-- `erf(x)`, `erfc(x)`, `tgamma(x)` and `lgamma(x)`: correctly rounded, as glibc 2.43 computes
  them, bit for bit (`Std.CR.erfCR`, `erfcCR`, `tgammaCR`, `lgammaCR`); undefined ("not
  modelled") where the rounding is not decided at 2048 bits. `lgamma` also stores glibc's sign of
  `Γ(x)` in `signgam` (`Std.CR.lgammaSign`) when the module names it. -/
  | erf
  | erfc
  | tgamma
  | lgamma
  /-- `rint(x)`, `nearbyint(x)` and their `float` versions (`single`): `x` rounded to an integer
  in the default rounding mode, to nearest, half to even (C11 7.12.9.3-4), exactly. -/
  | rint (single : Bool)
  /-- `lrint(x)`, `llrint(x)` and their `float` versions (`fn`, for diagnostics): `x` rounded as by
  `rint`, as a `long` / `long long`; out of their range, or for an infinity or NaN, the value is
  unspecified (C11 7.12.9.5), undefined here. -/
  | lrint (fn : String)
  /-- Constructors and destructors of the standard exception classes
  (`std::logic_error(const char*)`, `~length_error`, ...): no effect on the
  modelled state (the message is not modelled; reading it is undefined). -/
  | excNoop
  /-- `what()` of the standard exception classes whose message is fixed,
  `std::exception` and `std::bad_alloc` (the strings of libc++ and libstdc++):
  a pointer to the first character of the read-only global `whatSym msg` (one per
  message, as the libraries return a literal), or, where the module has no such
  global, of a fresh read-only copy of `msg` and its terminator. -/
  | excWhat (msg : String)
  /-- Output to a `std::basic_ostream<char>` (`operator<<`, `put`, `write`,
  `flush`, `std::endl`): writes nothing to the modelled state and returns the
  stream, which must be an object. `check`: 1 = the second argument must be a C string, 2 = a live
  `std::string`, 0 = nothing to check. -/
  | ostreamOut (check : Nat)
  /-- `<ctype.h>` in the C locale: `isdigit`, `isalpha`, `isalnum`, `isspace`,
  `isupper`, `islower`, `isxdigit`, `ispunct`, `isprint`, `toupper`, `tolower`.
  The argument must be EOF or in the range of `unsigned char`. -/
  | ctype (fn : String)
  /-- glibc's `<ctype.h>` tables (`isdigit` etc. are macros over them):
  `__ctype_b_loc` (class bits), `__ctype_toupper_loc`, `__ctype_tolower_loc`.
  Each returns a pointer to a pointer into a read-only table indexed from -128
  to 255 (C locale). -/
  | ctypeTable (which : Nat)
  /-- `printf`, `fprintf` (`stream` = 1: the first argument is the stream),
  `puts`, `putchar`: the output is not modelled. The format string and the
  arguments are checked (conversion against argument kind, `%s` a C string), and
  `fprintf`'s stream must be a valid `FILE *`, not null (`stdin`, `stdout` and `stderr` are
  distinct non-null handles, `Frontend.stdStreams`);
  the result is the number of characters printed. -/
  | printf (stream : Nat)
  | puts
  | putchar
  /-- `setjmp` / `_setjmp` / `__sigsetjmp` / `__builtin_setjmp` where the parser did not make the
  call an `Op.setjmp` (in a block that branches; its context is checked there): returns 0, the
  direct return; the buffer holds no invocation then, so a `longjmp` with it is undefined (not
  modelled). -/
  | setjmp
  /-- `longjmp(env, v)` (also `_longjmp`, `siglongjmp`, `__longjmp_chk`): back to the `setjmp`
  invocation whose token `env` holds (`Exit.longjmp`, `Std.jmpTokenAt`), which returns `v`, or 1
  when `v` is 0 (C11 7.13.2.1p4); undefined when that invocation is no longer active (p2). Also
  `__builtin_longjmp(buf)`, whose value is 1. -/
  | longjmp
  /-- `strtod(s, end)` (`single`: `strtof`; `atof(s)` without `end`):
  decimal and hexadecimal numbers, `inf`/`infinity`/`nan(...)`, rounded
  correctly to the format (`CIR/Std/Float.lean`); `*end` points after the
  subject sequence (to `s` when there is none), a typed store (`Std.storeEnd`:
  the object must hold a pointer, C11 6.5p7). `atof` of a value that overflows, which cannot be
  represented, is undefined (C11 7.22.1p1). -/
  | strtod (single : Bool)
  /-- `strtol(s, end, base)` and `strtoll` (`signed`), `strtoul` and
  `strtoull` (`long` and `long long` are both 64-bit): white space, a sign,
  bases 0 and 2..36 with their prefixes (`Std.strtolWith`); a value out of
  range gives the bound in the direction of the sign (`ULONG_MAX` for the
  unsigned ones, where a minus sign negates in the unsigned type); `*end`
  points after the subject sequence (to `s` when there is none), a typed store
  as for `strtod`. `c23`:
  glibc's `__isoc23_*` versions (what glibc 2.38+ headers call under
  `_GNU_SOURCE`), which also take a `0b` prefix. `errno` is not modelled. -/
  | strtol (signed c23 : Bool)
  /-- `atoi(s)`, `atol(s)`, `atoll(s)` (`width`: the bits of the result type):
  the value of `strtol(s, NULL, 10)`'s subject sequence (white space, an
  optional sign, decimal digits; 0 when there are no digits). A value outside
  the result type is undefined (C11 7.22.1.2p1). -/
  | atoi (width : Nat)
  /-- `realloc(p, n)`: a new heap block of `n` bytes of the same element type,
  the old elements copied, the old block freed. -/
  | realloc
  /-- `std::__1::__sort<std::__1::__less<T, T>&, T*>(first, last, comp)`, the
  explicit instantiations in libc++'s library (their code is not in the
  headers) that `std::sort` calls for an arithmetic `T` (`elem`) with the
  standard comparators: `[first, last)`, within one array, sorted ascending in
  place through typed loads and stores. Undefined: a range not within one
  array, an indeterminate element, a NaN (no strict weak order, C++
  [alg.sorting]p3). Not modelled: both -0.0 and +0.0 in the range (their
  relative order depends on libc++'s introsort). -/
  | sortLess (elem : Ty)
  /-- The models of `LibOp`, which `Std.libModel` runs. -/
  | lib (op : LibOp)
  /-- `sprintf(buf, fmt, ...)`: conversions `d i u o x X c s f F e E g G %`
  with flags, field width and precision (`Std.sprintfChars`; floating-point
  conversions exact, as glibc; `%s` with a precision reads at most that many
  characters, which need no terminator; the combinations C11 leaves undefined,
  such as `%#d` or `%.3c`, are undefined); the text and its terminator are written to
  `buf`. `snprintf(buf, n, fmt, ...)` writes at most `n - 1` characters and
  the terminator, and returns the full length. The format string or a `%s` string (the
  characters it reads: with a precision, at most that many) overlapping the characters
  written is undefined (`Std.strArgsOverlap`, C11 7.21.6.6p2). -/
  | sprintf
  | snprintf
  /-- `vprintf(fmt, ap)`, `vfprintf(f, fmt, ap)` (`stream` = 1), `vsprintf(buf, fmt, ap)`,
  `vsnprintf(buf, n, fmt, ap)` (C11 7.21.6.8-13): as `printf`, `fprintf`, `sprintf` and
  `snprintf`, with the variadic arguments that the `va_list` `ap` has not given to `va_arg` yet;
  `ap` must be initialized (`Std.vaRemaining`), and `vfprintf`'s stream valid as `fprintf`'s.
  An argument that its call site boxed with its type
  (`Op.vaBox`) must have the type its conversion needs, or the other signedness and a value that
  fits it (`Std.fmtArgsBad`, the check the frontend makes of a `printf` call with a literal
  format). Afterwards the value of `ap` is indeterminate (7.21.6.8p2 and its footnote): state 4
  (`Std.vaLive`), on which only `va_end` is defined. -/
  | vprintf (stream : Nat)
  | vsprintf
  | vsnprintf
  /-- `sscanf(s, fmt, ...)`: conversions `d i u x X f F e E g G a A n %` with `*`,
  field width and length modifiers (`Std.scanChars`; `%x` takes an optional
  `0x`, `%i` reads in base 0 as strtol does: `0x` hexadecimal, a leading 0
  octal, `0b` not modelled); each target object, the one a typed store through
  its pointer reaches (an aggregate's initial scalar), has exactly the
  conversion's type (C11 7.21.6.2p10-12, signedness included) and is written by
  a typed store; the result is the number of assignments, or EOF. -/
  | sscanf
  /-- `scanf(fmt, ...)` (also glibc's `__isoc99_scanf`, `__isoc23_scanf`): standard input is not
  modelled, it is at its end, so as `sscanf` on an empty string: EOF (-1) when the format has a
  directive other than white space and `%n` (an input failure before the first conversion, C11
  7.21.6.4p3), else 0. -/
  | scanf
  /-- `strcpy(d, s)`: the C string `s` and its terminator, into a char range at
  `d`; undefined when the two overlap (`Std.rangesOverlap`). -/
  | strcpy
  /-- `strncpy(d, s, n)`: n characters into a char range at `d`, those of the C string `s`
  read up to its terminator or n of them, then null characters (C11 7.24.2.4); undefined when
  the two overlap. -/
  | strncpy
  /-- `strcat(d, s)`: the C string `s` and its terminator, into the char range from the
  terminator of the C string `d` (C11 7.24.3.1); undefined when the two overlap. -/
  | strcat
  /-- `strchr(s, c)`: a pointer to the first character of the C string `s`
  equal to `c` converted to `char` (the terminator included), or null. -/
  | strchr
  /-- `strrchr(s, c)`: a pointer to the last such character, or null (C11 7.24.5.5). -/
  | strrchr
  /-- `localeconv()`: the C locale's `struct lconv` (`setlocale` is not
  modelled, so the locale is always "C"): `decimal_point` ".", the other
  strings "", the `char` members `CHAR_MAX`; in read-only storage. -/
  | localeconv
  /-- `strdup(s)`: a fresh heap array of `char` holding the C string `s` and its terminator
  (allocation is assumed to succeed). -/
  | strdup
  /-- `getchar()`: standard input is not modelled, it is at its end: `EOF` (-1). -/
  | getchar
  /-- `fflush(stream)`: the output is not modelled (no buffers), so nothing is pending: 0 (never
  `EOF`) for `stdout`, `stderr` and a null pointer (all streams); undefined for `stdin`, an input
  stream (C11 7.21.5.2p2), and for a pointer that designates no stream (7.1.4p1). -/
  | fflush
  /-- `perror(s)`: writes to `stderr`, which is not modelled; `s` is a null pointer or a string
  (C11 7.21.10.4). `errno` is indeterminate afterwards (7.5p3: it may be set to any nonzero value;
  glibc leaves EINVAL when `stderr` is not open for reading). -/
  | perror
  /-- `signal(sig, func)`: registers `func` for `sig` and returns the function registered before
  (`SIG_DFL`, a null pointer, at startup), or `SIG_ERR` (all bits set) for a signal glibc does not let a
  program handle (outside 1..64, `SIGKILL`, `SIGSTOP`, glibc's internal 32 and 33). Signals are
  never delivered here (`raise`, `kill` and hardware traps are not modelled): registering only. -/
  | signal
  /-- `memchr(s, c, n)`: the first character equal to `(unsigned char)c` among the first `n` of
  the char array `s` points into, read one by one up to it (C11 7.24.5.1), or a null pointer; `s`
  must be valid even for `n` = 0 (7.24.1p2). -/
  | memchr
  /-- `posix_memalign(memptr, alignment, size)`: `EINVAL` (22) unless `alignment` is a power of two
  and a multiple of `sizeof(void *)`; else fresh heap storage of `size` bytes (as `malloc`, the
  allocation succeeds) in `*memptr`, and 0 (POSIX.1-2008). -/
  | posixMemalign
  /-- `__cxa_pure_virtual`, the vtable slot of a pure virtual function: a call is undefined
  ("pure virtual call"; the C++ runtime aborts). -/
  | pureVirtual
  /-- `rand()` and `srand(seed)` (`seed` = true) with glibc's generator (`random_r`, `TYPE_3`):
  31 words, `r[i] = r[i-3] + r[i-31]` (mod 2^32), the result `r[i] >> 1` (`RAND_MAX` is
  2^31 - 1); `srand` seeds as glibc does (`Std.randSeed`: the 16807 multiplier, then 310 outputs
  discarded); without `srand` the state is `srand(1)`'s. The state is in a block that
  `CIR.runCtors` allocates before the program (`Std.randBlock`). -/
  | rand (seed : Bool)
  /-- `__cxa_atexit(f, p, d)` (the destructor of a C++ object with static storage duration) and
  `atexit(f)` (`cxa` = false): register `f`, called with `p`, to run in the exit sequence (after
  the program's entry returns, or at `exit`), the last registered first (`CIR.runExit`); returns
  0. -/
  | atexit (cxa : Bool)
  /-- `at_quick_exit(f)`: register `f` to run at `quick_exit`, the last registered first
  (`CIR.endProgram`); returns 0 (C11 7.22.4.3). -/
  | atQuickExit
  /-- `__cxa_guard_acquire(g)`, before a guarded dynamic initialization (a static local
  variable, an inline variable, a static data member of a template): 1 when the guard (a byte
  here, see `parseGlobal`) is 0, and the caller initializes, then calls `__cxa_guard_release`;
  else 0. One thread: nothing waits, and a recursive initialization (undefined) is not
  detected. -/
  | guardAcquire
  /-- `__cxa_guard_release(g)`: the initialization is complete, the guard becomes 1 (a typed
  store into the integer object `g`). -/
  | guardRelease
  /-- `__cxa_guard_abort(g)`: the initialization exited by an exception, the guard is 0 again
  (the next pass through the declaration retries). -/
  | guardAbort
  -- libevent 2.1 and POSIX threads: libraries outside the C and C++ standards (`CIR.Std.World`
  -- holds the environment some of their results depend on)
  /-- `evbuffer_new()` (libevent `<event2/buffer.h>`): a fresh empty buffer, a library object
  (`Std.libObj?`) holding its bytes; allocation is assumed to succeed. -/
  | evbufferNew
  /-- `evbuffer_free(buf)`: the buffer, which must be a live one, is freed. -/
  | evbufferFree
  /-- `evbuffer_add(buf, data, n)`: the `n` bytes at `data` (a `char` range; valid also when `n`
  is 0) appended to the buffer; 0 (allocation is assumed to succeed). -/
  | evbufferAdd
  /-- `evbuffer_get_length(buf)`: the number of bytes in the buffer. -/
  | evbufferLength
  /-- `evhttp_add_header(headers, key, value)` (`<event2/http.h>`): -1 for a key or a value
  holding CR or LF (libevent 2.1.12 refuses folded values too); else a new `struct evkeyval` with
  heap copies of both strings goes to the end of the list `headers` (`TAILQ_INSERT_TAIL`, typed
  stores), and 0 (allocation is assumed to succeed). -/
  | evhttpAddHeader
  /-- `evhttp_send_reply(req, code, reason, databuf)`: the request becomes libevent's and is freed
  with what it owns (`Std.evFreeRequest`): at once when it has no connection (`databuf` is left as
  it is), else after sending, when `databuf`'s bytes move into the reply (`databuf` is empty). -/
  | evhttpSendReply
  /-- `event_base_loopbreak(base)` (`<event2/event.h>`): -1 for a null base; 0 for a live one (the
  event loop is not modelled, so the flag it sets is not observable). -/
  | eventBaseLoopbreak
  /-- `pthread_self()`: the id of the calling thread, the only one (`Std.World.threadId`). -/
  | pthreadSelf
  /-- `pthread_equal(a, b)`: 1 when the ids are equal, else 0 (glibc compares them). -/
  | pthreadEqual
  /-- `pthread_setschedparam(t, policy, param)`: `t` must be the thread's id (`Std.World.threadId`).
  Linux's checks (`Std.schedParamError`): EINVAL for a policy that is not one (`SCHED_RESET_ON_FORK`
  aside) or `SCHED_DEADLINE`, and for a priority outside 1..99 with `SCHED_FIFO`, `SCHED_RR`, or
  other than 0 with the others; EPERM for a real-time policy without the privilege
  (`Std.World.rtPrivileged`, assumed); else 0. The result is the error number, and glibc also
  stores a nonzero one in `errno`. -/
  | pthreadSetschedparam
  /-- `sched_get_priority_max(policy)` (`max`), `sched_get_priority_min(policy)`: Linux's values,
  99 and 1 for `SCHED_FIFO` and `SCHED_RR`, 0 for `SCHED_OTHER`, `SCHED_BATCH`, `SCHED_IDLE`,
  `SCHED_DEADLINE`, `SCHED_EXT`; for anything else -1, and `errno` is EINVAL. -/
  | schedPriority (max : Bool)
  /-- `__errno_location()`, which glibc's `errno` expands to: the address of the program's `errno`,
  an `int` global that the frontend adds to a module declaring this function (`Std.errnoSym`; 0 at
  program start, C11 7.5p3). -/
  | errnoLocation
  /-- `strerror_r(e, buf, n)`, GNU's (which glibc declares under `_GNU_SOURCE`, as `g++` defines it):
  glibc's message for an error number it knows (`Std.glibcErrorText`), a string of its own, `buf`
  unused; else `"Unknown error e"` written to `buf` as `snprintf(buf, n, …)` would, and `buf`. -/
  | strerrorR
  /-- `time(t)`: the current calendar time, `Std.World.now` seconds since the Epoch, also stored
  into `*t` when `t` is not null. -/
  | time
  /-- `ctime_r(t, buf)`: `*t` as local time (`Std.World.tzOffset` seconds east of UTC) in
  `asctime`'s form, `"Thu Jan  1 00:00:00 1970\n"`, written to `buf`, and `buf` (`Std.ctimeText`);
  as glibc: null with `errno` EOVERFLOW (`buf` holding the first 25 characters) when the text with
  its terminator needs more than 26 bytes, and null with `errno` EINVAL when the year does not fit
  `struct tm`. -/
  | ctimeR
  deriving Repr, Inhabited

/-- The global holding the string `what()` returns for an exception class with the fixed message
`msg` (`Model.excWhat`; the frontend adds it, `Frontend.stdWhat`). -/
def whatSym (msg : String) : String := "__cirlean.what." ++ msg

end CIR
