# audit: items of rog's audit of next3 (scratch/soundaudit_n3/FINDINGS.md)

- M12 (missed UB): `fflush` returned 0 for any pointer. It returns 0 for `stdout`, `stderr` and a null pointer
  (all output streams; output has no buffers in the model), and is undefined for `stdin`, an input stream (C11
  7.21.5.2p2), and for any other pointer, which designates no stream (7.1.4p1). The streams are the handles 1, 2
  and 3 that `stdStreams` gives `stdin`, `stdout`, `stderr`.
- F5 (false UB): a module only declares the typeinfo objects of the fundamental types (`_ZTIi`, `_ZTIPKc`, ...),
  which the C++ runtime library defines, so `typeid(int)` read an object without a value. The frontend
  (`stdTypeinfo`) gives each declared one its value, read-only, laid out as a class's typeinfo constant: an
  indeterminate vptr (the runtime's vtables are not modelled; reading it is undefined) and a pointer to the
  first character of its name `_ZTS…`, the mangled type, which it adds (or gives its value) when the module does
  not define it. The Itanium codes `v w b c a h s t i j l m x y n o f d e g Ds Di Du Dn`, each also as a pointer
  (`P`) and a pointer to const (`PK`).
- F6 (false UB): the name in a class's typeinfo constant points to the `_ZTS` array object, not its element 0, and
  the string models refused it. `readCStr`, `readCStrN`, `arrTail` (strcmp, strncmp) and `strchr` read a pointer
  to an array object from its element 0 (`arrayObjStart?`), as bytes' rule makes a pointer to an array object
  converted to a pointer to its element type (`CHANGES_bytes.md`, 2 and 3); element pointers are read as before.
- N1: `what()` of `std::exception` / `std::bad_alloc` returned a fresh array per call. The frontend (`stdWhat`)
  adds one read-only string per message (`whatSym`), which the model returns, as the libraries return a literal:
  `e.what() == e.what()`.
- F15 (false UB): vector left shifts kept the scalar rule of C11 6.5.7p4 (`(v4si){-1} << 1` was UB), though
  Clang emits vector shifts without overflow flags, like the other vector arithmetic, which wraps. A vector left
  shift wraps (`evalVecShift`); a count outside `0 ≤ n < width` stays undefined.
- N4: `memcmp` returned -1, 0 or 1; it returns glibc's result, the difference of the first differing bytes as
  `unsigned char` (only the sign is specified, C11 7.24.4.1p2), as the `strcmp` model does.

## Narrowings

M12: `fflush` of `stdin` or of a pointer that is no stream is UB (it returned 0).

## Test labels changed

None in the existing case files. New: `tests/difftest/audit.cpp` (`CASES=audit_cases.txt`, every case labelled).
