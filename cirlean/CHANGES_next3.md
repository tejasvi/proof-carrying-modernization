# cirlean next3: changes since next2 424e821

Each item names its branch and labelled case file(s) (tests/difftest). "UB" = the semantics reports undefined
behaviour; "gap" = a labelled case where it is known not to. Exposure checks and sealed scans are under
~/cirlean_work/scratch; the freeze notice lists each with the sha256 of its SHA256SUMS. Restatements and proof-script
changes: RESTATEMENTS_next3.md.

## Deviations of earlier pins that next3 fixes (reported to the evidence-owner session with exposure checks)
- **Pointer arithmetic in the pointer's units** (bytes): next2 and earlier counted strides/differences in elements of
  the array reached, not sizeof(pointee): wrong values and false UB (stride scan v2: scratch/stridescan_v2).
- **By-value parameters of classes non-trivial for calls** (byval): earlier pins gave the callee a bitwise second
  object; next3 passes the caller's temporary (one object, Itanium). Exposure on claimed paths: none
  (scratch/byvalscan).
- **Results of classes non-trivial for calls** (retslot): earlier pins copied the result out of the callee's return
  slot, which dies at the return (a pointer into it, e.g. a short string's buffer or a list's end node, dangles);
  next3 makes the caller's destination the result object (hidden result pointer, Itanium); any other shape is "not
  modelled", never a silent copy. Exposure on claimed paths: none (scratch/retscan v1-v3; the evidence-owner session's independent screen
  agrees). Limit: a class whose only non-trivial member is a user copy constructor that NRVO elides is not
  recognised, since the CIR record carries nothing about it (labelled gap g_elided_copy; the fix needs a ClangIR
  record attribute).
- **Declared-only globals read as zeros** (externglob2, externglob3): reads and writes of a global the module only
  declares are UB unless modelled: stdin/stdout/stderr, the fundamental typeinfo objects, __libc_single_threaded = 1,
  getopt's optind = opterr = 1, libm's signgam (written by the lgamma models), and the C++ stream objects
  (std::cout/cerr/clog/cin and the wide ones), which are live objects of indeterminate value, so operator<< takes them
  while a member read is UB. Exposure: no declared-only access on a path a non-vacuous verdict relates
  (scratch/sealscan_20261029T055225Z: 45 of 521 claims have such a read in an over-approximated closure; reasons per
  claim).
- **Pointer↔integer conversions** (intptr2, intptrlife2, intptrzap): earlier pins gave an index encoding (wrong
  values against GCC) and made round trips UB (against 7.20.1.4); next3 uses flat addresses (block b at
  (b+1)·2^32); int→ptr gives the provenance of the live block at that address; function addresses and Itanium member
  function pointers are integers; void* arithmetic counts bytes; converting a pointer whose object's lifetime ended is
  UB, like its comparison and arithmetic (6.2.4p2). T2/T3: no verdict-covered function converts pointers to integers.
- **Single-precision math** (f32math): earlier float models rounded the double result (1 ulp off glibc on millions
  of inputs); next3 calls glibc's float functions (exhaustive re-scan: 0 mismatches).

## Memory, pointers and object representations (bytes phases 1-5, memb, vecstore, unionact3/4b/5b, unionfix3)
- Character access reads/writes a byte of an int, float, bool or record object (little-endian; records by member
  offsets) (C11 6.5p7, 6.2.6.1p4). Byte-wise memcpy/memmove/memset; a pointer survives only when all its bytes are
  copied in order; invalid _Bool/NaN bytes are kept until the object is read as its type.
- Stride/difference in the pointer's units; same-size array elements keep exact results. **Strict subobject rule**
  (agreed with the evidence-owner session): non-character arithmetic from a pointer that is not an array element allows n ∈ {0, 1} only,
  the one-past pointer is not dereferenceable (6.5.6p7-8, 6.7.2.1p15); character arithmetic ranges over the complete
  object (offsetof, container_of), and a cast back designates the subobject at that byte offset.
- A scalar access at an aggregate path descends to the initial element (G5); record access through another record
  type is UB unless the object starts with that type (G4); record loads/stores over scalars or arrays go member by
  member (6.5p7 aggregate clause); an array-object pointer used with the element type designates element 0; a lone
  object is an array of one (one-past pointers); bit-fields placed over other objects use their declared type.
- Pointer equality/relational comparison by byte position within one block (&s == &s.a) (6.5.9p6, 6.5.8p5).
- In C, converting to a misaligned pointer is UB (6.3.2.3p7); C++ keeps the value.
- Vectors (vecstore): a vector or complex access over objects of another type (e.g. a v4sf store through &buf[0]
  of float buf[64]) reads/writes those objects element by element at its bytes (was: buf[0] overwritten with the
  whole vector, a wrong value); a record's vector member is aligned to its size rounded up to a power of two (was:
  wrong offsets and sizeof, e.g. struct {float x; v4sf v;} put v at 4, native 16); a vector access whose byte
  position is not a multiple of its CIR alignment is UB in C and C++ (a misaligned conversion never used is not
  caught: CIR erases typedef alignment).
- Unions (unionact3, unionact4b, unionact5b, unionfix3): the member last stored is the active one, whichever pointer
  the store went through (6.5.2.3p3, footnote 95); reads view the union without writing, so const unions are readable;
  a member read while indeterminate takes the active member's bytes: same-size scalars as they are, scalars of another
  size composed little-endian from the bytes the active member holds (bytes it does not hold stay indeterminate; bool
  trap bytes and NaN patterns are kept and their reads are UB), so the common initial sequence, a struct's first
  member, narrower or array members after a wider store and a byte store followed by a wider read behave as in C.
  Whether a path enters a union is decided from the block's type and the path alone (Ctx.unionOnPath).
- VCG performance (fhrt2): reachIn/memberPath are split into exact type tests plus folded slow cases (answers
  unchanged); simprocs decide the tests, the union step included, with type facts the FH chain states for its item
  blocks, so the FH bundles stay on the fast path (parse_array 1.42 core-h, parse_object 0.93; next2 1.89 / 1.14).

## Objects and lifetimes
- **const objects** (constobj2 + constobj3 option (c)): const-qualified locals are read-only once initialized
  (6.7.3p6); byte stores and memcpy/memset into them are UB. **Known gap introduced**: a const local no longer ends at
  its scope's exit, so a dangling pointer to it is not caught (next2 caught it): c_scope, next3.1 item. The FH chain
  is unchanged by it (killRange and its lemmas as before).
- C++ object lifetime (nx3, nx3b2): an object's lifetime ends when its destructor runs ([basic.life]p1): after a
  destructor body returns, the object (complete or subobject; automatic, temporary, by-value parameter or heap) has a
  fresh object's value, so reads are UB ([basic.life]p7); placement-new reuse stays defined ([basic.life]p8); const
  objects end too. Not detected: writes to or member calls on a destroyed object; a second destructor that does not
  read it; temporaries without a destructor (a C struct-returning call's array member after its full expression,
  6.2.4p8; a std::initializer_list backing array after its statement), since ClangIR gives them no full-expression end
  (labelled gaps).
- Exit sequence (exitseq2): the exiting frames' objects live while handlers run; late-registered handlers run; a
  static object's lifetime ends when its destructor runs (audit2b, M14).
- setjmp/longjmp (sjlj, auditfix8) with the strict contexts of 7.13.1.1p4, checked also when the block branches;
  after a longjmp the objects changed since the setjmp are indeterminate (7.13.2.1p3), found by dynamic store marks
  in every function of a module with a setjmp (library models' stores included), non-volatile by the program's own
  accesses. Flowing off a non-void function (retval) is UB only when the value is used, incl. aggregates in C (M13).

## C++ object model
- Function aliases (alias) and variable aliases (auditfix8: an alias names its target's object; a function alias of
  another type is UB to call, 6.5.2.2p9), VTTs/virtual bases/thunks (vtt), by-value parameters (byval), C++-only null
  arithmetic, std:: library code's own mem* calls with n = 0 (library code = std namespace AND library-header
  definition).
- Linker: anonymous records matched by structure and member names across units (anonlink, anonnames).
- Array new (arrnew, arrfix): new T[n] works for class types (constructors, value/default initialization, derived
  classes, runtime n); the array cookie of a class with a non-trivial destructor is not modelled (labelled gap).
- Empty values (gaps7): in C++ modules a store or copy of a type with no value representation (a record whose members
  are only padding, empty members or such records; arrays of them) writes nothing ([intro.object]p9,
  [dcl.attr.nouniqueaddr]), so an empty [[no_unique_address]] member (libc++'s allocators in map/set/list) no longer
  overwrites the member it overlaps (was: false UB on container copies). C modules keep such stores.
- Containers: initializer_list begins as &arr[0]; vector assign/emplace_back; string range ctor/operator+/compare/
  swap/(n, c)/reserve; __to_address of iterators; mem* over vector/string storage; a libc++ vector whose members are
  all null is an empty vector, vector(first, last), libc++ vector<bool> (vecfix); a zeroed vptr is null, so a virtual
  call through it is UB.

## Variadics and formatted I/O
- va_list boxes and lifecycle (vastruct, vafmt; auditfix8: ownership per activation: a second callee's va_arg,
  va_end outside the owner and a block exit without va_end are UB), printf/scanf argument types (only constant globals
  count as literal formats), v*printf (vprintf; vfprintf validates its stream), sscanf %i base 0 and typed stores
  (sscanfi), %lc encoding errors (libfix2; errno EILSEQ), memchr over any object (audit2b), fflush(stdin) UB.

## Interpreter performance (perf1, perf2; compiled code only)
- cirrun keeps a memory's blocks in a persistent hash map behind the function view (@[implemented_by] on the Mem
  builders), with a stack of live stack-block ids, and computes integer bounds from a table (@[csimp] with equality
  proofs); definitions, lemmas, the VCG and every kernel-checked proof are unchanged (no proof uses compiled code).
  Loops are linear instead of quadratic (100-200× on long loops). CIR_MEMCHECK=1 runs the reference representation
  beside the map and stops on any difference (0 differences over the case files, the census mains and the V smoke
  corpus).

## Library models added
- census3/4/5 (rand, fflush, rethrow, typeinfo, math via Float, what(), std::sort), complex (libgcc's __muldc3/
  __divdc3 family incl. this machine's fused products), simd + vecscalar (vectors as T[N], vector↔scalar bitcasts by
  bytes, NaN lanes indeterminate), cheap1 (fp classes, rint family, catch by pointer, perror, signal, memchr,
  posix_memalign), libm1 (hypot/expm1/log1p bit-exact as glibc x86-64-v3; erf/erfc/tgamma/lgamma correctly rounded),
  f32math (glibc float functions via Float32), extmodels tier 1 (libevent ×8, pthread_self/equal; only on body-less
  declarations), cmpxchg orders (C-only stronger rule), extmodels tier 2 (t2models8: sched_get_priority_max/min,
  pthread_setschedparam, __errno_location with a program-wide errno that the strto*/libm/sscanf/printf/perror models
  set as glibc does (indeterminate where glibc's rule varies), strerror_r (GNU), time, ctime_r; atof of an
  unrepresentable value is UB, 7.22.1p1).
- Soundness fix (census4): no model is attached to a function with internal linkage and a body.
- gaps1-gaps6 (census frontier): inline asm with memory operands for empty/nop templates (a tied +g/=g output stores
  its input through the pointer) and reg→mem moves, other templates stay unknown; strncpy/strcat/strrchr (UB on a
  short destination or overlap); x86 SSE intrinsics packssdw/pslli.w/psrli.w/max.ps/movmsk.ps as pure functions
  (movmsk of a NaN: labelled gap); __builtin_setjmp/__builtin_longjmp on the setjmp machinery (a 5-word buffer of
  pointers or int64, else UB; __builtin_longjmp is undefined for its own buf; to a buffer a caller set, not modelled
  (reported as undefined)); libc++ __hash_memory (CityHash64) and __next_prime; fread on the empty stdin;
  fputs/fwrite results; ffs family; ungetc(EOF); fscanf on stdin; lrand48/seed48 (glibc's 48-bit LCG). Census
  (wfglobal's pin census): 1188 programs fully modelled statically (1164 at next3 a623986), and 174 of the 193
  dynamic mains run to exit (169 at 709db2e); the pin's own census is reported with the freeze.

## Trust base (assumptions the models make)
- Allocation succeeds (malloc/new/evbuffer_new/...); one thread, pthread_t = 1, which may use real-time scheduling
  policies; the clock reads the Epoch (time) and local time is UTC (ctime_r); stdin is empty; main(int) and
  main(int, char**) receive argc = 1 (C11 5.1.2.2.1 allows implementation-defined forms); the installed glibc/libgcc
  (x86-64-v3 builds) define the math results; __libc_single_threaded = 1; stdin/stdout/stderr are distinct non-null
  handles; the fundamental typeinfo objects have their library values.
- C++ modules: a union member read reinterprets the active member's bytes, as GCC and Clang document; ISO C++ leaves
  it undefined ([class.union], [basic.life]p7); the common initial sequence is exempt in both (the evidence-owner session's option A,
  2026-10-29). Claims that depend on it: T2 0132, 0254, 0566 (thrift's bitwise_cast); later ones are added here.

## Modelling choices and known gaps (labelled)
- Pointers to objects whose lifetime ended (6.2.4p2): comparison, arithmetic and conversion to an integer are UB; a
  truth test `if (p)` of such a pointer is still defined (known inconsistency kept because cJSON's Gen has 46
  pointer-to-bool casts on the VCG hot path; next3.1). Addresses are never reused (block ids only grow), so a dead
  object's address never equals a later object's (natively it may). C++ modules use the C rule although C++ makes
  uses other than indirection and deallocation implementation-defined ([basic.stc.general]p4): a false UB (1 census
  main), next3.1. Pointer exposure (PNVI-ae-udi) is not tracked: every live block counts as exposed.
- Gaps: const locals do not end at scope exit (c_scope); const members of non-const structs; CIR erases char/signed
  char/char8_t and long/long long (M10/N3); non-literal printf formats unchecked (M9); padding bytes UB; libc++
  vector<bool> bit iterators, front/back/flip; an array member of a const union read through another array member
  (UB); temporaries without a destructor after their full expression (L1/L2); a class with only an NRVO-elided user
  copy constructor (retslot); __builtin_longjmp to a buffer a caller set (reported as undefined); the array cookie of
  new T[n] with a non-trivial destructor.

## Statement shapes that change at any next3 pin (scratch/retscan/addendum)
- byval: T2 130 TSocket::setPath, T2 463 TConnection::setSocket, T2 549 t_delphi_generator::finalize_field (#2, #5):
  record parameters become pointers to the caller's object (same arity).
- retslot: T3 50 TNonblockingServerSocket::getPath (old and new), T2 74/338/483, D2 38/61: [ptr this] → R becomes
  [ptr this, ptr R] → void; the observed result is the result object's contents after the call.
- Statements generated for the old signatures relate no execution at next3 and are regenerated by their owners.
