# retslot: results of classes that are non-trivial for calls

ClangIR before calling-convention lowering returns a record as a value: the callee builds the result in its return
slot (`cir.alloca "__retval"`, also the named object of a named return value) and returns a load of it; the caller
stores the value into the object the call initializes (a variable, a temporary, a member, its own return slot).
Executed as written that is two objects, and the callee's dies at its return. For a class that points into itself it
is wrong: libc++'s std::list keeps its end node inside the list object, so a list returned by value kept nodes
pointing at the callee's dead return slot (sorting_strand_sort: "invalid memory write"; byval.cpp's g_list_return),
and so did a std::map (its tree's end node), a class holding `this` ("comparison of an invalid pointer" when it
compares the pointer with its own address), or a class that registers its address.

C++ makes the result one object: a prvalue result initializes the object directly ([dcl.init.general]p16.6.1), a
return statement copy-initializes the result object ([stmt.return]p2), no further copy may be made of a class with a
non-trivial copy or move constructor or destructor ([class.temporary]p3); the Itanium ABI passes the result object's
address to the callee for such a class.

## The rewrite (`CIR/Frontend/RetSlot.lean`)

For the records that are non-trivial for calls (`Frontend.nonTrivialRecords`, as for by-value parameters),
`Frontend.retObjects`, run when a module is loaded (after `objectParams`) and again on a linked module:

- gives each function returning such a record a hidden parameter after its named ones (before any variadic
  arguments), a pointer to the record, and makes it return nothing (`FuncDecl.retObj`, which `cir2lean` does not
  write); in a definition the return slot's alloca becomes a bitcast of that parameter and each `return` of a load
  of the slot returns nothing. A definition with any other return of a value makes its calls not modelled;
- makes each call pass the object its result was stored into (the store right after the call) and drops that store;
  an indirect call passes it last. A call whose result anything else reads, or that has no result, becomes the
  operation `a return value of a class non-trivial for calls, not modelled`, undefined when it runs, never a silent
  copy;
- keeps calls of library models (their models give values) and trivially copyable records (the value copy, which
  [class.temporary]p3 allows).

The pass is idempotent: a function already rewritten keeps its form, and a call into it from a unit that did not know
the class non-trivial is rewritten when the linked module runs the pass again.

## Narrowings

None. In the T2 and T3 units no call or function became not modelled (0 markers in their Gen).

## Limits

`Frontend.nonTrivialRecords` (here and for by-value parameters) knows a record is non-trivial for calls only from the
copy or move constructors and destructors the module emits. A class whose user copy or move constructor is never
emitted (the named return value elides it, or a prvalue initializes the object) and which has no destructor counts as
trivially copyable: its result is still copied out of the callee's slot, and a caller's copy of a class that points
into itself points into the dead slot (the evidence-owner session's probe, checks/byval-20261029T025320Z/probe/ret.cpp: "invalid memory read"
at next3 709db2e, native 1; the labelled gap g_elided_copy). By-value arguments of such a class built from a prvalue
are the same case. The CIR carries nothing else that would tell: a record definition holds only its members (the only
attribute in the T2/T3 claim CIR is #cir.bitfield_decl), and a member that is not used is not declared. A fix needs the
producer to say it, any of:
- clang's -femit-all-decls emits the unused copy constructor (on the probe: `cxx_ctor<!rec_S, copy>`, and 709db2e then
  gives 1), but it emits every inline function of every header, untested on the thrift units;
- calling-convention lowering left on marks the result (`make` takes `llvm.sret = !rec_S`; 709db2e gives 1 on that CIR
  too), but it lowers every signature, also the C struct arguments the semantics takes as values;
- a ClangIR attribute on records that are non-trivial for calls (clang's CXXRecordDecl::canPassInRegisters), which
  nonTrivialRecords would then read.
A frontend guess cannot replace it: making every returned record one object would also change trivially copyable
classes, whose copy C++ allows and the ABI makes for small ones (a trivially copyable class pointing into itself
compares unequal to its copy natively). The claims are not affected: no claimed closure returns or passes such a class
(retscan v3, cirpun --allrec: no self-referential or kept result or temporary of a record not known non-trivial in 307
jobs; the evidence-owner session's screen agrees).

## Gen

C modules are unchanged (cJSON's Gen, LP64 and i686, is byte-identical). In a C++ module the functions returning
such records change (a parameter, no result, the slot's alloca and the loads before their returns) and so do their
calls (an argument, no result, no store): 418 of the 558 T2 units and 410 of the 530 T3 units (cir2lean of next3
a623986 against this branch); the 33 tracked examples (Examples/cpp/*.cir) are unchanged. Roots of claims that
return such a record (their Gen and statements change shape): T3 unit 50 TNonblockingServerSocket::getPath() (old
and new, std::string); T2 74 getPath, 338 t_container::get_cpp_name, 483 t_generator_factory::get_documentation
(std::string); D2 38 tinyxml2::XMLHandle::NextSibling, 61 XMLConstHandle::FirstChild (a user copy constructor).

## Test labels changed

byval_cases.txt: g_list_return, a gap (UB), is labelled MATCH. New: `tests/difftest/retslot.cpp`
(`CASES=retslot_cases.txt`, 14 cases, every case labelled): with libc++ next3 gave 4 MATCH and 10 UB, this branch 14
MATCH; with libstdc++ 2 MATCH before, 11 after (r_map and r_set stop with type-punned access, and r_string, whose
std::string(n, c) has a model with libc++ only, with "object is not a live std::vector / std::string": the same UB
as before).
