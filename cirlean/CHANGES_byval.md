# byval: by-value parameters of classes that are non-trivial for calls

ClangIR before calling-convention lowering passes a record argument as a value. In math_fibonacci_sum,
`matrix power(matrix t, uint64_t ex)` (a vector of vectors, which has no model) calls itself as
`t = power(t, ex / 2)`: the caller copy-constructs a temporary (`agg.tmp`), loads it and passes the value; the callee
stores the value into its parameter's slot; the caller destroys the temporary at the end of the full expression, and
the callee never destroys its slot. Executed as written that is two objects sharing one heap buffer. `return t`
moves the buffer into the result and empties the callee's copy, not the caller's temporary, whose destruction then
frees the buffer the result owns: "invalid read in library model" on a freed block.

C++ makes the parameter one object: it is initialized from the argument by the copy or move constructor
([expr.call]p7), no further copy may be made of a class with a non-trivial copy or move constructor or destructor
([class.temporary]p3), and whether it dies at the return or at the end of the full expression is
implementation-defined ([expr.call]p6); the Itanium ABI passes such an object by address and the caller destroys it at
the end of the full expression.

## The rewrite (`CIR/Frontend/ByValue.lean`)

For the records that are non-trivial for calls (`Frontend.nonTrivialRecords`: the module has a copy or move
constructor of `R`, two pointers to `R`, or a destructor of `R`), `Frontend.objectParams`, run when a module is loaded
and again on a linked module:

- makes each by-value parameter of such a record a pointer to it (in definitions and declarations); its slot, the
  alloca the parameter is stored into, becomes a bitcast of the parameter, and the store goes. A parameter used
  otherwise than by that one store makes the function's calls not modelled;
- makes each call pass the temporary its argument was loaded from (the record load and the local object in scope at
  the call: ClangIR numbers each region on from its parent, so a value name can come back in a sibling region). An
  argument of such a record that is no load of a local object is not modelled: the call becomes the operation
  `a by-value argument of a class non-trivial for calls, not modelled`, undefined when it runs, never a silent copy;
- keeps calls of library models (their models take values) and trivially copyable records (no copy or move
  constructor and no destructor among the module's functions: the value copy, which [class.temporary]p3 allows).

`Frontend.opUses` gives the values every operation reads. The pass is idempotent: a linked module runs it again, so
a parameter whose class only another unit shows non-trivial becomes an object there too.

## Results by value

A result by value of such a class was still copied out of the callee's return slot (`cir.load` of `__retval`, then
`cir.return`), which is right for classes without pointers into themselves and for the library models' values, and
wrong for one that points into itself: libc++'s std::list keeps its end node inside the list object, so a list
returned by value kept nodes pointing at the callee's return slot, which dies at the return (sorting_strand_sort;
g_list_return, a labelled gap here). The caller's object is now the result object (CHANGES_retslot.md), and
g_list_return is labelled MATCH.

## Narrowings

None.

## Gen

C modules are unchanged (no record is non-trivial for calls in C). In a C++ module the functions with such
parameters change (parameter types, the slot's alloca and store) and so do the calls that pass them.

## Test labels changed

None in the existing case files. New: `tests/difftest/byval.cpp` (`CASES=byval_cases.txt`, every case labelled).
