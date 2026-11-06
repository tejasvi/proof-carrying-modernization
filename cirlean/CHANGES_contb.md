# contb: container models through an initializer_list's begin

CIR stores the address of an `initializer_list`'s backing array object (`T(*)[N]`, through a bitcast of the
field's address) as its `const T*` begin. For lists of `std::vector` or `std::string` elements, libc++'s own code
walks the list (a vector of vectors or of strings has no model) and hands the begin pointer, and the strides from
it, to the modelled element constructors: the begin pointer designates the array object, and its strides are byte
views of that object (`Ctx.stride?` treats it as one object). The models read `.arr` there, or nothing, and were UB
"object is not a live std::vector / std::string" (12 census mains since the stride fix).

`Std.readVec` now reads, through a pointer that designates no container, the container at its address
(`Std.containerAt?`): the first element of an array of containers (recursively), or the element at a byte view of
such an array at a multiple of the element size. The element pointers the models return are built from that
container (`Std.contPtr`, in `cir_exec`: it is the pointer itself when that holds a container). A pointer that
designates a container is read and indexed as before (the Examples and the CJ examples build unchanged); a pointer
that reaches no container this way stays UB.

## contb2: the begin store itself

The parser now stores what the field is declared to hold (`initListBegins` / `initListRegion` in
`CIR/Frontend/Parser.lean`): a bitcast from the address of a `T*` to the address of a `T(*)[N]` that exactly one
store of a `T(*)[N]` goes through,

    %c = cir.cast bitcast %f : !cir.ptr<!cir.ptr<T>> -> !cir.ptr<!cir.ptr<!cir.array<T x N>>>
    cir.store %arr, %c : !cir.ptr<!cir.array<T x N>>, ...

has that store replaced by the store of `&arr[0]` into the field, through a fresh value:

    %d = cir.cast array_to_ptrdecay %arr : !cir.ptr<!cir.array<T x N>> -> !cir.ptr<T>
    cir.store %d, %f : !cir.ptr<T>, !cir.ptr<!cir.ptr<T>>

This is the C++ meaning (C++ [dcl.init.list]p5: `begin()` points to the first element). The begin is then an
element pointer, its strides are element pointers, and the member accesses, loads and model calls through it see
the element: a list of structs (`cir.get_member` through the begin selected an element, not the member of element
0), lists of pairs and of other records read by libc++'s own code (UB "type-punned access" through a byte view),
the program's own loop over an `initializer_list`. The models' reading at the address of an array of containers
(above) stays for other pointers to such arrays. The cJSON Gen and the T3 units veriforch certifies (530 unit
files, none with the pattern) are unchanged by the rewrite.

## C++ null pointer arithmetic

A module records whether it is C++ (`Module.cxx`, from `cir.lang = #cir.lang<cxx>`; a linked module when every
unit is; `cir2lean` writes `cxx := true` only for C++ modules, so C modules' output is unchanged). In C++ a null
pointer plus or minus 0 is null and the difference of two null pointers is 0 (C++ [expr.add]p4.1, p5.1): libc++'s
code takes `end - begin` of an empty vector whose element type has no model. `cir.ptr_stride` and `cir.ptr_diff`
take these cases first, on a null operand; C keeps both UB (C11 6.5.6p8, p9), and any other pointer goes through
`Ctx.stride?` / `Ctx.diff?` as before.

## std::vector::emplace_back

`emplace_back` of one element (`T&`, `const T&`, `T&&` of the element type) is `push_back`'s model, returning a
reference to the new element (C++17; a `void` result maps to `push_back`'s model itself). With other constructor
arguments (none, several, or of another type than the element's) it is UB "not modelled": the vector is a model's
value, so libc++'s body of `emplace_back` cannot run on it.

## Narrowings

None.

## Test labels changed

`cases.txt`: `t_gap_emplace` (emplace_back returning `T&`) is MATCH (it was UB, a known gap). Every other existing
case file: cirrun's output identical to 49fa46e's. contb's own `contb_cases.txt` grows (`contb.cpp`, `contbc.c`;
every case labelled), with `g_struct_list` and `g_nested_strings` renamed `c_` and relabelled MATCH.

## Gaps (labelled UB in contb_cases.txt)

Defined in C++, UB in the model: `g_one_vec_list` (a list of one vector: the copy goes into a one-element buffer,
a heap object of the element's type that is no array element, and libc++ steps past it; a lone object as an array
of one is bytes phase 1b), and two `emplace_back` forms that are not modelled, `g_emplace_convert` (an `int` into
a vector of `long`) and `g_emplace_none` (no argument). contb's `g_struct_list` and `g_nested_strings` are MATCH
since contb2 (`c_struct_list`, `c_nested_strings`).
