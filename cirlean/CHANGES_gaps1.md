# gaps1: inline asm with memory operands; strncpy, strcat, strrchr

The static census gaps that blocked the most programs: inline asm with memory operands (7 programs, two of
them also `strncpy`) and three C string functions (2 more).

- Inline asm with memory operands (gcc-c-torture pr65053-1, pr65053-2, pr65956, pr85156, pr88904;
  UnitTests/X86 dyn_stack_alloc_realign, dyn_stack_alloc_realign2). CIR gives `"+g"(x)` and `"=g"(x)` as an
  output through a pointer (`=*imr`, `maybe_memory`) tied to an input by its digit, `"+m"(x)` as a memory
  output (`=*m`) with a memory input (`*m`). An empty template, or `nop`, changes no operand, so a tied
  memory output is a store of its input's value through the pointer (`"+g"(x)` writes `x` back,
  `"=g"(x) : "0"(v)` gives `x` the value `v`), placed before the asm (`PState.preOps`); an untied memory
  output and a memory input are left as they are; the register inputs are read as before (`Op.asmTied`,
  `asmMemForm` in the parser). The template `movl $0, $1` of a 32-bit register input and a memory input of
  its type is a store of the first into the second (dyn_stack_alloc_realign). Any other template stays
  `Op.unknown`, and so does an input of another type than its output (gcc's stkalign: `"=g"(x) : "0"(&x)`,
  an `unsigned` given the bytes of a pointer; `g_ptr_into_int` below), as does 990413-2's x87 asm.
- `strncpy` (C11 7.24.2.4), `strcat` (7.24.3.1) and `strrchr` (7.24.5.5) as library models (Shootout's
  strcat; gcc-c-torture string-opt-5; `strncpy` also in dyn_stack_alloc_realign and realign2), recognized
  with their C signatures only. `strncpy` writes n
  characters: those of the source up to its terminator or n of them, then null characters; with n = 0 it
  writes nothing, but its pointers must be valid (7.24.1p2). `strcat` writes the source and its terminator
  from the terminator of the destination's string. Like `strcpy`, both are undefined into a destination too
  short for what they write (7.24.1p1) and between overlapping objects. `strrchr` finds the last occurrence
  as `strchr` finds the first, the terminator for `c` = 0.

Pin census: 1173 of the 1812 programs without a static blocker, against 1164 at next3 648c29b (the nine
programs above; none lost); the 193 dynamic mains as at 648c29b (172 run to their end, 17 UB, 4 timeouts).

## Narrowings

None.

## Test labels changed

`asm_cases.txt`: `u_asm_nop` (UB, a non-empty template) is `t_asm_nop`, expected MATCH. `asm2_cases.txt`:
`u_mem_in`, `u_mem_out`, `u_rw_mem` and `u_rw_g` (UB, memory operands) are `t_mem_in`, `t_mem_out` (which now
returns its operand's object rather than its argument), `t_rw_mem` and `t_rw_g`, expected MATCH. New:
`tests/difftest/gaps1.c` (`CASES=gaps1_cases.txt`, a C source, every case labelled: 15 MATCH, 5 UB: the
overlapping and too short destinations, and the gap `g_ptr_into_int`).
