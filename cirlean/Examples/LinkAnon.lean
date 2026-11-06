import CIR
import Examples.GenL.AnonLinked
import Examples.GenL.AnonNames

/-!
  Linking units with anonymous records (`cir2lean --link`).

  `Examples/cpp/anonlink_a.cpp` and `anonlink_b.cpp`: clang numbers anonymous records per
  translation unit, so each unit has an `anon.0` union of its own struct, of different layouts
  (`int`/`float` in a, `long`/`double` in b), and an `anon.1`, std::string's union. The linker
  names an anonymous record that a named record holds after that member (std::string's union, one
  record) and the others after their structure and member names, so the two unions stay apart
  (linking failed before: "record anon.0: different layouts in two units"). `a_value` calls
  `b_value` across the units; native execution of `a_value(3)` gives 17.

  `Examples/cpp/anonname_a.c` and `anonname_b.c`: free-standing anonymous structs of one layout,
  `{int, int}`. `pa` and `pb` have different member names (x, y and u, v), so they stay two types
  (C11 6.2.7p1); `same_a` and `same_b` have the same names (p, q), so they are one. Matching by
  structure alone merged `pa`'s type with `pb`'s. Native execution of `ua()` gives 36.
-/

open CIR

namespace Examples.LinkAnon

-- three anonymous records: the unions of `A1` and `B1`, and std::string's union
#guard (Examples.GenL.AnonLinked.module.records.filter (·.name.startsWith "anon.")).length == 3

/-- `a_value(3) = 3 + 5 + b_value(3) = 3 + 5 + (6 + 2 + 1) = 17`, as natively. -/
theorem a_value_ok :
    Returns Examples.GenL.AnonLinked.ctx "_Z7a_valuei" [.int 3] Examples.GenL.AnonLinked.module.initMem
      (fun r _ => r = some (.int 17)) := by
  cir_kernel

-- three anonymous records: `pa`'s, `pb`'s, and the one of `same_a` and `same_b`
#guard (Examples.GenL.AnonNames.module.records.filter (·.name.startsWith "anon.")).length == 3

-- `pa` and `pb` have different types, `same_a` and `same_b` one
#guard
  let ty (s : String) : Option Ty := (Examples.GenL.AnonNames.module.globals.find? (·.sym == s)).map (·.ty)
  !(ty "pa" == ty "pb") && ty "same_a" == ty "same_b"

/-- `ua() = 1 + 2 + 3 + 4 + ub() = 10 + (5 + 6 + 7 + 8) = 36`, as natively. -/
theorem ua_ok :
    Returns Examples.GenL.AnonNames.ctx "ua" [] Examples.GenL.AnonNames.module.initMem
      (fun r _ => r = some (.int 36)) := by
  cir_kernel

end Examples.LinkAnon
