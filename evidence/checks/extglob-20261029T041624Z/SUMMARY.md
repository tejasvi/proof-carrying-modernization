RESULT: CONFIRMED. Reading a global that the unit only declares (extern int, extern int[4]; defined in another unit when
linked natively) gives 0 for the object on cirrun at all five builds run (266d1ed, 28e2380, ffab71e, e6ac99a, 424e821):
t_ext_scalar 1 and t_ext_array 1 with k = 1, where the linked native program gives 42 and 31. A global defined in the unit
matches native (8). The model runs one unit and fills declared-only objects with zeros instead of refusing them.
# d0 check of the C maintainer session's report (written 2026-10-29T04:16:37Z by date -u): probe/use.c, def.c, drv.c; results.txt; native gcc -O0 with def.c
# linked; CIR of use.c alone from the toolchain clang; frozen cirrun builds.
