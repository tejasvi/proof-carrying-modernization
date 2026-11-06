import Jimple

/-!
Generated input: Soot 4.7.1 Jimple of `examples/java/search_old/Search.java` (before the change:
`return true` inside an index loop) and `examples/java/search_new/Search.java` (after: an enhanced
`for` with a flag and `break`), each compiled by `javac --release 17`
(`examples/java/build_jimple.sh search_old`, `… search_new`).  Paths are relative to the
repository root.
-/

jimple_import "EquivLean/Demo/Gen/Jimple/search_old" as EquivLean.Gen.SearchOld
jimple_import "EquivLean/Demo/Gen/Jimple/search_new" as EquivLean.Gen.SearchNew
