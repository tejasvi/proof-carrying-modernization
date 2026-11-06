import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH4a
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunPL

/-!
# CBTRN02C → Java: the processing timestamp as text
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- What `db2Timestamp` returns for the clock text is the text of COBOL's timestamp. -/
theorem db2J_cp037 (c : List UInt8) : db2J (cp037Str c) = cp037Str (CardDemo.Cbtrn02c.db2ts c) := by
  have h1 : cp037Unit 96 = 45#16 := by decide +kernel
  have h2 : cp037Unit 75 = 46#16 := by decide +kernel
  have h3 : cp037Unit 240 = 48#16 := by decide +kernel
  simp only [db2J, CardDemo.Cbtrn02c.db2ts, cp037Str, List.map_append, List.map_take,
    List.map_drop, List.map_cons, List.map_nil, h1, h2, h3, List.drop_take, List.append_assoc,
    List.singleton_append, List.cons_append]

end EquivLean.Modernize.Cbtrn02c.Java
