import EquivLean.Modernize.Cbstm03a.Java.Mem.RdVC
import EquivLean.Modernize.Cbstm03a.Java.Mem.Rd_past
import EquivLean.Modernize.Cbstm03a.Java.Mem.Rd_pre
import EquivLean.Modernize.Cbstm03a.Java.Mem.Rd_n38
import EquivLean.Modernize.Cbstm03a.Java.Mem.Rd_s38

/-! # CBSTM03A → Java: `memRead`'s verification conditions, all segments proved -/

open Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Mem

theorem memRead_vc : MethodVC Gen.prog rdCallees.env 0 memReadRef memReadSpec memReadInv 120 :=
  memRead_vc_of rd_past rd_pre rd_n38 rd_s38

end EquivLean.Modernize.Cbstm03a.Java.Mem

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mem.memRead_vc
