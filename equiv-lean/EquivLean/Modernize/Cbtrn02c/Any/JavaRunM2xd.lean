import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM2xs
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunTac

/-!
# CBTRN02C → Java: `abend` with status 22 (`displayIoStatus` inlined)
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem abend22i_vc : MethodVC Gen.prog (fun _ => none) 2 abendRef abendSpec22 [] 80 := by
  jverify [abendSpec22, Grows, FrameS, jstrLitT, argText, listOf, fieldsOf, strOfV, refField,
    evalDynamic, concatRecipe, Native.valueOfArg, valueOfObj_eq, valueOfObjN_ref, Native.nObjStr,
    Native.primStr, JType.isRef]

end EquivLean.Modernize.Cbtrn02c.Java
