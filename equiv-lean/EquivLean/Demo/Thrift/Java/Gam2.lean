import EquivLean.Demo.Thrift.Java.Gam

/-!
# Thrift → Java (T4): the callers' contract environment `Γ2` and its validity
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The transport contracts and the varint methods' contracts. -/
def Γ2 (P : Program) (R : TRep) : SpecEnv := fun sig =>
  if sig = rv32Sig then some (rv32SpecA P R)
  else if sig = wv32Sig then some (wv32SpecA P R)
  else (tContracts R).env sig

end EquivLean.Demo.Thrift.Java
