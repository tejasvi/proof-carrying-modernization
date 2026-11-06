import EquivLean.Modernize.Cbtrn02c.Any.JavaRunPL
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH1
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunTac

/-!
# Test harness: `run`'s body against a reduced callee list (only `spaces`)

For trying the segments of `run` before every callee contract is compiled: the reduced list
answers the calls to `spaces` as `runC` does; constructors are inlined in both.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

def spacesSigT : MethodSig := ⟨"Cbtrn02c", .cls "java.lang.String", "spaces", [.prim .int]⟩

def runCT : Contracts := [(spacesSigT, spacesSpec)]

abbrev runBodyT := Gen.Cbtrn02c.«run(Cbtrn02c$DalytranRecord[],Cbtrn02c$CardXrefRecord[],Cbtrn02c$AccountRecord[],Cbtrn02c$TranCatBalRecord[],java.lang.String)»

def RunWPcT (g : G) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog runCT.env 1) runBodyT cuts ((runSpecG g).post g.args σ0) 60 pc fr σ

attribute [irreducible] RunWPcT

end EquivLean.Modernize.Cbtrn02c.Java
