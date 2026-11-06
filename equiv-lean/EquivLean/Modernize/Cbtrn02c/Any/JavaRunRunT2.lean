import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunT
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunPL3
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunCT

/-!
# Test harness 2: `run`'s body against `spaces` and the record constructors
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

def runCT2 : Contracts :=
  [(spacesSigT, spacesSpec), (ctorXRSig, ctorXRSpec), (ctorACSig, ctorACSpec),
   (ctorTCSig, ctorTCSpec), (ctorTRSig, ctorTRSpec)]

def RunWPcT2 (g : G) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog runCT2.env 1) runBodyT cuts ((runSpecG g).post g.args σ0) 60 pc fr σ

attribute [irreducible] RunWPcT2

end EquivLean.Modernize.Cbtrn02c.Java
