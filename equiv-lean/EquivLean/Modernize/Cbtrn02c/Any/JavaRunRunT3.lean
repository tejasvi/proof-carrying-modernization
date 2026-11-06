import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunT2
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunF

/-!
# Test harness 3: `run`'s body against `spaces`, the copies and the record constructors
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

def copyAccountSigT : MethodSig :=
  ⟨"Cbtrn02c", .cls "Cbtrn02c$AccountRecord", "copyAccount", [.cls "Cbtrn02c$AccountRecord"]⟩
def copyTcatSigT : MethodSig :=
  ⟨"Cbtrn02c", .cls "Cbtrn02c$TranCatBalRecord", "copyTcat", [.cls "Cbtrn02c$TranCatBalRecord"]⟩

def runCT3 : Contracts :=
  [(copyAccountSigT, copyAccountSpecF), (copyTcatSigT, copyTcatSpecF), (spacesSigT, spacesSpec),
   (ctorXRSig, ctorXRSpec), (ctorACSig, ctorACSpec), (ctorTCSig, ctorTCSpec), (ctorTRSig, ctorTRSpec)]

def RunWPcT3 (g : G) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog runCT3.env 1) runBodyT cuts ((runSpecG g).post g.args σ0) 60 pc fr σ

attribute [irreducible] RunWPcT3

end EquivLean.Modernize.Cbtrn02c.Java
