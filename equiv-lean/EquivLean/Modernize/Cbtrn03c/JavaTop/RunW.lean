import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib2

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `run`'s callees and paths
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

def runCallees : Contracts :=
  [(spacesSig, spacesSpecT), (blankTranSig, blankTranSpecT), (compareEbcdicSig, compareEbcdicSpecC),
   (processDetailSig, processDetailSpecM), (processEndSig, processEndSpecM)]

/-- The paths of `run` from statement `pc` (constructors inlined: depth 1). -/
def runWP (a1 a2 a3 a4 a5 : Addr) (vals1 vals2 vals3 vals4 vals5 : Recs) (args : List Value)
    (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBody
    ((runInv a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5).inst args σ0)
    ((runSpecG a1 a2 a3 a4 a5 vals1 vals2 vals3 vals4 vals5).post args σ0) 200 pc fr σ

/-- `Model.run` with a date record: the loop's outcome from the entry's state. -/
theorem run_parm (vals1 vals2 vals3 vals4 : Recs) (d : Rec) (rest : Recs) :
    Model.run vals1 vals2 vals3 vals4 (d :: rest) =
      fin (Model.loop vals2 vals3 vals4 d vals1 Model.tran0 (sEntry (d :: rest))) := by
  simp only [Model.run, sEntry]
  cases Model.loop vals2 vals3 vals4 d vals1 Model.tran0 _ <;> rfl

theorem run_noparm (vals1 vals2 vals3 vals4 : Recs) :
    Model.run vals1 vals2 vals3 vals4 [] = Model.out (sEntry []) false := rfl

end EquivLean.Modernize.Cbtrn03c.Java.Top

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

theorem cp037Str_take (p : List UInt8) (n : Nat) : (cp037Str p).take n = cp037Str (p.take n) := by
  simp [cp037Str, List.map_take]

theorem cp037Str_length (p : List UInt8) : (cp037Str p).length = p.length := by
  simp [cp037Str]

theorem ebcBytes_cp037 (p : List UInt8) : ebcBytes (cp037Str p) = p := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    simp only [ebcBytes, cp037Str, List.map_cons, List.cons.injEq] at ih ⊢
    refine ⟨?_, ih⟩
    have h1 : (cp037Unit b).toNat = cp037Code b := by
      simp only [cp037Unit, BitVec.toNat_ofNat]
      have := cp037Code_lt b
      simp only [cp037Code] at this ⊢
      omega
    rw [h1, ebc_cp037]

end EquivLean.Modernize.Cbtrn03c.Java.Top

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

theorem dOf_cons (d : List EquivLean.Cobol.Rec.FVal) (rest : List (List EquivLean.Cobol.Rec.FVal)) :
    dOf (d :: rest) = d := rfl
theorem dOf_nil : dOf [] = d0 := rfl

end EquivLean.Modernize.Cbtrn03c.Java.Top
