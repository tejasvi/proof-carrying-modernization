import EquivLean.Modernize.Cbstm03a.Java.Num.HPara2

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

theorem appStr_len_le' (b : JStr) (cap : Int) (src : JStr) (d : Option JStr) (n : Nat) (hb : b.length ≤ n)
    (hc : cap ≤ n) : (appStr b cap src d).length ≤ n := by
  unfold appStr
  split
  · exact hb
  · simp only [List.length_append, List.length_take]
    omega

/-- The builder's texts after the first `k` calls of `app` in `star`. -/
def starS1 (ps : JStr) : JStr := appStr [] 100 ps (some (JStr.ofString "*"))
def starS2 (ps fs : JStr) : JStr := appStr (starS1 ps) 100 fs (some (JStr.ofString "*"))
def starS3 (ps fs : JStr) : JStr := appStr (starS2 ps fs) 100 (JStr.ofString "</p>") (some (JStr.ofString "*"))

def starStage (ps fs : JStr) : Nat → JStr
  | 0 => []
  | 1 => starS1 ps
  | 2 => starS2 ps fs
  | _ => starS3 ps fs

theorem starS1_len (ps : JStr) : (starS1 ps).length ≤ 100 := appStr_len_le' _ _ _ _ 100 (by simp) (by omega)
theorem starS2_len (ps fs : JStr) : (starS2 ps fs).length ≤ 100 :=
  appStr_len_le' _ _ _ _ 100 (starS1_len ps) (by omega)
theorem starS3_len (ps fs : JStr) : (starS3 ps fs).length ≤ 100 :=
  appStr_len_le' _ _ _ _ 100 (starS2_len ps fs) (by omega)

theorem starS1_lt (ps : JStr) : (starS1 ps).length < 2147483648 := Nat.lt_of_le_of_lt (starS1_len ps) (by decide)
theorem starS2_lt (ps fs : JStr) : (starS2 ps fs).length < 2147483648 :=
  Nat.lt_of_le_of_lt (starS2_len ps fs) (by decide)
theorem starS3_lt (ps fs : JStr) : (starS3 ps fs).length < 2147483648 :=
  Nat.lt_of_le_of_lt (starS3_len ps fs) (by decide)

theorem starS1_fold (ps : JStr) : appStr [] 100 ps (some (JStr.ofString "*")) = starS1 ps := rfl
theorem starS2_fold (ps fs : JStr) : appStr (starS1 ps) 100 fs (some (JStr.ofString "*")) = starS2 ps fs := rfl
theorem starS3_fold (ps fs : JStr) :
    appStr (starS2 ps fs) 100 (JStr.ofString "</p>") (some (JStr.ofString "*")) = starS3 ps fs := rfl

theorem starS3_eq (ps fs : JStr) : fixStr (starS3 ps fs) 100 = starStr ps fs := rfl


/-- After statement `4 + k` (`k` calls of `app` done): the builder `b` (local 0) holds `stg ps fs`, the text after the first `k` calls. -/
def starAt (stg : JStr → JStr → JStr) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ pv fv, args = [pv, fv] → ∃ (bb pa fa : Addr) (ps fs : JStr), pv = .ref pa ∧ fv = .ref fa ∧
    σ0.heap pa = some (.str ps) ∧ σ0.heap fa = some (.str fs) ∧ σ.heap pa = some (.str ps) ∧
    σ.heap fa = some (.str fs) ∧ ps.length < 2147483648 ∧ fs.length < 2147483648 ∧
    fr.get 0 = some (.ref bb) ∧ fr.get 1 = some pv ∧ fr.get 2 = some fv ∧
    σ.heap bb = some (.builder "java.lang.StringBuilder" (stg ps fs)) ∧
    σ0.next ≤ bb ∧ σ0.next ≤ σ.next ∧
    (∀ x, x < σ0.next → σ.heap x = σ0.heap x) ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ.initOf "Cbstm03a" = .done

def starInv : Invariants :=
  [(5, fun args σ0 fr σ => starAt (fun ps _ => starS1 ps) args σ0 fr σ),
   (6, fun args σ0 fr σ => starAt starS2 args σ0 fr σ),
   (7, fun args σ0 fr σ => starAt starS3 args σ0 fr σ)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
set_option jimple.modelContracts true in
theorem star_vc : MethodVC Gen.prog paraCalleesB.env 0 starRef starSpec starInv 40 := by
  jverify [starSpec, starInv, starAt, paraCalleesB, appSig, appSpecB, bText, fixSig, fixSpecI, StrNN, StrOk, argText,
    strOf, Keeps, Grows, starS3_eq, starS1_fold, starS2_fold, starS3_fold]
  all_goals first
    | with_reducible exact starS1_lt _
    | with_reducible exact starS2_lt _ _
    | with_reducible exact starS3_lt _ _

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.star_vc
