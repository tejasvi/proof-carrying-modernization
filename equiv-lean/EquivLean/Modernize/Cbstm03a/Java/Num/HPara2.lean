import EquivLean.Modernize.Cbstm03a.Java.Num.AppB

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

theorem appStr_len_le (b : JStr) (cap : Int) (src : JStr) (d : Option JStr) (n : Nat) (hb : b.length ≤ n)
    (hc : cap ≤ n) : (appStr b cap src d).length ≤ n := by
  unfold appStr
  split
  · exact hb
  · simp only [List.length_append, List.length_take]
    omega

/-- The builder's texts after the first `k` calls of `app` in `para`. -/
def paraS1 (ps : JStr) : JStr := appStr [] 100 ps (some (JStr.ofString "*"))
def paraS2 (ps fs : JStr) : JStr := appStr (paraS1 ps) 100 fs (some (JStr.ofString "  "))
def paraS3 (ps fs : JStr) : JStr := appStr (paraS2 ps fs) 100 (JStr.ofString "  ") none
def paraS4 (ps fs : JStr) : JStr := appStr (paraS3 ps fs) 100 (JStr.ofString "</p>") (some (JStr.ofString "*"))

def paraStage (ps fs : JStr) : Nat → JStr
  | 0 => []
  | 1 => paraS1 ps
  | 2 => paraS2 ps fs
  | 3 => paraS3 ps fs
  | _ => paraS4 ps fs

theorem paraS1_len (ps : JStr) : (paraS1 ps).length ≤ 100 := appStr_len_le _ _ _ _ 100 (by simp) (by omega)
theorem paraS2_len (ps fs : JStr) : (paraS2 ps fs).length ≤ 100 :=
  appStr_len_le _ _ _ _ 100 (paraS1_len ps) (by omega)
theorem paraS3_len (ps fs : JStr) : (paraS3 ps fs).length ≤ 100 :=
  appStr_len_le _ _ _ _ 100 (paraS2_len ps fs) (by omega)
theorem paraS4_len (ps fs : JStr) : (paraS4 ps fs).length ≤ 100 :=
  appStr_len_le _ _ _ _ 100 (paraS3_len ps fs) (by omega)

theorem paraS1_lt (ps : JStr) : (paraS1 ps).length < 2147483648 := Nat.lt_of_le_of_lt (paraS1_len ps) (by decide)
theorem paraS2_lt (ps fs : JStr) : (paraS2 ps fs).length < 2147483648 :=
  Nat.lt_of_le_of_lt (paraS2_len ps fs) (by decide)
theorem paraS3_lt (ps fs : JStr) : (paraS3 ps fs).length < 2147483648 :=
  Nat.lt_of_le_of_lt (paraS3_len ps fs) (by decide)
theorem paraS4_lt (ps fs : JStr) : (paraS4 ps fs).length < 2147483648 :=
  Nat.lt_of_le_of_lt (paraS4_len ps fs) (by decide)

theorem paraS1_fold (ps : JStr) : appStr [] 100 ps (some (JStr.ofString "*")) = paraS1 ps := rfl
theorem paraS2_fold (ps fs : JStr) : appStr (paraS1 ps) 100 fs (some (JStr.ofString "  ")) = paraS2 ps fs := rfl
theorem paraS3_fold (ps fs : JStr) : appStr (paraS2 ps fs) 100 (JStr.ofString "  ") none = paraS3 ps fs := rfl
theorem paraS4_fold (ps fs : JStr) :
    appStr (paraS3 ps fs) 100 (JStr.ofString "</p>") (some (JStr.ofString "*")) = paraS4 ps fs := rfl

theorem paraS4_eq (ps fs : JStr) : fixStr (paraS4 ps fs) 100 = paraStr ps fs := rfl


/-- After statement `4 + k` (`k` calls of `app` done): the builder `b` (local 0) holds `stg ps fs`, the text after the first `k` calls. -/
def paraAt (stg : JStr → JStr → JStr) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ pv fv, args = [pv, fv] → ∃ (bb pa fa : Addr) (ps fs : JStr), pv = .ref pa ∧ fv = .ref fa ∧
    σ0.heap pa = some (.str ps) ∧ σ0.heap fa = some (.str fs) ∧ σ.heap pa = some (.str ps) ∧
    σ.heap fa = some (.str fs) ∧ ps.length < 2147483648 ∧ fs.length < 2147483648 ∧
    fr.get 0 = some (.ref bb) ∧ fr.get 1 = some pv ∧ fr.get 2 = some fv ∧
    σ.heap bb = some (.builder "java.lang.StringBuilder" (stg ps fs)) ∧
    σ0.next ≤ bb ∧ σ0.next ≤ σ.next ∧
    (∀ x, x < σ0.next → σ.heap x = σ0.heap x) ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ.initOf "Cbstm03a" = .done

def paraInv : Invariants :=
  [(5, fun args σ0 fr σ => paraAt (fun ps _ => paraS1 ps) args σ0 fr σ),
   (6, fun args σ0 fr σ => paraAt paraS2 args σ0 fr σ),
   (7, fun args σ0 fr σ => paraAt paraS3 args σ0 fr σ), (8, fun args σ0 fr σ => paraAt paraS4 args σ0 fr σ)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
set_option jimple.modelContracts true in
theorem para_vc : MethodVC Gen.prog paraCalleesB.env 0 paraRef paraSpec paraInv 40 := by
  jverify [paraSpec, paraInv, paraAt, paraCalleesB, appSig, appSpecB, bText, fixSig, fixSpecI, StrNN, StrOk, argText,
    strOf, Keeps, Grows, paraS4_eq, paraS1_fold, paraS2_fold, paraS3_fold, paraS4_fold]
  all_goals first
    | with_reducible exact paraS1_lt _
    | with_reducible exact paraS2_lt _ _
    | with_reducible exact paraS3_lt _ _
    | with_reducible exact paraS4_lt _ _

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.para_vc
