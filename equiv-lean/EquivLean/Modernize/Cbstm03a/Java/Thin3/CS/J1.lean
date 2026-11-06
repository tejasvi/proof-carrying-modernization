import EquivLean.Modernize.Cbstm03a.Java.Thin3.CS.Seg

/-!
# CBSTM03A → Java, termination of `createStatement`: statements 0 … 18

The parameters, the substrings of the customer and account texts, `currBal` (`decodeZoned`), and the first
statement line (`repeat`, concatenation), up to the virtual cut point 19 (the first `stmt`).
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space fixStr_length grows_split)

attribute [-simp] List.reduceReplicate
attribute [-jsimp] List.take_succ

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

open EquivLean.Modernize.Cbstm03a.Java

/-- The first five fields of the customer text (locals 3 … 7). -/
def K8 : List (Nat × Nat) := [(3, 25), (4, 25), (5, 25), (6, 50), (7, 50)]

/-- The customer text's fields (locals 3 … 12, index and length bound). -/
def K13 : List (Nat × Nat) := K8 ++ [(8, 50), (9, 2), (10, 3), (11, 10), (12, 3)]

/-- The fields and the account id (local 13). -/
def K16 : List (Nat × Nat) := K13 ++ [(13, 11)]

/-- The string locals at 19: the first statement line (local 2), the fields, the account id. -/
def K19 : List (Nat × Nat) := (2, 80) :: K16

/-- `currBal` in local 0, from the account text `a`. -/
def BalA (a : JStr) (fr : Frame) : Prop :=
  fr.get 0 = some (.long (BitVec.ofInt 64 (zonedVal (List.drop 12 (List.take 24 a)))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 0 … 7: the parameters and the first five fields of the customer text. -/
theorem j1a (res ls lh xc xa : Addr) (c a : JStr) (σ0 : State) (fs : List (FieldKey × Value)) (xs xs2 : List Value)
    (m m2 : Nat) (hres : σ0.heap res = some (.plain resC fs)) (hls : σ0.heap ls = some (.list .arrayList xs m))
    (hlh : σ0.heap lh = some (.list .arrayList xs2 m2)) (hxc : σ0.heap xc = some (.str c))
    (hxa : σ0.heap xa = some (.str a)) (hc : 332 ≤ c.length) (fr : Frame)
    (hfr : Frame.init true [.ref res, .ref xc, .ref xa] = fr)
    (hini : σ0.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody
      [(8, VA res ls lh σ0 K8 (fun fr σ => fr.get 1 = some (.ref xc) ∧ fr.get 2 = some (.ref xa) ∧
        σ.heap xc = some (.str c) ∧ σ.heap xa = some (.str a)))]
      (fun _ => True) 20 0 fr σ0 := by
  subst hfr
  jvc [csT, VA, SLoc, K8, nat_self_ne_add_one, nat_self_ne_add_succ]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 8 … 12: the other fields of the customer text. -/
theorem j1a2 (res ls lh xc xa : Addr) (c a : JStr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K8, SLoc σ fr p.1 p.2) (h1 : fr.get 1 = some (.ref xc))
    (h2 : fr.get 2 = some (.ref xa)) (hxc : σ.heap xc = some (.str c)) (hxa : σ.heap xa = some (.str a))
    (hc : 332 ≤ c.length)
    (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody
      [(13, VA res ls lh σ K13 (fun fr σ => fr.get 2 = some (.ref xa) ∧ σ.heap xa = some (.str a)))] (fun _ => True)
      10 8 fr σ := by
  jvc [csT, VA, SLoc, K8, K13, nat_self_ne_add_one, nat_self_ne_add_succ]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 13 … 15: the account id, the balance text, `currBal`. -/
theorem j1b (res ls lh xa : Addr) (a : JStr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K13, SLoc σ fr p.1 p.2)
    (h2 : fr.get 2 = some (.ref xa)) (hxa : σ.heap xa = some (.str a)) (ha : 24 ≤ a.length)
    (ha' : a.length < 2147483648) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(16, VA res ls lh σ K16 (fun fr _ => BalA a fr))] (fun _ => True) 10 13 fr σ := by
  jvc [csT, VA, SLoc, K8, K13, K16, BalA, nat_self_ne_add_one, nat_self_ne_add_succ, decodeZonedSpec, StrNN,
    argText, strOf]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 16 … 18: the first statement line. -/
theorem j1c (res ls lh : Addr) (a : JStr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K16, SLoc σ fr p.1 p.2) (hbal : BalA a fr)
    (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(19, VA res ls lh σ K19 (fun fr _ => BalA a fr))] (fun _ => True) 10 16 fr σ := by
  jvc [csT, VA, SLoc, K8, K13, K16, K19, BalA, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, repeatSpec]

end EquivLean.Modernize.Cbstm03a.Java.Thin3
