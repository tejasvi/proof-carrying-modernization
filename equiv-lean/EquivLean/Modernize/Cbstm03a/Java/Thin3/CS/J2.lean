import EquivLean.Modernize.Cbstm03a.Java.Thin3.CS.J1

/-!
# CBSTM03A → Java, termination of `createStatement`: the computations up to the address lines

From a virtual cut point to the next: statements 30 … 31 (the `<h3>` line), 44 … 45 (the name builder), 52 … 55
(the name, the address builder), 64 … 70 (the address, the account fields, the first paragraph).
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space fixStr_length grows_split)

attribute [-simp] List.reduceReplicate
attribute [-jsimp] List.take_succ

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

open EquivLean.Modernize.Cbstm03a.Java

/-- The string locals at 32: the `<h3>` line (local 2), the fields, the account id. -/
def K32 : List (Nat × Nat) := (2, 100) :: K16

/-- A builder in local `i` of at most `n` characters. -/
def Bld (i n : Nat) (fr : Frame) (σ : State) : Prop :=
  ∃ d b, fr.get i = some (.ref d) ∧ σ.heap d = some (.builder "java.lang.StringBuilder" b) ∧ b.length ≤ n

/-- The fields used after the name (locals 6 … 13). -/
def K6 : List (Nat × Nat) := [(6, 50), (7, 50), (8, 50), (9, 2), (10, 3), (11, 10), (12, 3), (13, 11)]

/-- The string locals at 56: the name (local 15) and the fields used after it. -/
def K56 : List (Nat × Nat) := (15, 75) :: K6

/-- The texts the rest needs (locals 6, 7, 15 … 19). -/
def KE : List (Nat × Nat) := [(6, 50), (7, 50), (15, 75), (16, 80), (17, 20), (18, 13), (19, 20)]

/-- The string locals at a paragraph or `star` line: the line (local 13) and the texts the rest needs. -/
def KP : List (Nat × Nat) := (13, 100) :: KE

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 30 … 31: the `<h3>` line. -/
theorem j2 (res ls lh : Addr) (a : JStr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K16, SLoc σ fr p.1 p.2) (hbal : BalA a fr)
    (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(32, VA res ls lh σ K32 (fun fr _ => BalA a fr))] (fun _ => True) 8 30 fr σ := by
  jvc [csT, VA, SLoc, K8, K13, K16, K32, BalA, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, fixSpecI,
    StrOk, fixStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 44 … 45: the name builder. -/
theorem j3 (res ls lh : Addr) (a : JStr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K16, SLoc σ fr p.1 p.2) (hbal : BalA a fr)
    (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(46, VA res ls lh σ K16 (fun fr σ => BalA a fr ∧ Bld 23 0 fr σ))] (fun _ => True)
      8 44 fr σ := by
  jvc [csT, VA, SLoc, K8, K13, K16, BalA, Bld, nat_self_ne_add_one, nat_self_ne_add_succ]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 52 … 55: the name, the address builder. -/
theorem j4 (res ls lh : Addr) (a : JStr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K6, SLoc σ fr p.1 p.2) (hbal : BalA a fr)
    (hb : Bld 23 75 fr σ) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(56, VA res ls lh σ K56 (fun fr σ => BalA a fr ∧ Bld 24 0 fr σ))] (fun _ => True)
      16 52 fr σ := by
  jvc [csT, VA, SLoc, K6, K56, BalA, Bld, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, fixSpecI, StrOk,
    fixStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 6000000 in
/-- Statements 64 … 70: the address, the account fields, the first paragraph. -/
theorem j5 (res ls lh : Addr) (a : JStr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K56, SLoc σ fr p.1 p.2) (hbal : BalA a fr)
    (hbv : -9223372036854775808 < (BitVec.ofInt 64 (zonedVal (List.drop 12 (List.take 24 a)))).toInt)
    (hb : Bld 24 80 fr σ) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(71, VA res ls lh σ KP (fun _ _ => True))] (fun _ => True) 28 64 fr σ := by
  jvc [csT, VA, SLoc, K6, K56, KE, KP, BalA, Bld, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, fixSpecI,
    StrOk, fixStr_length, fmtCurrBalSpec, paraSpec, StrNN, paraStr_length, currStr_length]

end EquivLean.Modernize.Cbstm03a.Java.Thin3
