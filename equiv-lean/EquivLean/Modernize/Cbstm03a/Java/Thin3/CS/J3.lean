import EquivLean.Modernize.Cbstm03a.Java.Thin3.CS.J2

/-!
# CBSTM03A → Java, termination of `createStatement`: the paragraph and `star` lines, the statement lines

From a virtual cut point to the next: statements 72, 74, 76 (`para`), 87, 89, 91 (`star`), 111 … 113, 115 … 116,
118 … 119, 123 … 125, 128 … 129, 131 … 132, 134 … 135, 138 … 140, 143 … 144 (the statement lines: `repeat`,
`spaces`, `fix`, concatenations), and the `return` (147).
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space fixStr_length grows_split)

attribute [-simp] List.reduceReplicate
attribute [-jsimp] List.take_succ

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

open EquivLean.Modernize.Cbstm03a.Java

def K114 : List (Nat × Nat) := [(3, 80), (6, 50), (7, 50), (16, 80), (17, 20), (18, 13), (19, 20), (21, 80)]
def K115 : List (Nat × Nat) := [(6, 50), (7, 50), (16, 80), (17, 20), (18, 13), (19, 20), (21, 80)]
def K117 : List (Nat × Nat) := [(6, 80), (7, 50), (16, 80), (17, 20), (18, 13), (19, 20), (21, 80)]
def K118 : List (Nat × Nat) := [(7, 50), (16, 80), (17, 20), (18, 13), (19, 20), (21, 80)]
def K120 : List (Nat × Nat) := [(7, 80), (16, 80), (17, 20), (18, 13), (19, 20), (21, 80)]
def K123 : List (Nat × Nat) := [(17, 20), (18, 13), (19, 20), (21, 80)]
def K126 : List (Nat × Nat) := [(7, 80), (17, 20), (18, 13), (19, 20), (21, 80)]
def K130 : List (Nat × Nat) := [(7, 80), (18, 13), (19, 20), (21, 80)]
def K131 : List (Nat × Nat) := [(18, 13), (19, 20), (21, 80)]
def K133 : List (Nat × Nat) := [(2, 80), (19, 20), (21, 80)]
def K134 : List (Nat × Nat) := [(19, 20), (21, 80)]
def K136 : List (Nat × Nat) := [(1, 80), (21, 80)]
def K138 : List (Nat × Nat) := [(21, 80)]
def K145 : List (Nat × Nat) := [(1, 80), (21, 80)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statement 72: a paragraph or `star` line. -/
theorem j72 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(73, VA res ls lh σ KP (fun _ _ => True))] (fun _ => True) 4 72 fr σ := by
  jvc [csT, VA, SLoc, KE, KP, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, paraSpec, starSpec, StrNN,
    paraStr_length, starStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statement 74: a paragraph or `star` line. -/
theorem j74 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(75, VA res ls lh σ KP (fun _ _ => True))] (fun _ => True) 4 74 fr σ := by
  jvc [csT, VA, SLoc, KE, KP, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, paraSpec, starSpec, StrNN,
    paraStr_length, starStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statement 76: a paragraph or `star` line. -/
theorem j76 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(77, VA res ls lh σ KP (fun _ _ => True))] (fun _ => True) 4 76 fr σ := by
  jvc [csT, VA, SLoc, KE, KP, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, paraSpec, starSpec, StrNN,
    paraStr_length, starStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statement 87: a paragraph or `star` line. -/
theorem j87 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(88, VA res ls lh σ KP (fun _ _ => True))] (fun _ => True) 4 87 fr σ := by
  jvc [csT, VA, SLoc, KE, KP, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, paraSpec, starSpec, StrNN,
    paraStr_length, starStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statement 89: a paragraph or `star` line. -/
theorem j89 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(90, VA res ls lh σ KP (fun _ _ => True))] (fun _ => True) 4 89 fr σ := by
  jvc [csT, VA, SLoc, KE, KP, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, paraSpec, starSpec, StrNN,
    paraStr_length, starStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statement 91: a paragraph or `star` line. -/
theorem j91 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(92, VA res ls lh σ KP (fun _ _ => True))] (fun _ => True) 4 91 fr σ := by
  jvc [csT, VA, SLoc, KE, KP, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, paraSpec, starSpec, StrNN,
    paraStr_length, starStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 111 … 113: a statement line. -/
theorem j111 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(114, VA res ls lh σ K114 (fun _ _ => True))] (fun _ => True) 10 111 fr σ := by
  jvc [csT, VA, SLoc, KE, K114, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, spacesSpecI, repeatSpec,
    fixSpecI, StrOk, fixStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 115 … 116: a statement line. -/
theorem j115 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K115, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(117, VA res ls lh σ K117 (fun _ _ => True))] (fun _ => True) 8 115 fr σ := by
  jvc [csT, VA, SLoc, K115, K117, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, spacesSpecI, repeatSpec,
    fixSpecI, StrOk, fixStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 118 … 119: a statement line. -/
theorem j118 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K118, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(120, VA res ls lh σ K120 (fun _ _ => True))] (fun _ => True) 8 118 fr σ := by
  jvc [csT, VA, SLoc, K118, K120, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, spacesSpecI, repeatSpec,
    fixSpecI, StrOk, fixStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 123 … 125: a statement line. -/
theorem j123 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K123, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(126, VA res ls lh σ K126 (fun _ _ => True))] (fun _ => True) 10 123 fr σ := by
  jvc [csT, VA, SLoc, K123, K126, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, spacesSpecI, repeatSpec,
    fixSpecI, StrOk, fixStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 128 … 129: a statement line. -/
theorem j128 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K123, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(130, VA res ls lh σ K130 (fun _ _ => True))] (fun _ => True) 8 128 fr σ := by
  jvc [csT, VA, SLoc, K123, K130, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, spacesSpecI, repeatSpec,
    fixSpecI, StrOk, fixStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 131 … 132: a statement line. -/
theorem j131 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K131, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(133, VA res ls lh σ K133 (fun _ _ => True))] (fun _ => True) 8 131 fr σ := by
  jvc [csT, VA, SLoc, K131, K133, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, spacesSpecI, repeatSpec,
    fixSpecI, StrOk, fixStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 134 … 135: a statement line. -/
theorem j134 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K134, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(136, VA res ls lh σ K136 (fun _ _ => True))] (fun _ => True) 8 134 fr σ := by
  jvc [csT, VA, SLoc, K134, K136, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, spacesSpecI, repeatSpec,
    fixSpecI, StrOk, fixStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 138 … 140: a statement line. -/
theorem j138 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K138, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(141, VA res ls lh σ K136 (fun _ _ => True))] (fun _ => True) 10 138 fr σ := by
  jvc [csT, VA, SLoc, K138, K136, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, spacesSpecI, repeatSpec,
    fixSpecI, StrOk, fixStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
set_option jimple.maxHeartbeats 4000000 in
/-- Statements 143 … 144: a statement line. -/
theorem j143 (res ls lh : Addr) (fr : Frame) (σ : State) (fs : List (FieldKey × Value))
    (xs xs2 : List Value) (m m2 : Nat) (hres : σ.heap res = some (.plain resC fs))
    (hls : σ.heap ls = some (.list .arrayList xs m)) (hlh : σ.heap lh = some (.list .arrayList xs2 m2))
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K138, SLoc σ fr p.1 p.2) (hini : σ.initOf "Cbstm03a" = .done) :
    bodyWP Gen.prog HT csBody [(145, VA res ls lh σ K145 (fun _ _ => True))] (fun _ => True) 8 143 fr σ := by
  jvc [csT, VA, SLoc, K138, K145, nat_self_ne_add_one, nat_self_ne_add_succ, grows_split, spacesSpecI, repeatSpec,
    fixSpecI, StrOk, fixStr_length]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- Statement 147: `return`. -/
theorem j147 (fr : Frame) (σ : State) : bodyWP Gen.prog HT csBody [] (fun _ => True) 2 147 fr σ := by
  jvc [csT]

end EquivLean.Modernize.Cbstm03a.Java.Thin3
