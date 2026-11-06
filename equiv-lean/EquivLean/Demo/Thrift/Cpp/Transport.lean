import CIR
import EquivLean.Demo.Gen.Cir.Thrift.ProtoTT.Types

open CIR Lean Meta Simp EquivLean.Demo.Gen.Cir.Thrift.ProtoTT

namespace EquivLean.Demo.Thrift.Cpp

/-- The record declarations of `TCompactProtocolT<TTransport>`, its base classes, and its field/collection headers. -/
structure ProtoRecords (ctx : Ctx) : Prop where
  proto : ctx.record? "apache::thrift::protocol::TCompactProtocolT<apache::thrift::transport::TTransport>" =
    some rec_apache_thrift_protocol_TCompactProtocolT_apache_thrift_transport_TTransp
  vproto : ctx.record? "apache::thrift::protocol::TVirtualProtocol<apache::thrift::protocol::TCompactProtocolT<apache::thrift::transport::TTransport>, apache::thrift::protocol::TProtocolDefaults>.base" =
    some rec_apache_thrift_protocol_TVirtualProtocol_apache_thrift_protocol_TCompactP
  pdef : ctx.record? "apache::thrift::protocol::TProtocolDefaults.base" =
    some rec_apache_thrift_protocol_TProtocolDefaults_base
  pbase : ctx.record? "apache::thrift::protocol::TProtocol.base" =
    some rec_apache_thrift_protocol_TProtocol_base
  anon0 : ctx.record? "anon.0" = some rec_anon_0
  anon1 : ctx.record? "anon.1" = some rec_anon_1
  tlist : ctx.record? "apache::thrift::protocol::TList" = some rec_apache_thrift_protocol_TList
  tset : ctx.record? "apache::thrift::protocol::TSet" = some rec_apache_thrift_protocol_TSet

def symWrite : String := "_ZN6apache6thrift9transport10TTransport5writeEPKhj"

def bytesOf (vs : List Val) (k len : Nat) : List Nat :=
  (List.range len).map fun i => match vs[k + i]? with | some (.int x) => x.toNat | _ => 0

structure WriteContract (ctx : Ctx) (tp : Ptr) (Fp : Nat → Prop) (sinkOf : Mem → List Nat) : Prop where
  records : ProtoRecords ctx
  stable : ∀ m m', (∀ b, Fp b → m'.blocks b = m.blocks b) → sinkOf m' = sinkOf m
  write : ∀ (m : Mem) (b : Nat) (kd : BlockKind) (N : Nat) (vs : List Val) (k : Nat) (len : Int), ¬ Fp b →
    m.blocks b = some ⟨kd, true, .array (.int false 8) N, .arr vs⟩ → 0 ≤ len → k + len.toNat ≤ N →
    Returns ctx symWrite [.ptr tp, .ptr (.loc b [.idx k]), .int len] m
      (fun r m' => r = none ∧ sinkOf m' = sinkOf m ++ bytesOf vs k len.toNat ∧ m.next ≤ m'.next ∧
        ∀ b', ¬ Fp b' → b' < m.next → m'.blocks b' = m.blocks b')
  write1 : ∀ (m : Mem) (b : Nat) (kd : BlockKind) (s : Bool) (c : Int), ¬ Fp b →
    m.blocks b = some ⟨kd, true, .int s 8, .int c⟩ →
    Returns ctx symWrite [.ptr tp, .ptr (.loc b []), .int 1] m
      (fun r m' => r = none ∧ sinkOf m' = sinkOf m ++ [(c % 256).toNat] ∧ m.next ≤ m'.next ∧
        ∀ b', ¬ Fp b' → b' < m.next → m'.blocks b' = m.blocks b')

def symReadAll : String := "_ZN6apache6thrift9transport10TTransport7readAllEPhj"
def symBorrow : String := "_ZN6apache6thrift9transport10TTransport6borrowEPhPj"
def symConsume : String := "_ZN6apache6thrift9transport10TTransport7consumeEj"

structure ReadContract (ctx : Ctx) (tp : Ptr) (Fp : Nat → Prop) (srcOf : Mem → List Nat) : Prop where
  records : ProtoRecords ctx
  stable : ∀ m m', (∀ b, Fp b → m'.blocks b = m.blocks b) → srcOf m' = srcOf m
  bytes : ∀ m c, c ∈ srcOf m → c < 256
  readAll1 : ∀ (m : Mem) (b : Nat) (kd : BlockKind) (v : Val), ¬ Fp b →
    kd ≠ .readonly → m.blocks b = some ⟨kd, true, .int false 8, v⟩ → srcOf m ≠ [] →
    Returns ctx symReadAll [.ptr tp, .ptr (.loc b []), .int 1] m
      (fun r m' => r = some (.int 1) ∧ m'.blocks b = some ⟨kd, true, .int false 8, .int ((srcOf m).headD 0)⟩ ∧
        srcOf m' = (srcOf m).tail ∧ m.next ≤ m'.next ∧
        ∀ b', ¬ Fp b' → b' ≠ b → b' < m.next → m'.blocks b' = m.blocks b')
  readAll1a : ∀ (m : Mem) (b : Nat) (kd : BlockKind) (N : Nat) (vs : List Val) (k : Nat), ¬ Fp b →
    kd ≠ .readonly → m.blocks b = some ⟨kd, true, .array (.int false 8) N, .arr vs⟩ → k < vs.length →
    srcOf m ≠ [] →
    Returns ctx symReadAll [.ptr tp, .ptr (.loc b [.idx k]), .int 1] m
      (fun r m' => r = some (.int 1) ∧
        m'.blocks b = some ⟨kd, true, .array (.int false 8) N, .arr (vs.set k (.int ((srcOf m).headD 0)))⟩ ∧
        srcOf m' = (srcOf m).tail ∧ m.next ≤ m'.next ∧
        ∀ b', ¬ Fp b' → b' ≠ b → b' < m.next → m'.blocks b' = m.blocks b')
  borrow : ∀ (m : Mem) (bb : Nat) (kb : BlockKind) (N : Nat) (vb : List Val) (bl : Nat) (kl : BlockKind)
      (L0 : Int), ¬ Fp bb → ¬ Fp bl → bb ≠ bl → kb ≠ .readonly → kl ≠ .readonly →
    m.blocks bb = some ⟨kb, true, .array (.int false 8) N, .arr vb⟩ →
    m.blocks bl = some ⟨kl, true, .int false 32, .int L0⟩ →
    Returns ctx symBorrow [.ptr tp, .ptr (.loc bb [.idx 0]), .ptr (.loc bl [])] m
      (fun r m' => m.next ≤ m'.next ∧ (∀ b', ¬ Fp b' → b' ≠ bb → b' ≠ bl → b' < m.next → m'.blocks b' = m.blocks b') ∧
        srcOf m' = srcOf m ∧
        (r = some (.ptr .null) ∨
          ∃ (b' k' L : Nat) (kd' : BlockKind) (N' : Nat) (vs' : List Val),
            r = some (.ptr (.loc b' [.idx k'])) ∧ L0 ≤ L ∧ L ≤ (srcOf m).length ∧ (Fp b' ∨ b' = bb) ∧
            m'.blocks b' = some ⟨kd', true, .array (.int false 8) N', .arr vs'⟩ ∧ k' + L ≤ vs'.length ∧
            ∀ i, i < L → vs'[k' + i]? = some (.int ((srcOf m).getD i 0))))
  consume : ∀ (m : Mem) (n : Int), 0 ≤ n → n.toNat ≤ (srcOf m).length →
    Returns ctx symConsume [.ptr tp, .int n] m
      (fun r m' => r = none ∧ srcOf m' = (srcOf m).drop n.toNat ∧ m.next ≤ m'.next ∧
        ∀ b', ¬ Fp b' → b' < m.next → m'.blocks b' = m.blocks b')

def findProtoRecords? (ctx : Expr) : MetaM (Option Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := d.type.consumeMData
    if ty.isAppOfArity ``ProtoRecords 1 && ty.appArg! == ctx then
      return some (mkFVar d.fvarId)
    if ty.isAppOfArity ``WriteContract 4 && ty.getArg! 0 == ctx then
      return some (mkProj ``WriteContract 0 (mkFVar d.fvarId))
    if ty.isAppOfArity ``ReadContract 4 && ty.getArg! 0 == ctx then
      return some (mkProj ``ReadContract 0 (mkFVar d.fvarId))
  return none

simproc ↓ [cir_exec] reduceProtoRecord (Ctx.record? _ _) := fun e => do
  unless e.isAppOfArity ``Ctx.record? 2 do return .continue
  let ctx := e.getArg! 0
  let nameExpr ← whnfD (e.getArg! 1)
  let name ← match nameExpr with
    | .lit (.strVal s) => pure s
    | _ => return .continue
  let idx? : Option Nat :=
    if name == "apache::thrift::protocol::TCompactProtocolT<apache::thrift::transport::TTransport>" then some 0
    else if name == "apache::thrift::protocol::TVirtualProtocol<apache::thrift::protocol::TCompactProtocolT<apache::thrift::transport::TTransport>, apache::thrift::protocol::TProtocolDefaults>.base" then some 1
    else if name == "apache::thrift::protocol::TProtocolDefaults.base" then some 2
    else if name == "apache::thrift::protocol::TProtocol.base" then some 3
    else if name == "anon.0" then some 4
    else if name == "anon.1" then some 5
    else if name == "apache::thrift::protocol::TList" then some 6
    else if name == "apache::thrift::protocol::TSet" then some 7
    else none
  let some idx := idx? | return .continue
  let some hRec ← findProtoRecords? ctx | return .continue
  let pf := mkProj ``ProtoRecords idx hRec
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  let x ← whnfD rhs.appArg!
  let rhs := mkApp rhs.appFn! x
  let pf ← mkExpectedTypeHint pf (← mkEq e rhs)
  return .done { expr := rhs, proof? := some pf }

end EquivLean.Demo.Thrift.Cpp
