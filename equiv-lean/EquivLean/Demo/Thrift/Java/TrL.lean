import EquivLean.Demo.Thrift.Java.Tr

/-!
# Thrift → Java (T4): the transport contracts during symbolic execution

The contracts take the representation `R`, so their table is not a closed term and the symbolic
execution does not evaluate a lookup in it; these equations give the contract of each transport
call (the signatures as the calls in the bodies spell them). `ClassOK` names the declaration of
the transport object's class, so that lookups of that class are resolved instead of split on.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem tc_write (R : TRep) :
    List.lookup (⟨"org.apache.thrift.transport.TTransport", .void, "write", [(JType.prim PrimType.byte).array, .prim .int, .prim .int]⟩ : MethodSig) (tContracts R) =
      some (writeSpec R) := rfl

theorem tc_readAll (R : TRep) :
    List.lookup (⟨"org.apache.thrift.transport.TTransport", .prim .int, "readAll", [(JType.prim PrimType.byte).array, .prim .int, .prim .int]⟩ : MethodSig) (tContracts R) =
      some (readAllSpec R) := rfl

theorem tc_getBytesRemainingInBuffer (R : TRep) :
    List.lookup (⟨"org.apache.thrift.transport.TTransport", .prim .int, "getBytesRemainingInBuffer", []⟩ : MethodSig) (tContracts R) =
      some (getBytesRemainingInBufferSpec R) := rfl

theorem tc_getBuffer (R : TRep) :
    List.lookup (⟨"org.apache.thrift.transport.TTransport", (JType.prim PrimType.byte).array, "getBuffer", []⟩ : MethodSig) (tContracts R) =
      some (getBufferSpec R) := rfl

theorem tc_getBufferPosition (R : TRep) :
    List.lookup (⟨"org.apache.thrift.transport.TTransport", .prim .int, "getBufferPosition", []⟩ : MethodSig) (tContracts R) =
      some (getBufferPositionSpec R) := rfl

theorem tc_consumeBuffer (R : TRep) :
    List.lookup (⟨"org.apache.thrift.transport.TTransport", .void, "consumeBuffer", [.prim .int]⟩ : MethodSig) (tContracts R) =
      some (consumeBufferSpec R) := rfl

theorem tc_checkReadBytesAvailable (R : TRep) :
    List.lookup (⟨"org.apache.thrift.transport.TTransport", .void, "checkReadBytesAvailable", [.prim .long]⟩ : MethodSig) (tContracts R) =
      some (checkReadBytesAvailableSpec R) := rfl

/-- A call to a method of another class than `TTransport` has no transport contract. -/
theorem tc_none (R : TRep) (c : ClassName) (r : JType) (n : String) (ps : List JType)
    (h : c ≠ "org.apache.thrift.transport.TTransport") :
    List.lookup (⟨c, r, n, ps⟩ : MethodSig) (tContracts R) = none := by
  have hb : ∀ (r' : JType) (n' : String) (ps' : List JType),
      ((⟨c, r, n, ps⟩ : MethodSig) == ⟨"org.apache.thrift.transport.TTransport", r', n', ps'⟩) = false := by
    intro r' n' ps'
    rw [beq_eq_false_iff_ne]
    intro e
    exact h (MethodSig.mk.inj e).1
  simp only [tContracts, List.lookup, writeSig, readAllSig, getBytesRemainingInBufferSig, getBufferSig,
    getBufferPositionSig, consumeBufferSig, checkReadBytesAvailableSig, ttCls, hb]

/-- The first element of a list of length at least `(1#32).toNat` (the bound as `readAll(…, 1)`'s
contract states it): a rewrite rule whose side condition is that hypothesis itself. -/
theorem getElem?_zero_of_one32 {α : Type} {l : List α} (h : (1#32 : I32).toNat ≤ l.length) :
    l[0]? = some (l[0]'(by have : (1#32 : I32).toNat = 1 := rfl; omega)) :=
  List.getElem?_eq_getElem _

/-- The transport object's class is a class of the program, with declaration `d`. -/
def ClassOK (P : Program) (σ : State) (t : Addr) : Prop :=
  ∃ c fst d, σ.heap t = some (.plain c fst) ∧ P.findClass c = some d

end EquivLean.Demo.Thrift.Java
