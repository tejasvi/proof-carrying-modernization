import EquivLean.Modernize.Cbtrn02c.Any.JavaRunLib

/-!
# CBTRN02C → Java: the signatures of `run`'s and `postTransaction`'s callees
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

def validateTranSig : MethodSig :=
  ⟨"Cbtrn02c", .prim .int, "validateTran", [.cls "Cbtrn02c$DalytranRecord",
    .array (.cls "Cbtrn02c$CardXrefRecord"), .array (.cls "Cbtrn02c$AccountRecord"),
    .cls "Cbtrn02c$CardXrefRecord", .cls "Cbtrn02c$AccountRecord"]⟩
def writeRejectSig : MethodSig :=
  ⟨"Cbtrn02c", .void, "writeReject", [.cls "Cbtrn02c$Result", .cls "Cbtrn02c$DalytranRecord", .prim .int]⟩
def db2TimestampSig : MethodSig :=
  ⟨"Cbtrn02c", .cls "java.lang.String", "db2Timestamp", [.cls "java.lang.String"]⟩
def updateTcatbalSig : MethodSig :=
  ⟨"Cbtrn02c", .prim .boolean, "updateTcatbal", [.cls "Cbtrn02c$Result", .cls "Cbtrn02c$DalytranRecord",
    .cls "Cbtrn02c$CardXrefRecord", .cls "Cbtrn02c$TranCatBalRecord", .cls "java.util.List"]⟩
def updateAccountSig : MethodSig :=
  ⟨"Cbtrn02c", .void, "updateAccount", [.cls "Cbtrn02c$Result", .cls "Cbtrn02c$DalytranRecord",
    .cls "Cbtrn02c$AccountRecord", .array (.cls "Cbtrn02c$AccountRecord")]⟩
def writeTransactionSig : MethodSig :=
  ⟨"Cbtrn02c", .prim .boolean, "writeTransaction", [.cls "Cbtrn02c$Result", .cls "Cbtrn02c$TranRecord",
    .cls "java.util.List"]⟩

end EquivLean.Modernize.Cbtrn02c.Java
