import CIR
open CIR

/-- int f(int n) { int s = 0; for (int i = 0; i < n; ++i) { if (i == 3) continue; s += i; } return s; }
    with a cleanup scope around the body (as for an RAII object). -/
def body : Region := .mk [.mk [0] [
  .alloca 1 Ty.s32 "__retval",
  .alloca 2 Ty.s32 "n",
  .alloca 3 Ty.s32 "s",
  .store 0 2 Ty.s32,
  .const 4 Ty.s32 (.int 0),
  .store 4 3 Ty.s32,
  .scope none (.ofOps [
    .alloca 5 Ty.s32 "i",
    .const 6 Ty.s32 (.int 0),
    .store 6 5 Ty.s32,
    .forOp {} (.ofOps [
        .load 7 5 Ty.s32, .load 8 2 Ty.s32, .cmp 9 .lt 7 8 Ty.s32, .condition 9])
      (.ofOps [
        .cleanupScope .all
          (.ofOps [
            .load 10 5 Ty.s32, .const 11 Ty.s32 (.int 3), .cmp 12 .eq 10 11 Ty.s32,
            .ifOp 12 (.ofOps [.cont]) (.mk []),
            .load 13 5 Ty.s32, .load 14 3 Ty.s32, .binop 15 .add true false 14 13 Ty.s32,
            .store 15 3 Ty.s32, .yield []])
          (.ofOps [.load 16 3 Ty.s32, .const 17 Ty.s32 (.int 1000), .binop 18 .add true false 16 17 Ty.s32,
                   .const 19 Ty.s32 (.int 1000), .binop 20 .sub true false 18 19 Ty.s32, .store 20 3 Ty.s32,
                   .yield []]),
        .yield []])
      (.ofOps [.load 21 5 Ty.s32, .unop 22 .inc true 21 Ty.s32, .store 22 5 Ty.s32, .yield []])
      none,
    .yield []]),
  .load 23 3 Ty.s32,
  .store 23 1 Ty.s32,
  .load 24 1 Ty.s32,
  .ret (some 24)]]

def M : Module := { funcs := [{ sym := "f", params := [Ty.s32], ret := Ty.s32, body := some body }] }
def ctx : Ctx := { mod := M, gaddr := fun _ => none }

def showRes (r : Res (Exit × Mem)) : String :=
  match r with
  | .ok (.ret (some (.int v)), m) => s!"returned {v}, next block id {m.next}"
  | .ok _ => "returned something else"
  | .ub msg => s!"UB: {msg}"
  | .div => "diverges"

#eval showRes (evalCall ctx "f" [.int 6] Mem.empty)
#eval showRes (evalCall ctx "f" [.int 0] Mem.empty)
#eval showRes (evalCall ctx "f" [.int 300] Mem.empty)
#check @CIR.evalFor.eq_1
#print axioms CIR.evalCall
