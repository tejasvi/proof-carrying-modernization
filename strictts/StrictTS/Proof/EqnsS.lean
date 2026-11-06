/-
StrictTS proof layer: one equation per statement form (generated from `evalS`).
Lean's own per-arm equation generation for `evalS` exceeds its heartbeat budget, so these
equations are stated explicitly and proved from `evalS.eq_def`.
-/
import StrictTS.Proof.Exec

set_option maxHeartbeats 1000000

namespace StrictTS
open JS
variable {TT : TypeTable}

@[ts_sym] theorem evalS_expr (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty} (e : Expr TT Γ t)
    (env : Env TT Γ) :
    evalS I P (.expr e : Stmt TT Γ ρ) env = (do
    match ← catchThrown (evalE I P e env) with
    | .error ex => pure (.exc ex, env)
    | .ok _ => pure (.normal, env)
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_assign (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty} (x : MVar Γ t) (e : Expr TT Γ t)
    (env : Env TT Γ) :
    evalS I P (.assign x e : Stmt TT Γ ρ) env = (do
    match ← catchThrown (evalE I P e env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => pure (.normal, env.set x v)
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_gset (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty} (g : GRef t) (e : Expr TT Γ t)
    (env : Env TT Γ) :
    evalS I P (.gset g e : Stmt TT Γ ρ) env = (do
    match ← catchThrown (evalE I P e env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => do
      JS.write (.box _) g.idx (some v)
      pure (.normal, env)
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_setField (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {c : String} {t : Ty} {fs : Fields} (o : Expr TT Γ (.obj c)) (m : Mem t fs.types) (e : Expr TT Γ t)
    (env : Env TT Γ) :
    evalS I P (.setField o m e : Stmt TT Γ ρ) env = (do
    match ← catchThrown (do
        let r ← evalE I P o env
        let v ← evalE I P e env
        let cell ← readObj c fs.types r.objAddr
        writeObj c fs.types r.objAddr (cell.set m v)) with
    | .error ex => pure (.exc ex, env)
    | .ok _ => pure (.normal, env)
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_ite (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (c : Expr TT Γ .bool) (b1 : Block TT Γ ρ) (b2 : Block TT Γ ρ)
    (env : Env TT Γ) :
    evalS I P (.ite c b1 b2 : Stmt TT Γ ρ) env = (do
    match ← catchThrown (evalE I P c env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => if v.toBool then evalB I P b1 env else evalB I P b2 env
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_while (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (c : Expr TT Γ .bool) (body : Block TT Γ ρ)
    (env : Env TT Γ) :
    evalS I P (.while c body : Stmt TT Γ ρ) env = (evalLoop I P c body .nil env
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_forLoop (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (c : Expr TT Γ .bool) (body : Block TT Γ ρ) (step : Block TT Γ ρ)
    (env : Env TT Γ) :
    evalS I P (.forLoop c body step : Stmt TT Γ ρ) env = (evalLoop I P c body step env
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_doWhile (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (body : Block TT Γ ρ) (c : Expr TT Γ .bool)
    (env : Env TT Γ) :
    evalS I P (.doWhile body c : Stmt TT Γ ρ) env = (evalDo I P body c env
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_forOf (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty} (a : Expr TT Γ (.arr t)) (body : Block TT (⟨t, false⟩ :: Γ) ρ)
    (env : Env TT Γ) :
    evalS I P (.forOf a body : Stmt TT Γ ρ) env = (do
    match ← catchThrown (evalE I P a env) with
    | .error ex => pure (.exc ex, env)
    | .ok r => evalForOf I P r.arrAddr 0 body env
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_forOfMap (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {k v : Ty} (a : Expr TT Γ (.map k v)) (body : Block TT (⟨.tup (.cons k (.cons v .nil)), false⟩ :: Γ) ρ)
    (env : Env TT Γ) :
    evalS I P (.forOfMap a body : Stmt TT Γ ρ) env = (do
    match ← catchThrown (evalE I P a env) with
    | .error ex => pure (.exc ex, env)
    | .ok r => evalForOfMap I P r.mapAddr 0 body env
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_forOfSet (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty} (a : Expr TT Γ (.set t)) (body : Block TT (⟨t, false⟩ :: Γ) ρ)
    (env : Env TT Γ) :
    evalS I P (.forOfSet a body : Stmt TT Γ ρ) env = (do
    match ← catchThrown (evalE I P a env) with
    | .error ex => pure (.exc ex, env)
    | .ok r => evalForOfSet I P r.setAddr 0 body env
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_forOfStr (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (a : Expr TT Γ .str) (body : Block TT (⟨.str, false⟩ :: Γ) ρ)
    (env : Env TT Γ) :
    evalS I P (.forOfStr a body : Stmt TT Γ ρ) env = (do
    match ← catchThrown (evalE I P a env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => evalForOfStr I P (Conv.codePointStrs v.toStr.units) body env
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_brk (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (n : Nat)
    (env : Env TT Γ) :
    evalS I P (.brk n : Stmt TT Γ ρ) env = (pure (.brk n, env)
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_cont (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (n : Nat)
    (env : Env TT Γ) :
    evalS I P (.cont n : Stmt TT Γ ρ) env = (pure (.cont n, env)
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_ret (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (e : Expr TT Γ ρ)
    (env : Env TT Γ) :
    evalS I P (.ret e : Stmt TT Γ ρ) env = (do
    match ← catchThrown (evalE I P e env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => pure (.ret v, env)
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_retP (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (e : Expr TT Γ (.promise ρ))
    (env : Env TT Γ) :
    evalS I P (.retP e : Stmt TT Γ ρ) env = (do
    match ← catchThrown (evalE I P e env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => pure (.retP v.promAddr, env)
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_throw (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (e : Expr TT Γ .err)
    (env : Env TT Γ) :
    evalS I P (.throw e : Stmt TT Γ ρ) env = (do
    match ← catchThrown (evalE I P e env) with
    | .error ex => pure (.exc ex, env)
    | .ok v => pure (.exc v.toErr, env)
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_try (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (body : Block TT Γ ρ) (h : Block TT (⟨.err, false⟩ :: Γ) ρ) (fin : Block TT Γ ρ)
    (env : Env TT Γ) :
    evalS I P (.try body h fin : Stmt TT Γ ρ) env = (do
    let (c1, env1) ← evalB I P body env
    let (c2, env2) ← match c1 with
      | .exc ex => do
        let (c, env') ← evalB I P h (.cons (.err ex) env1)
        pure (c, env'.tail)
      | c => pure (c, env1)
    let (c3, env3) ← evalB I P fin env2
    match c3 with
    | .normal => pure (c2, env3)
    | c => pure (c, env3)
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_tryFin (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (body : Block TT Γ ρ) (fin : Block TT Γ ρ)
    (env : Env TT Γ) :
    evalS I P (.tryFin body fin : Stmt TT Γ ρ) env = (do
    let (c1, env1) ← evalB I P body env
    let (c3, env3) ← evalB I P fin env1
    match c3 with
    | .normal => pure (c1, env3)
    | c => pure (c, env3)
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_caseOptS (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {t : Ty} (a : Expr TT Γ (.opt t)) (bn : Block TT Γ ρ) (bs : Block TT (⟨t, false⟩ :: Γ) ρ)
    (env : Env TT Γ) :
    evalS I P (.caseOptS a bn bs : Stmt TT Γ ρ) env = (do
    match ← catchThrown (evalE I P a env) with
    | .error ex => pure (.exc ex, env)
    | .ok .none => evalB I P bn env
    | .ok (.some x) => do
      let (c, env') ← evalB I P bs (.cons x env)
      pure (c, env'.tail)
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_caseUS (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty} {ts : Tys} (a : Expr TT Γ (.union ts)) (alts : AltsS TT Γ ts.toList ρ)
    (env : Env TT Γ) :
    evalS I P (.caseUS a alts : Stmt TT Γ ρ) env = (do
    match ← catchThrown (evalE I P a env) with
    | .error ex => pure (.exc ex, env)
    | .ok (.inj m x) => do
      let (c, env') ← evalB I P (alts.select m) (.cons x env)
      pure (c, env'.tail)
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_block (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (b : Block TT Γ ρ)
    (env : Env TT Γ) :
    evalS I P (.block b : Stmt TT Γ ρ) env = (evalB I P b env
    ) := by
  rw [evalS.eq_def]; try rfl

@[ts_sym] theorem evalS_breakable (I : Impl) (P : Program TT) {Γ : Ctx} {ρ : Ty}  (b : Block TT Γ ρ)
    (env : Env TT Γ) :
    evalS I P (.breakable b : Stmt TT Γ ρ) env = (do
    let (c, env') ← evalB I P b env
    match c with
    | .brk 0 => pure (.normal, env')
    | .brk (n + 1) => pure (.brk n, env')
    | c => pure (c, env')
    ) := by
  rw [evalS.eq_def]; try rfl

end StrictTS
