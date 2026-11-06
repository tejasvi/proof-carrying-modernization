import StrictTS.Core.Sem
open StrictTS

/-! Hand-written IR for tests/smoke/smoke.ts (before the translator exists). -/

def TT0 : TypeTable := ⟨fun _ => .undef, fun _ => .nil⟩

def dummyImpl : Impl :=
  { pow := fun _ _ => .nan, atan2 := fun _ _ => .nan, hypot := fun _ _ => .nan,
    un := fun _ _ => .nan, toUpper := id, toLower := id, localeCompare := fun _ _ => .nan }

abbrev S (s : String) {Γ : Ctx} : Expr TT0 Γ .str := .lit (.str (JSStr.ofString s))
abbrev B (n : Int) {Γ : Ctx} : Expr TT0 Γ .bigint := .lit (.bigint n)
abbrev logE {Γ : Ctx} (e : Expr TT0 Γ .str) : Expr TT0 Γ .undef := .builtin .log (.cons e .nil)

def factRef : FunRef (.cons .bigint .nil) .bigint := ⟨0, "fact"⟩
def fRef : FunRef .nil (.promise .bigint) := ⟨1, "f"⟩

def factDef : FunDef TT0 :=
  { name := "fact", args := .cons .bigint .nil, ret := .bigint,
    lam := .sync [⟨.bigint, false⟩] rfl
      (.seq (.ret (.cond (.prim (.bigCmp .le) (.cons (.var .here) (.cons (B 0) .nil)))
        (B 1)
        (.prim (.bigBin .mul) (.cons (.var .here)
          (.cons (.call factRef (.cons (.prim (.bigBin .sub) (.cons (.var .here) (.cons (B 1) .nil))) .nil)) .nil)))))
      .nil) }

def fDef : FunDef TT0 :=
  { name := "f", args := .nil, ret := .promise .bigint,
    lam := .async [] rfl
      (.seq (.expr (logE (S "f1")))
      (.await ⟨.bigint, false⟩ (.builtin (.promResolve .bigint) (.cons (B 5) .nil))
        (.seq (.expr (logE (S "f2")))
        (.seq (.ret (.prim (.bigBin .add) (.cons (.var .here) (.cons (B 1) .nil)))) .nil)))) }

abbrev Γm : Ctx := [⟨.map .str .bigint, false⟩, ⟨.arr .str, false⟩]
abbrev tupTy : Ty := .tup (.cons .str (.cons .bigint .nil))

def thenCb : Expr TT0 Γm (.fn (.cons .bigint .nil) .undef) :=
  .lam [] .nil (.sync [⟨.bigint, false⟩] rfl
    (.seq (.expr (logE (.prim .strConcat (.cons (S "then ") (.cons (.prim .bigToStr (.cons (.var .here) .nil)) .nil))))) .nil))

def mainB : Block TT0 [] .undef :=
  .seq (.expr (logE (.prim .bigToStr (.cons (.call factRef (.cons (B 20) .nil)) .nil))))
  (.decl ⟨.arr .str, false⟩ (.builtin (.arrOf .str 3) (.cons (S "b") (.cons (S "a") (.cons (S "c") .nil))))
  (.seq (.expr (.builtin (.arrPush .str) (.cons (.var .here) (.cons (S "d") .nil))))
  (.seq (.expr (logE (.builtin .arrJoin (.cons (.var .here) (.cons (S ",") .nil)))))
  (.decl ⟨.map .str .bigint, false⟩ (.builtin (.mapNew .str .bigint) .nil)
  (.seq (.expr (.builtin (.mapSet .str .bigint) (.cons (.var .here) (.cons (S "x") (.cons (B 1) .nil)))))
  (.seq (.expr (.builtin (.mapSet .str .bigint) (.cons (.var .here) (.cons (S "y") (.cons (B 2) .nil)))))
  (.seq (.expr (.builtin (.mapSet .str .bigint) (.cons (.var .here) (.cons (S "x") (.cons (B 3) .nil)))))
  (.seq (.forOfMap (.var .here)
      (.seq (.expr (logE (.prim .strConcat (.cons
          (.prim .strConcat (.cons (.getTup (.var .here) .here) (.cons (S "=") .nil)))
          (.cons (.prim .bigToStr (.cons (.getTup (.var .here) (.there .here)) .nil)) .nil))))) .nil))
  (.seq (.expr (.builtin (.promThen .bigint .undef) (.cons (.call fRef .nil) (.cons thenCb .nil))))
  (.seq (.expr (logE (S "sync end"))) .nil))))))))))

def smokeProg : Program TT0 := { funs := [factDef, fDef], globals := [], main := mainB }

def showRun : Option (Except Exc Unit × List JSStr) → String
  | none => "DIVERGED"
  | some (r, out) =>
    let status := match r with
      | .ok _ => "ok"
      | .error (.thrown e) => s!"uncaught {e.name}: {e.message}"
      | .error (.panic m) => s!"PANIC {m}"
    String.intercalate "\n" (out.map toString) ++ s!"\n[{status}]"

#eval IO.println (showRun (runOutput dummyImpl smokeProg))
