import CIR.Frontend.Driver

/-!
  Emitting a `CIR.Module` as Lean source.

  The output defines one Lean constant per record, global and function, plus
  `module`. Terms use dot-constructor notation (`.load 3 1 (.int true 32)`)
  so the generated file stays readable; regions are laid out one operation
  per line.
-/

namespace CIR.Frontend

namespace Emit

def q (s : String) : String := s.quote

def int (i : Int) : String := if i < 0 then s!"({i})" else s!"{i}"

def list (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def nats (xs : List Nat) : String := list (xs.map toString)

def optVId : Option VId → String
  | some v => s!"(some {v})"
  | none => "none"

def floatKind : FloatKind → String
  | .single => ".single" | .double => ".double" | .fp16 => ".fp16" | .bf16 => ".bf16"
  | .fp80 => ".fp80" | .fp128 => ".fp128" | .longDouble => ".longDouble"

partial def ty : Ty → String
  | .int s w => s!"(.int {s} {w})"
  | .bool => ".bool"
  | .float k => s!"(.float {floatKind k})"
  | .void => ".void"
  | .ptr t => s!"(.ptr {ty t})"
  | .array t n => s!"(.array {ty t} {n})"
  | .record n => s!"(.record {q n})"
  | .func ps r va => s!"(.func {list (ps.map ty)} {ty r} {va})"
  | .vptr => ".vptr"
  | .ehToken => ".ehToken"
  | .catchToken => ".catchToken"
  | .cleanupToken => ".cleanupToken"
  | .other s => s!"(.other {q s})"

def floatLit (txt : String) (v : Float) : String :=
  s!"(.float {q txt} (Float.ofBits {v.toBits}))"

partial def const : Const → String
  | .int v => s!"(.int {int v})"
  | .bool b => s!"(.bool {b})"
  | .float t v => floatLit t v
  | .null => ".null"
  | .ptrInt v => s!"(.ptrInt ({v}))"
  | .zero => ".zero"
  | .undef => ".undef"
  | .poison => ".poison"
  | .array es => s!"(.array {list (es.map const)})"
  | .str bs tz => s!"(.str {list (bs.map int)} {tz})"
  | .record fs => s!"(.record {list (fs.map const)})"
  | .globalAddr s is => s!"(.globalAddr {q s} {list (is.map int)})"
  | .vtableAddr s i k => s!"(.vtableAddr {q s} {i} {k})"
  | .blockAddr s l => s!"(.blockAddr {q s} {q l})"
  | .other s => s!"(.other {q s})"

def binOp : BinOp → String
  | .add => ".add" | .sub => ".sub" | .mul => ".mul" | .div => ".div" | .rem => ".rem"
  | .and => ".and" | .or => ".or" | .xor => ".xor" | .max => ".max" | .min => ".min"

def fbinOp : FBinOp → String
  | .fadd => ".fadd" | .fsub => ".fsub" | .fmul => ".fmul" | .fdiv => ".fdiv" | .frem => ".frem"

def unOp : UnOp → String
  | .inc => ".inc" | .dec => ".dec" | .minus => ".minus" | .not => ".not"

def cmpKind : CmpKind → String
  | .lt => ".lt" | .le => ".le" | .gt => ".gt" | .ge => ".ge" | .eq => ".eq" | .ne => ".ne"
  | .one => ".one" | .uno => ".uno"

def castKind : CastKind → String
  | .bitcast => ".bitcast" | .arrayToPtrDecay => ".arrayToPtrDecay"
  | .memberPtrToBool => ".memberPtrToBool" | .intToPtr => ".intToPtr"
  | .ptrToInt => ".ptrToInt" | .ptrToBool => ".ptrToBool" | .integral => ".integral"
  | .intToBool => ".intToBool" | .intToFloat => ".intToFloat" | .floatToInt => ".floatToInt"
  | .floatToBool => ".floatToBool" | .boolToInt => ".boolToInt" | .floating => ".floating"
  | .addressSpace => ".addressSpace" | .boolToFloat => ".boolToFloat"
  | .other s => s!"(.other {q s})"

def cleanupKind : CleanupKind → String
  | .normal => ".normal" | .eh => ".eh" | .all => ".all"

def caseKind : CaseKind → String
  | .default => ".default" | .equal => ".equal" | .anyof => ".anyof" | .range => ".range"

def catchKind : CatchKind → String
  | .type s => s!"(.type {q s})"
  | .all => ".all"

def callee : Callee → String
  | .direct s => s!"(.direct {q s})"
  | .indirect v => s!"(.indirect {v})"

def loc (l : Loc) : String := s!"⟨{l.line}, {l.col}⟩"

def special : SpecialMember → String
  | .none => ".none" | .ctor => ".ctor" | .dtor => ".dtor"
  | .copyAssign => ".copyAssign" | .moveAssign => ".moveAssign"

def pad (n : Nat) : String := "".pushn ' ' n

/-- Splitting of large blocks: a block whose operations (nested ones included)
exceed `chunkLimit` is emitted as `abbrev` chunks `fn_x_opsK : List Op`
joined with `++`, so that no single definition is too large for the code
generator. -/
def chunkLimit : Nat := 400

structure St where
  /-- Lean name of the function being emitted (prefix of helper names). -/
  fnName  : String := ""
  helpers : Array String := #[]
  counter : Nat := 0

abbrev M := StateM St

/-- Group operations into chunks of total weight at most `chunkLimit`. -/
def chunks (ops : List Op) : List (List Op) := Id.run do
  let mut out : Array (List Op) := #[]
  let mut cur : Array Op := #[]
  let mut w : Nat := 0
  for o in ops do
    let k := countOpsOp o
    if w + k > chunkLimit && !cur.isEmpty then
      out := out.push cur.toList
      cur := #[]
      w := 0
    cur := cur.push o
    w := w + k
  if !cur.isEmpty then out := out.push cur.toList
  return out.toList

mutual
/-- A region at indentation `ind` (the opening `(.mk [` is on the current line). -/
partial def region (ind : Nat) : Region → M String
  | .mk [] => pure "(.mk [])"
  | .mk bs => do
    let blocks ← bs.mapM (block (ind + 2))
    return "(.mk [\n" ++ ",\n".intercalate blocks ++ "])"

partial def opLines (ind : Nat) (ops : List Op) : M String := do
  let txt ← ops.mapM fun o => do return pad ind ++ (← op ind o)
  return ",\n".intercalate txt

partial def block (ind : Nat) : Block → M String
  | .mk args ops => do
    let total := (ops.map countOpsOp).sum
    if total ≤ chunkLimit then
      return pad ind ++ s!".mk {nats args} [\n" ++ (← opLines (ind + 2) ops) ++ "]"
    else
      let mut names : Array String := #[]
      for c in chunks ops do
        let body ← opLines 4 c
        let st ← get
        let nm := s!"{st.fnName}_ops{st.counter}"
        set { st with counter := st.counter + 1 }
        let h := s!"abbrev {nm} : List Op := [\n{body}]\n"
        modify fun st => { st with helpers := st.helpers.push h }
        names := names.push nm
      let joined := " ++ ".intercalate names.toList
      return pad ind ++ s!".mk {nats args} ({joined})"

partial def op (ind : Nat) : Op → M String
  | .const r t c => pure s!".const {r} {ty t} {const c}"
  | .alloca r t n => pure s!".alloca {r} {ty t} {q n}"
  | .allocaConst r t n => pure s!".allocaConst {r} {ty t} {q n}"
  | .load r a t => pure s!".load {r} {a} {ty t}"
  | .retLoad r a t => pure s!".retLoad {r} {a} {ty t}"
  | .store v a t => pure s!".store {v} {a} {ty t}"
  | .copy s d t => pure s!".copy {s} {d} {ty t}"
  | .getMember r b i rt ft => pure s!".getMember {r} {b} {i} {ty rt} {ty ft}"
  | .getElement r b i it et => pure s!".getElement {r} {b} {i} {ty it} {ty et}"
  | .ptrStride r b o et ot => pure s!".ptrStride {r} {b} {o} {ty et} {ty ot}"
  | .ptrDiff r a b et rt => pure s!".ptrDiff {r} {a} {b} {ty et} {ty rt}"
  | .getGlobal r s t => pure s!".getGlobal {r} {q s} {ty t}"
  | .blockAddress r s l => pure s!".blockAddress {r} {q s} {q l}"
  | .baseClassAddr r b o st dt => pure s!".baseClassAddr {r} {b} {o} {ty st} {ty dt}"
  | .derivedClassAddr r b o st dt => pure s!".derivedClassAddr {r} {b} {o} {ty st} {ty dt}"
  | .vtableAddressPoint r v i o => pure s!".vtableAddressPoint {r} {q v} {i} {o}"
  | .vtableGetVptr r o t => pure s!".vtableGetVptr {r} {o} {ty t}"
  | .vtableGetVirtualFnAddr r v i => pure s!".vtableGetVirtualFnAddr {r} {v} {i}"
  | .vttGlobalAddr r s n => pure s!".vttGlobalAddr {r} {q s} {n}"
  | .vttParamAddr r v n => pure s!".vttParamAddr {r} {v} {n}"
  | .extractMember r a i at_ ft => pure s!".extractMember {r} {a} {i} {ty at_} {ty ft}"
  | .binop r k nsw nuw a b t => pure s!".binop {r} {binOp k} {nsw} {nuw} {a} {b} {ty t}"
  | .fbinop r k a b t => pure s!".fbinop {r} {fbinOp k} {a} {b} {ty t}"
  | .fmuladd r a b c t => pure s!".fmuladd {r} {a} {b} {c} {ty t}"
  | .shift r l a b t bt => pure s!".shift {r} {l} {a} {b} {ty t} {ty bt}"
  | .unop r k nsw a t => pure s!".unop {r} {unOp k} {nsw} {a} {ty t}"
  | .fneg r a t => pure s!".fneg {r} {a} {ty t}"
  | .fmath r f a t => pure s!".fmath {r} {repr f} {a} {ty t}"
  | .isFpClass r a c t => pure s!".isFpClass {r} {a} {repr c} {ty t}"
  | .bitCount r l pz a t => pure s!".bitCount {r} {l} {pz} {a} {ty t}"
  | .isConstant r a => pure s!".isConstant {r} {a}"
  | .bitOp r f a t => pure s!".bitOp {r} {repr f} {a} {ty t}"
  | .rotate r l a n t => pure s!".rotate {r} {l} {a} {n} {ty t}"
  | .copysign r a b t => pure s!".copysign {r} {a} {b} {ty t}"
  | .fminmax r m a b t => pure s!".fminmax {r} {m} {a} {b} {ty t}"
  | .prefetch p => pure s!".prefetch {p}"
  | .allocaN r t n c => pure s!".allocaN {r} {ty t} {q n} {c}"
  | .stackSave r => pure s!".stackSave {r}"
  | .stackRestore p => pure s!".stackRestore {p}"
  | .vaCopy s d => pure s!".vaCopy {s} {d}"
  | .unionMember r b i rt ft => pure s!".unionMember {r} {b} {i} {ty rt} {ty ft}"
  | .vaStart a => pure s!".vaStart {a}"
  | .vaEnd a => pure s!".vaEnd {a}"
  | .vaArg r a t => pure s!".vaArg {r} {a} {ty t}"
  | .vaArgP r a t => pure s!".vaArgP {r} {a} {ty t}"
  | .vaBox r a t => pure s!".vaBox {r} {a} {ty t}"
  | .vaEndCheck => pure ".vaEndCheck"
  | .vaEndCheckOf aps => pure s!".vaEndCheckOf {nats aps}"
  | .fail msg => pure s!".fail {repr msg}"
  | .fitsCheck a t msg => pure s!".fitsCheck {a} {ty t} {repr msg}"
  | .alignCheck a n => pure s!".alignCheck {a} {n}"
  | .arithOverflow r o k a b s d => pure s!".arithOverflow {r} {o} {binOp k} {a} {b} {ty s} {ty d}"
  | .iabs r mp a t => pure s!".iabs {r} {mp} {a} {ty t}"
  | .atomicFetch r k ff p v t => pure s!".atomicFetch {r} {repr k} {ff} {p} {v} {ty t}"
  | .atomicXchg r p v t => pure s!".atomicXchg {r} {p} {v} {ty t}"
  | .atomicCmpXchg o k p e d t s f => pure s!".atomicCmpXchg {o} {k} {p} {e} {d} {ty t} {q s} {q f}"
  | .getBitfield r p st n o sg t => pure s!".getBitfield {r} {p} {ty st} {n} {o} {sg} {ty t}"
  | .setBitfield r p v st n o sg t => pure s!".setBitfield {r} {p} {v} {ty st} {n} {o} {sg} {ty t}"
  | .cmp r k a b t => pure s!".cmp {r} {cmpKind k} {a} {b} {ty t}"
  | .complexCreate r a b t => pure s!".complexCreate {r} {a} {b} {ty t}"
  | .complexPart r i c t => pure s!".complexPart {r} {i} {c} {ty t}"
  | .complexArith r s a b t => pure s!".complexArith {r} {s} {a} {b} {ty t}"
  | .complexEq r n a b t => pure s!".complexEq {r} {n} {a} {b} {ty t}"
  | .vecCreate r es t => pure s!".vecCreate {r} {nats es} {ty t}"
  | .vecSplat r x n t => pure s!".vecSplat {r} {x} {n} {ty t}"
  | .vecExtract r v i t => pure s!".vecExtract {r} {v} {i} {ty t}"
  | .vecInsert r v x i t => pure s!".vecInsert {r} {v} {x} {i} {ty t}"
  | .vecCmp r k a b t rt => pure s!".vecCmp {r} {cmpKind k} {a} {b} {ty t} {ty rt}"
  | .vecShuffle r a b idx => pure s!".vecShuffle {r} {a} {b} {list (idx.map int)}"
  | .vecTernary r c a b => pure s!".vecTernary {r} {c} {a} {b}"
  | .x86Intrinsic r n as t => pure s!".x86Intrinsic {r} {repr n} {nats as} {ty t}"
  | .cast r k a st dt => pure s!".cast {r} {castKind k} {a} {ty st} {ty dt}"
  | .select r c a b t => pure s!".select {r} {c} {a} {b} {ty t}"
  | .call l r f as ts rt nt =>
    pure s!".call {loc l} {optVId r} {callee f} {nats as} {list (ts.map ty)} {ty rt} {nt}"
  | .scope r b => do return s!".scope {optVId r} {← region ind b}"
  | .setjmp r e vol svol ok b => do
    let sv := list (svol.map fun (a, p, v) => s!"({a}, {nats p}, {v})")
    return s!".setjmp {r} {e} {list (vol.map toString)} {sv} {ok} {← region ind b}"
  | .sjNote p st v => pure s!".sjNote {p} {st} {v}"
  | .setjmpRun r t v b => do return s!".setjmpRun {r} {t} ({v}) {← region ind b}"
  | .cleanupScope k b c => do
    return s!".cleanupScope {cleanupKind k} {← region ind b}\n{pad ind}  {← region ind c}"
  | .ifOp c t e => do return s!".ifOp {c} {← region ind t}\n{pad ind}  {← region ind e}"
  | .ternary r c t f => do
    return s!".ternary {optVId r} {c} {← region ind t}\n{pad ind}  {← region ind f}"
  | .forOp l c b s cl => do
    let clTxt ← match cl with
      | some (k, r) => do pure s!"(some ({cleanupKind k}, {← region ind r}))"
      | none => pure "none"
    return s!".forOp {loc l}\n{pad ind}  {← region ind c}\n{pad ind}  {← region ind b}\n{pad ind}  {← region ind s}\n{pad ind}  {clTxt}"
  | .whileOp l c b cl => do
    let clTxt ← match cl with
      | some (k, r) => do pure s!"(some ({cleanupKind k}, {← region ind r}))"
      | none => pure "none"
    return s!".whileOp {loc l}\n{pad ind}  {← region ind c}\n{pad ind}  {← region ind b}\n{pad ind}  {clTxt}"
  | .doWhileOp l b c => do
    return s!".doWhileOp {loc l}\n{pad ind}  {← region ind b}\n{pad ind}  {← region ind c}"
  | .switch c t b => do return s!".switch {c} {ty t} {← region ind b}"
  | .case k vs b => do return s!".case {caseKind k} {list (vs.map int)} {← region ind b}"
  | .tryOp b hs u => do
    let hsTxt ← hs.mapM fun (k, r) => do pure s!"({catchKind k}, {← region (ind + 2) r})"
    let uTxt ← match u with
      | some r => do pure s!"(some {← region ind r})"
      | none => pure "none"
    return s!".tryOp {← region ind b}\n{pad ind}  {list hsTxt}\n{pad ind}  {uTxt}"
  | .yield vs => pure s!".yield {nats vs}"
  | .condition c => pure s!".condition {c}"
  | .brk => pure ".brk"
  | .goto l => pure s!".goto {q l}"
  | .indirectGoto t s => pure s!".indirectGoto {t} {q s}"
  | .libc fn args => pure s!".libc {q fn} {list (args.map toString)}"
  | .label l => pure s!".label {q l}"
  | .cont => pure ".cont"
  | .ret v => pure s!".ret {optVId v}"
  | .br d as => pure s!".br {d} {nats as}"
  | .brcond c t ta f fa => pure s!".brcond {c} {t} {nats ta} {f} {nats fa}"
  | .trap => pure ".trap"
  | .unreachable => pure ".unreachable"
  | .throw o t ti =>
    let tiTxt := match ti with | some s => s!"(some {q s})" | none => "none"
    pure s!".throw {optVId o} {ty t} {tiTxt}"
  | .resume t => pure s!".resume {t}"
  | .allocException r n t => pure s!".allocException {r} {n} {ty t}"
  | .beginCatch t e h => pure s!".beginCatch {t} {e} {h}"
  | .endCatch t => pure s!".endCatch {t}"
  | .initCatchParam k e d t => pure s!".initCatchParam {q k} {e} {d} {ty t}"
  | .ehTerminate e => pure s!".ehTerminate {e}"
  | .assume c => pure s!".assume {c}"
  | .asmBarrier => pure ".asmBarrier"
  | .asmTied r ins ties => pure s!".asmTied {optVId r} {nats ins} {nats ties}"
  | .unknown n rs => pure s!".unknown {q n} {nats rs}"
end

/-! ### Lean identifiers -/

/-- Drop template arguments and the parameter list of a demangled name. -/
def baseName (d : String) : String := Id.run do
  let mut out : String := ""
  let mut depth : Nat := 0
  for c in d.toList do
    if c == '<' then depth := depth + 1
    else if c == '>' then depth := depth - 1
    else if depth == 0 then
      if c == '(' && !(out.endsWith "operator") then break
      out := out.push c
  return out

def sanitize (s : String) : String := Id.run do
  let s := (s.replace "std::__1::" "std::").replace "::" "_"
  let mut out : String := ""
  for c in s.toList do
    let c' := if c.isAlphanum then c else '_'
    if !(c' == '_' && out.endsWith "_") then out := out.push c'
  let cs := (out.toList.dropWhile (· == '_')).reverse.dropWhile (· == '_') |>.reverse
  let r3 := String.ofList (cs.take 72)
  return if r3.isEmpty then "anon" else r3

/-- Assign unique Lean names with prefix `pre`. -/
def uniqueNames (pre : String) (raw : List String) : List String := Id.run do
  let mut used : Std.HashMap String Nat := {}
  let mut out : Array String := #[]
  for r in raw do
    let base := pre ++ sanitize r
    match used[base]? with
    | none =>
      used := used.insert base 1
      out := out.push base
    | some k =>
      used := used.insert base (k + 1)
      out := out.push s!"{base}_{k + 1}"
  return out.toList

def docComment (s : String) : String :=
  "/-- `" ++ ((s.replace "`" "'").replace "-/" "- /") ++ "` -/"

def record (nm : String) (r : RecordDecl) : String :=
  let kind := match r.kind with | .struct => ".struct" | .class => ".class" | .union => ".union"
  let mems := r.members.map fun (k, t) =>
    let k := match k with | .data => ".data" | .pad => ".pad" | .empty => ".empty" | .bitfield => ".bitfield"
    s!"({k}, {ty t})"
  s!"def {nm} : RecordDecl where\n  name := {q r.name}\n  kind := {kind}\n  members := {list mems}\n  packed := {r.packed}\n  complete := {r.complete}\n" ++
  (if r.padding.isEmpty then "" else s!"  padding := {list (r.padding.map ty)}\n") ++
  (if r.vecAligns.isEmpty then "" else s!"  vecAligns := {list (r.vecAligns.map fun (i, a) => s!"({i}, {a})")}\n")

def global (nm : String) (g : GlobalDecl) : String :=
  let init := match g.init with | some c => s!"(some {const c})" | none => "none"
  s!"def {nm} : GlobalDecl where\n  sym := {q g.sym}\n  ty := {ty g.ty}\n  init := {init}\n  constant := {g.constant}\n" ++
  (if g.internal then "  internal := true\n" else "") ++
  (match g.alias with | some a => s!"  alias := some {q a}\n" | none => "")

/-- The `ctors` / `dtors` fields of a module (nothing when it has none). -/
def structors (m : Module) : String :=
  let one (fld : String) (xs : List (String × Nat)) : String :=
    if xs.isEmpty then "" else s!"  {fld} := {list (xs.map fun (s, p) => s!"({q s}, {p})")}\n"
  one "ctors" m.ctors ++ one "dtors" m.dtors

def modelTxt : Option Model → String
  | none => "none"
  | some m => s!"(some ({(repr m).pretty 100000}))"

def func (nm : String) (f : FuncDecl) : String :=
  let (body, st) := (match f.body with
    | some r => do pure s!"(some {← region 2 r})"
    | none => pure "none" : M String).run { fnName := nm }
  let ssa := list (f.ssaNames.map fun (v, n) => s!"({v}, {q n})")
  String.join (st.helpers.toList.map (· ++ "\n")) ++
  docComment (if f.demangled.isEmpty then f.sym else f.demangled) ++ "\n" ++
  s!"def {nm} : FuncDecl where\n  sym := {q f.sym}\n  demangled := {q f.demangled}\n" ++
  s!"  params := {list (f.params.map ty)}\n  ret := {ty f.ret}\n" ++
  s!"  nothrow := {f.nothrow}\n  noreturn := {f.noreturn}\n  special := {special f.special}\n" ++
  s!"  model := {modelTxt f.model}\n  ssaNames := {ssa}\n  body := {body}\n" ++
  (if f.internal then "  internal := true\n" else "") ++
  (match f.alias with | some g => s!"  alias := some {q g}\n" | none => "")

end Emit

/-- `cir2lean --modular`: one Lean module per function, so that a proof about
a function over an abstract context (`ctx.mod.findFunc? sym = some fn_f`)
imports only that function and is re-checked only when it changes.
* `<ns>.Types`: the records and globals;
* `<ns>.F.<fn_name>`: one function's `FuncDecl`;
* `<ns>`: imports all of them and defines `module` and `ctx` as `emitModule`
  does (proofs over the concrete context keep working unchanged).
Returns the files (path relative to the output root, contents) and a JSON
manifest: per function its symbol, demangled name, Lean name, module, hash of
its definition, callees, and whether it has a body or a library model. -/
def emitModular (ns : String) (m : Module) (source : String := "") :
    List (String × String) × String := Id.run do
  let recNames := Emit.uniqueNames "rec_" (m.records.map (·.name))
  let globNames := Emit.uniqueNames "g_" (m.globals.map (·.sym))
  let fnNames := Emit.uniqueNames "fn_" (m.funcs.map fun f =>
    Emit.baseName (if f.demangled.isEmpty then f.sym else f.demangled))
  let path := ns.replace "." "/"
  let header := s!"/-\n  Generated by cir2lean --modular from {source}. Do not edit.\n-/\n"
  let opening := s!"set_option maxRecDepth 100000\n\nnamespace {ns}\nopen CIR\n\n"
  let mut types := header ++ "import CIR\n\n" ++ opening
  for (r, nm) in m.records.zip recNames do
    types := types ++ Emit.record nm r ++ "\n"
  for (g, nm) in m.globals.zip globNames do
    types := types ++ Emit.global nm g ++ "\n"
  types := types ++ s!"end {ns}\n"
  let mut files : Array (String × String) := #[(path ++ "/Types.lean", types)]
  let mut imports : Array String := #[ns ++ ".Types"]
  let mut entries : Array String := #[]
  for (f0, nm) in m.funcs.zip fnNames do
    let modName := s!"{ns}.F.{nm}"
    -- line numbers relative to the function (line 1 = its first located line),
    -- so that an edit elsewhere in the file does not change this module
    let (f, baseLine) := relativeLines f0
    let defn := Emit.func nm f
    files := files.push (path ++ "/F/" ++ nm ++ ".lean",
      header ++ "import CIR\n\n" ++ opening ++ defn ++ "\n" ++ s!"end {ns}\n")
    imports := imports.push modName
    let callees := Emit.list ((funcCallees f).map Emit.q)
    entries := entries.push (s!"\{\"sym\": {Emit.q f.sym}, \"name\": {Emit.q f.demangled}, " ++
      s!"\"lean\": {Emit.q (ns ++ "." ++ nm)}, \"module\": {Emit.q modName}, " ++
      s!"\"hash\": \"{hash defn}\", \"callees\": {callees}, " ++
      s!"\"body\": {f.body.isSome}, \"model\": {f.model.isSome}, \"first_line\": {baseLine}, " ++
      s!"\"ssa_locs\": [{", ".intercalate (f0.ssaLocs.map fun (v, l, c) => s!"[{v}, {l}, {c}]")}]}")
  let mut agg := header ++ "\n".intercalate (imports.toList.map ("import " ++ ·)) ++ "\n\n" ++ opening
  agg := agg ++ s!"def module : Module where\n  name := {Emit.q m.name}\n"
  agg := agg ++ s!"  records := {Emit.list recNames}\n"
  agg := agg ++ s!"  globals := {Emit.list globNames}\n"
  if m.ptrBytes != 8 then agg := agg ++ s!"  ptrBytes := {m.ptrBytes}\n"
  if m.cxx then agg := agg ++ "  cxx := true\n"
  agg := agg ++ Emit.structors m
  agg := agg ++ s!"  funcs := {Emit.list fnNames}\n\n"
  agg := agg ++ "/-- Verification context of this module. -/\n"
  agg := agg ++ "def ctx : Ctx := Ctx.ofModule module\n\n"
  agg := agg ++ s!"end {ns}\n"
  files := files.push (path ++ ".lean", agg)
  let manifest := s!"\{\"namespace\": {Emit.q ns}, \"source\": {Emit.q source}, \"types\": {Emit.q (ns ++ ".Types")}, " ++
    s!"\"functions\": [\n  " ++ ",\n  ".intercalate entries.toList ++ "\n]}\n"
  return (files.toList, manifest)

/-- Render a module as a Lean file defining it in namespace `ns`. -/
def emitModule (ns : String) (m : Module) (source : String := "") : String := Id.run do
  let recNames := Emit.uniqueNames "rec_" (m.records.map (·.name))
  let globNames := Emit.uniqueNames "g_" (m.globals.map (·.sym))
  let fnNames := Emit.uniqueNames "fn_" (m.funcs.map fun f =>
    Emit.baseName (if f.demangled.isEmpty then f.sym else f.demangled))
  let mut out := s!"/-\n  Generated by cir2lean from {source}. Do not edit.\n-/\nimport CIR\n\n"
  out := out ++ "set_option maxRecDepth 100000\n\n"
  out := out ++ s!"namespace {ns}\nopen CIR\n\n"
  for (r, nm) in m.records.zip recNames do
    out := out ++ Emit.record nm r ++ "\n"
  for (g, nm) in m.globals.zip globNames do
    out := out ++ Emit.global nm g ++ "\n"
  for (f, nm) in m.funcs.zip fnNames do
    out := out ++ Emit.func nm f ++ "\n"
  out := out ++ s!"def module : Module where\n  name := {Emit.q m.name}\n"
  out := out ++ s!"  records := {Emit.list recNames}\n"
  out := out ++ s!"  globals := {Emit.list globNames}\n"
  if m.ptrBytes != 8 then out := out ++ s!"  ptrBytes := {m.ptrBytes}\n"
  if m.cxx then out := out ++ "  cxx := true\n"
  out := out ++ Emit.structors m
  out := out ++ s!"  funcs := {Emit.list fnNames}\n\n"
  out := out ++ "/-- Verification context of this module. -/\n"
  out := out ++ "def ctx : Ctx := Ctx.ofModule module\n\n"
  out := out ++ s!"end {ns}\n"
  return out

end CIR.Frontend
