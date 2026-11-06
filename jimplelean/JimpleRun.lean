/-
  JimpleRun.lean — the `jimple-run` executable.

    jimple-run DIR MAINCLASS [--fuel N]
    jimple-run DIR --stats


  Parses every `*.jimple` file of `DIR` (sorted by name; `DIR` may list several directories
  separated by `:`, read in that order, e.g. a program and the Jimple of library classes) with
  `Jimple.Parser`, runs
  `MAINCLASS.main(new String[0])` with the executable interpreter of `Jimple/Interp.lean`,
  and writes what the program printed to `System.out` on standard output. How the run
  ended is reported on standard error and in the exit code:
    0  normal termination
    1  uncaught exception (standard error names its class and message, as the JVM does)
    2  bad usage, unreadable directory or parse error
    3  `wrong`: the program got stuck (unmodelled library call or undefined behaviour);
       nothing is printed on standard output, since a stuck run has no final state
    4  out of fuel (`--fuel`, default 100000000 steps)
  With `--stats`, every file is parsed and the numbers of classes, methods, bodies,
  statements, traps and locals are printed with the parse time; each file that fails to
  parse is reported (exit code 2 if any does).
-/
import Jimple.Parser
import Jimple.Interp

open Jimple

def usage : String := "usage: jimple-run DIR MAINCLASS [--fuel N] | jimple-run DIR --stats"

/-- `--stats`: parse every `*.jimple` file of `dir` and print counts and the parse time. -/
def stats (dir : System.FilePath) : IO UInt32 := do
  let es ← dir.readDir
  let fs := (es.filter (·.fileName.endsWith ".jimple")).qsort (·.fileName < ·.fileName)
  let t0 ← IO.monoMsNow
  let mut classes := 0; let mut methods := 0; let mut bodies := 0
  let mut stmts := 0; let mut traps := 0; let mut locals := 0; let mut bytes := 0
  let mut failed := 0
  for e in fs do
    let src ← IO.FS.readFile e.path
    bytes := bytes + src.utf8ByteSize
    match Parser.parseClass src with
    | .ok c =>
      classes := classes + 1
      methods := methods + c.methods.length
      for m in c.methods do
        if let some b := m.body then
          bodies := bodies + 1
          stmts := stmts + b.stmts.size
          traps := traps + b.traps.length
          locals := locals + b.locals.length
    | .error msg =>
      failed := failed + 1
      IO.eprintln s!"parse error: {e.fileName}: {msg}"
  let t1 ← IO.monoMsNow
  IO.println s!"files {fs.size} ({bytes} bytes), classes {classes}, methods {methods}, bodies {bodies}, statements {stmts}, traps {traps}, locals {locals}, parse failures {failed}, parse time {t1 - t0} ms"
  return if failed = 0 then 0 else 2

/-- The classes of all `*.jimple` files of the directories `dirs`, each in file-name order. -/
def loadProgram (dirs : List System.FilePath) : IO (Except String Program) := do
  let mut cs : Array ClassDecl := #[]
  for dir in dirs do
    let es ← dir.readDir
    let fs := (es.filter (·.fileName.endsWith ".jimple")).qsort (·.fileName < ·.fileName)
    for e in fs do
      match Parser.parseClass (← IO.FS.readFile e.path) with
      | .ok c => cs := cs.push c
      | .error msg => return .error s!"{e.path}: {msg}"
  return .ok { classes := cs.toList }

/-- `java.lang.Foo: message` for an exception object, as the JVM's uncaught-exception
    handler prints it (for exceptions whose `toString` is the library one). -/
def excText (σ : State) (e : Addr) : String :=
  match σ.heap e with
  | some (.plain c fs) =>
    match Fields.get fs ("java.lang.Throwable", "detailMessage") with
    | some m => match strOf σ m with
      | some s => s!"{c}: {JStr.toLean s}"
      | none => c
    | none => c
  | some o => match o.ty with
    | .cls c => c
    | _ => "?"
  | none => "?"

def main (args : List String) : IO UInt32 := do
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  if let [d, "--stats"] := args then
    if !(← System.FilePath.isDir d) then
      stderr.putStrLn s!"jimple-run: not a directory: {d}"
      return 2
    return ← stats d
  let (dir, cls, fuel?) ← match args with
    | [d, c] => pure (d, c, some 100000000)
    | [d, c, "--fuel", n] => pure (d, c, n.toNat?)
    | _ => pure ("", "", none)
  let some fuel := fuel? | stderr.putStrLn usage; return 2
  let dirs := (dir.splitOn ":").map System.FilePath.mk
  for d in dirs do
    if !(← d.isDir) then
      stderr.putStrLn s!"jimple-run: not a directory: {d}"
      return 2
  match ← loadProgram dirs with
  | .error msg =>
    stderr.putStrLn s!"jimple-run: parse error: {msg}"
    return 2
  | .ok P =>
    match runMain P cls fuel with
    | some (.normal _ σ) =>
      stdout.putStr (JStr.toLean σ.out)
      return 0
    | some (.exc e σ) =>
      stdout.putStr (JStr.toLean σ.out)
      stdout.flush
      stderr.putStrLn s!"Exception in thread \"main\" {excText σ e}"
      return 1
    | some (.wrong msg) =>
      stderr.putStrLn s!"jimple-run: wrong: {msg}"
      return 3
    | none =>
      stderr.putStrLn s!"jimple-run: out of fuel ({fuel})"
      return 4
