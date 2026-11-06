/-
`cobolrun prog.json [--fuel N] [--mem HEX] [--inputs inputs.json] [--clock YYYYMMDDhhmmsshh+hhmm]
  [--externals carddemo] [--addrspace segments.json] [--absent ID,...]`

Resolve a surface-IR program, run it with the reference semantics and print the outcome as
JSON: `{"signal": ..., "mem": [bytes], "out": [events]}`.  Used for differential testing
against a COBOL compiler and for replaying test vectors.  `--externals carddemo` supplies the
non-COBOL routines CardDemo calls (`COBDATFT`, Cobol/Ext/CardDemo.lean); without it every
`CALL` other than `CEE3ABD` is `unsupported`.  `--addrspace` gives the address space that
`SET ADDRESS OF` reads (a JSON list of `[address, [bytes]]` segments; elsewhere zeros).
`--absent` lists the `OPTIONAL` files (by id) that are not present when the run starts
(`Env.absent`; other files are present, with the records `--inputs` gives them or none).
-/
import Cobol
import Cobol.Ext.CardDemo
open Lean Cobol

def signalStr : Signal → String
  | .stop k => s!"stop:{repr k}"
  | .fault f => s!"fault:{repr f}"
  | s => s!"{repr s}"

def eventJson : Event → Json
  | .display bs => Json.mkObj [("display", toJson (bs.map (·.toNat)))]
  | .write f bs => Json.mkObj [("write", Json.mkObj [("file", toJson f), ("rec", toJson (bs.map (·.toNat)))])]
  | .call p => Json.mkObj [("call", toJson p)]
  | .rewrite f bs => Json.mkObj [("rewrite", Json.mkObj [("file", toJson f), ("rec", toJson (bs.map (·.toNat)))])]
  | .delete f k => Json.mkObj [("delete", Json.mkObj [("file", toJson f), ("key", toJson (k.map (·.toNat)))])]

partial def parseArgs : List String → Nat → Option String → Option String → (Nat × Option String × Option String)
  | "--fuel" :: n :: rest, _, m, i => parseArgs rest n.toNat! m i
  | "--mem" :: h :: rest, f, _, i => parseArgs rest f (some h) i
  | "--inputs" :: p :: rest, f, m, _ => parseArgs rest f m (some p)
  | _ :: rest, f, m, i => parseArgs rest f m i
  | [], f, m, i => (f, m, i)

/-- The value after `--addrspace`, if any. -/
def addrArg : List String → Option String
  | "--addrspace" :: c :: _ => some c
  | _ :: rest => addrArg rest
  | [] => none

/-- The byte at address `a` of a list of segments. -/
def segByte (segs : List (Nat × Array UInt8)) (a : Nat) : UInt8 :=
  match segs.find? (fun (s, bs) => s ≤ a && a < s + bs.size) with
  | some (s, bs) => bs[a - s]!
  | none => 0

/-- The value after `--externals`, if any. -/
def externalsArg : List String → Option String
  | "--externals" :: c :: _ => some c
  | _ :: rest => externalsArg rest
  | [] => none

/-- The value after `--clock`, if any (the reading returned by every clock access). -/
def clockArg : List String → Option String
  | "--clock" :: c :: _ => some c
  | _ :: rest => clockArg rest
  | [] => none

/-- The value after `--sysin`, if any: a JSON file with the records of the system input device
(`Env.sysin`, read by `ACCEPT`), a list of records, each a list of bytes in the program's character
set (as the records of `--inputs`).  Without it the run has no system input device. -/
def sysinArg : List String → Option String
  | "--sysin" :: c :: _ => some c
  | _ :: rest => sysinArg rest
  | [] => none

/-- The value after `--absent`, if any (file ids separated by commas). -/
def absentArg : List String → Option String
  | "--absent" :: c :: _ => some c
  | _ :: rest => absentArg rest
  | [] => none

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => IO.eprintln "usage: cobolrun prog.json [--fuel N] [--mem HEX] [--inputs inputs.json] [--clock C]"; pure 2
  | path :: rest =>
    let (fuel, memHex, inputs) := parseArgs rest 100000 none none
    let P ← loadProgram path
    let m0 : Mem ← match memHex with
      | none => pure (Mem.fill P.memSize 0)
      | some h => match Resolve.hexBytes h.toList with
        | .ok bs => pure ⟨bs.toArray⟩
        | .error e => throw (IO.userError e)
    let inp : List (Nat × List (List UInt8)) ← match inputs with
      | none => pure []
      | some p => do
        let j ← IO.ofExcept (Json.parse (← IO.FS.readFile p))
        let raw ← IO.ofExcept (fromJson? (α := List (Nat × List (List Nat))) j)
        pure (raw.map (fun (f, rs) => (f, rs.map (·.map UInt8.ofNat))))
    let env : Env := match clockArg rest with
      | none => {}
      | some c =>
        let bs := match P.cfg.charset with
          | .ascii => c.toList.map (fun ch => UInt8.ofNat ch.toNat)
          | .ebcdic => (Codepage.encode037 c).getD []
        { clock := fun _ => bs }
    let env : Env := match externalsArg rest with
      | some "carddemo" => { env with call := Ext.cardDemoCalls P.cfg }
      | _ => env
    let env : Env ← match addrArg rest with
      | none => pure env
      | some p => do
        let j ← IO.ofExcept (Json.parse (← IO.FS.readFile p))
        let raw ← IO.ofExcept (fromJson? (α := List (Nat × List Nat)) j)
        let segs := raw.map (fun (a, bs) => (a, (bs.map UInt8.ofNat).toArray))
        pure { env with addrSpace := segByte segs }
    let env : Env ← match sysinArg rest with
      | none => pure env
      | some p => do
        let j ← IO.ofExcept (Json.parse (← IO.FS.readFile p))
        let raw ← IO.ofExcept (fromJson? (α := List (List Nat)) j)
        pure { env with sysin := some (raw.map (·.map UInt8.ofNat)) }
    let env : Env ← match absentArg rest with
      | none => pure env
      | some s => do
        let ids ← (s.splitOn ",").mapM fun x => match x.toNat? with
          | some n => pure n
          | none => throw (IO.userError s!"--absent: not a file id: {x}")
        pure { env with absent := fun f => ids.contains f }
    let (sig, st) := P.run env fuel (P.initState m0 inp)
    let out := Json.mkObj [
      ("signal", toJson (signalStr sig)),
      ("mem", toJson (st.mem.bytes.toList.map (·.toNat))),
      ("out", Json.arr (st.out.reverse.map eventJson).toArray)]
    IO.println out.compress
    pure 0
