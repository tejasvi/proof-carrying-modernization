import CIR
open CIR CIR.Std

/-!
  Unit tests of the libevent and POSIX threads models (`Std.runModel`) on the paths the
  differential test cannot reach natively (`tests/difftest/libev_cases.txt` checks the others
  against libevent 2.1.12's library): `evhttp_send_reply` on a request with a connection, a request
  whose freeing is deferred, and `event_base_loopbreak` on a live base.
  Run: `lake env lean tests/ExtModels.lean` (every `#guard` must hold).
-/

def str : Ty := .ptr (.int true 8)

/-- The records of libevent 2.1's `<event2/http_struct.h>` and `<event2/keyvalq_struct.h>` as
cir2lean emits them (the callbacks' function pointer types simplified to `void *`). -/
def recs : List RecordDecl := [
  { name := "anon.2", members := [(.data, .ptr (.record "evkeyval")), (.data, .ptr (.ptr (.record "evkeyval")))] },
  { name := "evkeyval", members := [(.data, .record "anon.2"), (.data, str), (.data, str)] },
  { name := "evkeyvalq", members := [(.data, .ptr (.record "evkeyval")), (.data, .ptr (.ptr (.record "evkeyval")))] },
  { name := "anon.1", members := [(.data, .ptr (.record "evhttp_request")), (.data, .ptr (.ptr (.record "evhttp_request")))] },
  { name := "evhttp_connection", complete := false },
  { name := "evhttp_uri", complete := false },
  { name := "evbuffer", complete := false },
  { name := "evhttp_request", members := [
      (.data, .record "anon.1"), (.data, .ptr (.record "evhttp_connection")), (.data, .int true 32),
      (.data, .ptr (.record "evkeyvalq")), (.data, .ptr (.record "evkeyvalq")), (.data, str),
      (.data, .int false 16), (.data, str), (.data, .int false 32), (.data, .int false 32),
      (.data, .int false 64), (.data, .int false 64), (.data, str), (.data, .ptr (.record "evhttp_uri")),
      (.data, .int true 8), (.data, .int true 8), (.data, .int true 32), (.data, str),
      (.data, .ptr (.record "evbuffer")), (.data, .int true 64), (.bitfield, .int false 8),
      (.data, .ptr (.record "evbuffer")), (.data, .ptr .void), (.data, .ptr .void), (.data, .ptr .void),
      (.data, .ptr .void), (.data, .ptr .void), (.data, .ptr .void), (.data, .ptr .void)] }]

def ctx : Ctx := Ctx.ofModule { records := recs }

/-- A request (block 0) as `evhttp_request_new` leaves it, with empty header lists (blocks 2 and
3) and an output buffer (block 4), the connection (block 1) when `conn`, the flags `flags`; a body
buffer holding "ab" (block 5); the strings "K" and "v" (blocks 6, 7) for a header. -/
def setup (conn : Bool) (flags : Int) : Res Mem := do
  let some zr := ctx.zeroVal 32 (.record "evhttp_request") | .ub "no zero request"
  let some zq := ctx.zeroVal 32 (.record "evkeyvalq") | .ub "no zero list"
  let (rq, m) := Mem.empty.alloc .heap (.record "evhttp_request") zr
  let (cn, m) := m.alloc .heap (.other "libevent.evhttp_connection") (.agg [])
  let (ih, m) := m.alloc .heap (.record "evkeyvalq") zq
  let (oh, m) := m.alloc .heap (.record "evkeyvalq") zq
  let (ob, m) := m.alloc .heap (.other "libevent.evbuffer") (.arr [])
  let (_, m) := m.alloc .heap (.other "libevent.evbuffer") (.arr [.int 97, .int 98])
  let (_, m) := m.alloc .readonly (.array (.int true 8) 2) (.arr [.int 75, .int 0])
  let (_, m) := m.alloc .readonly (.array (.int true 8) 2) (.arr [.int 118, .int 0])
  let req : Ptr := .loc rq []
  let m ← ctx.typedStore m (.ptr (.record "evhttp_connection")) (fld req 1)
    (.ptr (if conn then .loc cn [] else .null))
  let m ← ctx.typedStore m (.int true 32) (fld req 2) (.int flags)
  let m ← ctx.typedStore m (.ptr (.record "evkeyvalq")) (fld req 3) (.ptr (.loc ih []))
  let m ← ctx.typedStore m (.ptr (.record "evkeyvalq")) (fld req 4) (.ptr (.loc oh []))
  let m ← ctx.typedStore m (.ptr (.ptr (.record "evkeyval"))) (.loc ih [.idx 1]) (.ptr (.loc ih [.idx 0]))
  let m ← ctx.typedStore m (.ptr (.ptr (.record "evkeyval"))) (.loc oh [.idx 1]) (.ptr (.loc oh [.idx 0]))
  ctx.typedStore m (.ptr (.record "evbuffer")) (fld req 21) (.ptr (.loc ob []))

/-- Add the header K: v to the output list, then `evhttp_send_reply(req, 200, "K", body)`. -/
def reply (conn : Bool) (flags : Int) : Res (Exit × Mem) := do
  let m ← setup conn flags
  let (_, m) ← runModel ctx .evhttpAddHeader [.ptr (.loc 3 []), .ptr (.loc 6 [.idx 0]), .ptr (.loc 7 [.idx 0])] m
  runModel ctx .evhttpSendReply [.ptr (.loc 0 []), .int 200, .ptr (.loc 6 [.idx 0]), .ptr (.loc 5 [])] m

def live (m : Mem) (b : Nat) : Bool := (m.live? b).isSome

def bytesOf (m : Mem) (b : Nat) : Option Nat :=
  match m.live? b with
  | some ⟨_, _, _, .arr xs⟩ => some xs.length
  | _ => none

/- With a connection: the body's bytes moved out (the buffer is empty and still the caller's), the
request, its header lists, the header added (entry, key, value: blocks 8, 9, 10) and its output
buffer freed; the connection stays. -/
#guard match reply true 0 with
  | .ok (.ret none, m) =>
    bytesOf m 5 == some 0 && !live m 0 && !live m 2 && !live m 3 && !live m 4 &&
      !live m 8 && !live m 9 && !live m 10 && live m 1
  | _ => false

/- Without a connection: freed at once, and the body keeps its two bytes. -/
#guard match reply false 0 with
  | .ok (.ret none, m) => bytesOf m 5 == some 2 && !live m 0 && !live m 3 && !live m 8 && live m 4 == false
  | _ => false

/- A request whose freeing is deferred (`EVHTTP_REQ_DEFER_FREE`): not modelled. -/
#guard match reply false 8 with
  | .ub msg => msg.startsWith "evhttp_send_reply: a request whose freeing is deferred"
  | _ => false

/- The request used after the reply: its block is dead. -/
#guard match reply true 0 with
  | .ok (_, m) => match ctx.typedLoad m (.int true 32) (fld (.loc 0 []) 2) with
    | .ub _ => true
    | _ => false
  | _ => false

/- `event_base_loopbreak` on a live base: 0; on another object: undefined; on null: -1. -/
#guard
  let (b, m) := Mem.empty.alloc .heap (.other "libevent.event_base") (.agg [])
  (match runModel ctx .eventBaseLoopbreak [.ptr (.loc b [])] m with
    | .ok (.ret (some (.int 0)), _) => true
    | _ => false) &&
  (match runModel ctx .eventBaseLoopbreak [.ptr (.loc 7 [])] m with
    | .ub _ => true
    | _ => false) &&
  (match runModel ctx .eventBaseLoopbreak [.ptr .null] m with
    | .ok (.ret (some (.int (-1))), _) => true
    | _ => false)

/- `pthread_self` is the one thread's id, 1; `pthread_equal` compares. -/
#guard
  (match runModel ctx .pthreadSelf [] Mem.empty with
    | .ok (.ret (some (.int 1)), _) => true
    | _ => false) &&
  (match runModel ctx .pthreadEqual [.int 1, .int 1] Mem.empty with
    | .ok (.ret (some (.int 1)), _) => true
    | _ => false) &&
  (match runModel ctx .pthreadEqual [.int 1, .int 2] Mem.empty with
    | .ok (.ret (some (.int 0)), _) => true
    | _ => false)
