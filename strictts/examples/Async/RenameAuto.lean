/-
The theorems of `RenameProof.lean`, each proved by `ts_auto` alone: it unfolds `rename`,
recognises async code (the microtask loop, promise cells) and runs it with `ts_drain`, using the
oracle's answers given as lemmas. For `NoFault` over every oracle it splits on the answers itself.
-/
import Async.RenameProof
import StrictTS.Proof.Auto

open StrictTS JS RenameEx

theorem rename_missing_auto (I : Impl) (w : World TT) (n db : Nat) (id name : JSStr)
    (hj : w.jobs = []) (hn : w.extIdx = n)
    (hget : w.answer getDoc (.cons (.ext db) (.cons (.str id) .nil)) n = .ok (.val .none)) :
    ∃ p w₁ w₂ c,
      exec (callFun I program renameRef (.cons (.ext db) (.cons (.str id) (.cons (.str name) .nil)))) w =
        some (.ok (.promise p), w₁) ∧
      exec (drain I program) w₁ = some (.ok (), w₂) ∧
      w₂.heap.get? (.promise .bool, p) = some c ∧ c.state = .fulfilled (.bool false) ∧
      w₂.extIdx = n + 1 := by
  ts_auto [hj, hn, hget]

theorem rename_found_auto (I : Impl) (w : World TT) (n db d : Nat) (id name : JSStr)
    (hj : w.jobs = []) (hn : w.extIdx = n)
    (hget : w.answer getDoc (.cons (.ext db) (.cons (.str id) .nil)) n = .ok (.val (.some (.ext d))))
    (o : Except ErrVal (EVal TT .undef))
    (hset : w.answer setName (.cons (.ext db) (.cons (.str id) (.cons (.str name) .nil))) (n + 1) = o) :
    ∃ p w₁ w₂ c,
      exec (callFun I program renameRef (.cons (.ext db) (.cons (.str id) (.cons (.str name) .nil)))) w =
        some (.ok (.promise p), w₁) ∧
      exec (drain I program) w₁ = some (.ok (), w₂) ∧
      w₂.heap.get? (.promise .bool, p) = some c ∧
      c.state = (match o with | .ok _ => .fulfilled (.bool true) | .error e => .rejected e) ∧
      w₂.extIdx = n + 2 := by
  rcases o with e | ⟨⟨⟩⟩ <;> ts_auto [hj, hn, hget, hset]

theorem rename_getDoc_fails_auto (I : Impl) (w : World TT) (n db : Nat) (id name : JSStr) (e : ErrVal)
    (hj : w.jobs = []) (hn : w.extIdx = n)
    (hget : w.answer getDoc (.cons (.ext db) (.cons (.str id) .nil)) n = .error e) :
    ∃ p w₁ w₂ c,
      exec (callFun I program renameRef (.cons (.ext db) (.cons (.str id) (.cons (.str name) .nil)))) w =
        some (.ok (.promise p), w₁) ∧
      exec (drain I program) w₁ = some (.ok (), w₂) ∧
      w₂.heap.get? (.promise .bool, p) = some c ∧ c.state = .rejected e ∧ w₂.extIdx = n + 1 := by
  ts_auto [hj, hn, hget]

theorem rename_noFault_auto (I : Impl) (w : World TT) (db : Nat) (id name : JSStr) (hj : w.jobs = []) :
    NoFault (do
      let r ← callFun I program renameRef (.cons (.ext db) (.cons (.str id) (.cons (.str name) .nil)))
      drain I program
      pure r) w := by
  ts_auto [hj]
