RESULT: CONFIRMED with two conditions. At cirlean next2 (424e821) the 3 T2 union units and the 12 T3 shared_ptr verdicts compile from copies, every theorem prints exactly propext, Classical.choice, Quot.sound, and their closures replay (115/115 modules rc 0, controls ok); every statement is the same Lean expression as at e6ac99a. (1) At next2 libstdc++'s 64-bit read of the two 32-bit counters is undefined (Ctx.punnedMember), so each T3 verdict relates outcomes only on inputs on which neither version has undefined behaviour; on inputs on which either version reaches the read it says only that both versions go wrong, and no verdict is informative on executions that reach the read. (2) The T3 verdicts use the program terms of T3; next2's own front end emits them differently (one union of std::string in 24/24 terms; an atomic compare-and-swap that 2/24 terms leave unsupported). The T2 terms equal next2's front-end output.

# T2 union units and T3 shared_ptr verdicts at cirlean next2 424e821 (veriforch re-check, labelled, outside the pre-registrations): evidence check
An agent of the evidence-owner session, 2026-10-28 06:10Z-06:30Z (date -u). Check dir: this directory; replay dir ~/fv_paper/replay/t23next2-20261028T061053Z.
Method of checks/t2union-20261027T0208Z and checks/t3sp-20261027T0244Z. (Written by the evidence-owner session from the fork's report; the file tool refused
report files from the fork.)

## 1. Packages, copies, frozen semantics: PASS
- t2_unionpun_next2_424e821: SHA256SUMS 59083fd5 = announced; 26/26 OK before, in copy, after. leanchecker_replay.log 99fcead1.
- t3_shared_ptr_next2_424e821: SHA256SUMS 4811f315 = announced; 189/189 OK before, in copy, after. REPORT.md b85964c3, summary.json
  775293ab, leanchecker_replay.log e1328859 = announced.
- Copies: cp -rL, 0 symlinks, diff -rq empty. ~/cirlean_frozen/next2_424e821_20261027: HEAD 424e8218, clean, not a partial clone; no
  delivered build manifest, mine of .lake/build (1,161 files) identical before and after; cirrun 85da63b4 = an agent's.

## 2. Sources and statements: PASS
- T2: VO 3/3 byte-identical to the e6ac99a run dirs; the 2 Gen modules are the e6ac99a ones (0566 uses 0254's binary-protocol Gen,
  differing only in the unity name string).
- T3: 24 Gen, 12 verdicts, 3 VerifOrch and Core/Facts byte-identical to the e6ac99a package; of the 13 EquivLean modules, 12 equal
  equiv-lean 5ec2642; Tactic.lean adds one line (item 3). CheckAll12 imports the 12 verdicts.
- Fresh-process statements: T2 3/3 identical type hash, modules and text at next2 vs e6ac99a (NaN hypotheses unchanged); T3 24/24
  identical at next2, at e6ac99a and in the producer's next2 lib. The statements are the same expressions; the library under them
  changed.
- Front end: next2's cir2lean regenerates the T2 Gen byte for byte except line 2 (0566: except the name string); for T3 it
  regenerates none of the 24: union anon.0 of basic_string is [char[16], uint64] + padding in next2's output vs one member uint8[8]
  in the verdicts' terms (all 24); in the 2 TFileTransport units next2 emits .atomicCmpXchg where the terms have
  .unknown "cir.atomic.cmpxchg" (UB "unsupported operation", Eval.lean:1112). e6ac99a's front end gives the verdicts' terms (an agent).

## 3. Tactic.lean: PASS (proof side only)
- Line 112 adds `| .halt n => pure (Exit.halt n, σ.mem)` to the statement of the helper holds_evalCall_body_elim (103-114), mirroring
  evalCall_body (Exec.lean:419) after next2 added Exit.halt (Basic.lean:108). No printed statement uses a constant from this module.

## 4. Counter read: undefined at next2; verdicts vacuous on it
- _M_release loads member 1 (int32) through an int64 pointer, unconditionally on entry (Gen 3699-3706). next2: .load -> loadPtr ->
  Ctx.typedLoad -> punnedMember (Basic.lean:485-497; accessCompatible 197-202, same-width integers only) -> UB "type-punned access".
  Probe: next2 cirrun gives the UB in 12/12; e6ac99a cirrun returns the use count alone; native returns use + 2^32·weak.
- Definitions: Sim := Safe s -> Safe t ∧ ∀ ot, Runs t ot -> ∃ os, Runs s os ∧ R ot os; Equiv = Sim both ways (Sim.lean:42-47); CIR
  Runs = ok, Safe = ∃ ok (Behaves.lean:26-28); ObsEq / EquivOn (Obs.lean:25-31); Bad = ¬WT ∨ ¬SafeRet old (Patch.lean:27-28, 70-71).
- Per input: the new version is safe exactly when the old one is, and safe runs agree; inputs that reach the read in either version
  are unsafe in both, with no outcome claim; the theorems do not show that safe inputs exist. At e6ac99a the same statements held with
  the one-element meaning (an agent). The C maintainer session's account is consistent (plus: safety coincides on every input); the strict-aliasing remark
  is the C maintainer session's statement only.

## 5. T2 NaN restriction stays
- An agent's controls run unchanged at next2: non-NaN inputs return; NaN patterns end in UB "read of an indeterminate or
  ill-typed value"; outputs equal the e6ac99a ones. CHANGES_recpun.md: union reinterpretation unchanged.

## 6. Build, axioms, replay: PASS
- Compile (producer's flags; LEAN_PATH = mine + next2): A 5/5, B 53/53 rc 0. Oleans: A 5/5 and B 40/53 equal the producer's.
- Axioms: 3/3 + 24/24 exactly the standard three. Replay: CIR 44/44, mine B 53/53, producer VOEquiv 13/13, mine A 5/5 = 115/115 rc
  0, no reuse. BadCtl rc 1, GoodCtl rc 0.

## 7. Producer's report consistent with the above. ## 8. 0.217 guarded core-h (180 guard logs); copies, hashing, diffs, closures and
git reads unguarded; read only outside the two check directories; no messages sent.
