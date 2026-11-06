RESULT: T2 union units at e6ac99a check out: orders 132, 254 and 566 compile from my copy against the frozen next pin, each theorem prints exactly propext, Classical.choice and Quot.sound, and each closure (45 modules: VO, Gen, 43 CIR) replays in the kernel with rc 0. Each theorem assumes a non-NaN input; on NaN inputs the model ends in UB (kernel-evaluated controls). The T2 census stays as recorded. One discrepancy: the six per-file hash prefixes in veriforch's message match no file (the package's SHA256SUMS 414b2c49... is as announced and verifies 23/23).

Checked by an agent of the evidence owner, 2026-10-27, 02:08Z-02:31Z. Check dir: ~/fv_paper/evidence/checks/t2union-20261027T0208Z. Replay dir: ~/fv_paper/replay/t2union-20261027T0208Z.

## 1. Package and copies
- Package ~/veriforch/runs/postfreeze/t2_unionpun_e6ac99a/: SHA256SUMS sha 414b2c493b4fc2f3... as announced; sha256sum -c
  23/23 OK; copied to replay/.../pkg (diff -rq empty, no symlinks; sums and identity re-verified at the end).
- The sealed package holds logs, proofs and records only. The Lean packages are in the per-unit run dirs
  ~/veriforch/runs/postfreeze_t2_{0132,0254,0566}_e6ac99a, copied to replay/.../run_<order> (diff -rq empty, no
  symlinks). The package's proofs/*.lean equal the run dirs' VO modules (cmp); its records equal the run dirs' unit
  records (sha256).
- Each lakefile requires only cirlean at path ~/cirlean_frozen/next_e6ac99a_20261027 (the manifest lists that one path
  package); toolchain v4.35.0. Pin HEAD e6ac99a09c75...; its build and tree are covered by an agent
  (checks/cirnext-20261027T0143Z: MANIFEST_build 126/126 OK, worktree clean).
- Targets: the settings of T2's frozen thrift_c_glib.toml (same root, compile_commands and cflags; only the name
  differs). Thrift at f0eb8b84eb56, both protocol sources unmodified (git diff against HEAD empty).

## 2. Build, axioms, kernel replay
LEAN_PATH = my build : the pin's .lake/build : the toolchain; one thread; ulimit -v 64 GB; every Lean job under
coreh_guard_v2.

| order | function (file) | Gen, VO compile | axioms (fresh process) | closure replay |
|---|---|---|---|---|
| 132 | thrift_bitwise_cast_guint64 (thrift_compact_protocol.c) | rc 0, rc 0 | propext, Classical.choice, Quot.sound | 45/45 rc 0 |
| 254 | thrift_bitwise_cast_gdouble (thrift_binary_protocol.c) | rc 0, rc 0 | propext, Classical.choice, Quot.sound | 45/45 rc 0 |
| 566 | thrift_bitwise_cast_guint64 (thrift_binary_protocol.c) | rc 0, rc 0 | propext, Classical.choice, Quot.sound | 45/45 rc 0 |

- Compiled from source into replay/.../bld_<order> (lean -DautoImplicit=false, as the lakefile sets), with no error or
  warning; each module's own #print axioms gives the same three. My .olean bytes differ from the producer's (the Gen
  sources embed the producer's run path, and the build invocation differs), so the Gen and VO verdicts rest on my
  build; the CIR modules are the pin's frozen .olean files.
- Replay: leancheck1lp.sh on the Gen and VO modules of each unit (6 runs) and on the 43 CIR modules in the pin's import
  closure of CIR. closure_verdicts.py: 45 modules per unit (43 CIR, Gen, VO), all rc 0.

## 3. The statements in words
- 254, thrift_bitwise_cast_gdouble_spec. For every v with 0 <= v <= 2^64 - 1 (the guint64 argument) whose bit pattern
  is not a binary64 NaN (hneed_notnan : Std.decodeBits v.toNat ≠ Std.FVal.nan), and every memory m, the call returns
  normally (it terminates with no UB on the semantics) with some return value, and no caller block changes
  (Frame m m' []). The returned double is not characterised. The hypothesis excludes the 2^53 - 2 patterns with
  exponent field 2047 and a nonzero fraction, so the theorem covers 2^64 - 2^53 + 2 inputs. The theorem applies at
  v = 0 (instantiated in the controls).
- 132 and 566, thrift_bitwise_cast_guint64_spec (the same statement in two translation units). For every double v (a
  Lean Float) that is not the NaN (Std.decodeF v ≠ Std.FVal.nan, named hneed_nan in 132 and hneed_notnan in 566) and
  every m, the call returns normally with an integer x, 0 <= x < 2^64, and no caller block changes. The exact bits are
  not stated. The hypothesis holds at v = Float.ofBits 0x3FF0000000000000 (1.0), decided by the kernel in the controls.
- Records: status proved, trust kernel, statement_origin llm, 2 attempts. Attempt 1 was stuck on exactly the NaN goal
  (Std.decodeBits v.toNat = Std.FVal.nan ⊢ False for 254; Std.decodeF v = Std.FVal.nan ⊢ False for 132 and 566).
  Attempt 2 adds the hypothesis and closes that branch by absurd.

Why the hypothesis is needed (the model at e6ac99a):
- 6653cbe (unionpun; its tip ad01e8e adds labelled difftest cases) changed `.unionMember`. A member that becomes active
  while indeterminate now takes the active member's scalar when both member types have the same size (`unionInit`,
  `punScalar` in CIR/Semantics/Eval.lean): integers of the same width are wrapped to the target's signedness, an
  integer and a binary64 or binary32 float exchange the bit pattern (Float.toBits, Float.ofBits), and floats of the
  same kind are kept. `punScalar` returns none for pointers, other sizes, aggregates and NaN bit patterns in either
  direction. The member then stays indeterminate (ctx.initVal gives .undef), and the load is UB on the semantics
  (loadTy: "read of an indeterminate or ill-typed value").
- The NaN exclusion comes from the float model. Lean 4.35's Float is Float.Model: UInt64 restricted to one canonical
  NaN, and Float.ofBits maps every NaN pattern to it (control: Float.ofBits 0x7FF0000000000001 = Float.ofBits
  0xFFFFFFFFFFFFFFFF, decided by the kernel). A Float keeps no NaN sign or payload, so a NaN pattern read as a double
  has no Float with those bits, and the NaN read as a guint64 has no original bits to return. cirlean's FVal has a
  single nan (Std.decodeBits: exponent 2047 and fraction ≠ 0).
- So on NaN inputs the Returns statement is false on the semantics, and without the hypothesis the theorems cannot
  hold. C11 6.5.2.3 (footnote 95) defines these reads for every bit pattern, so the hypothesis marks a limit of the
  model, not a property of the C code.
- An agent re-ran the unions difftest at e6ac99a: 39 MATCH and 10 UB, as labelled; the NaN-pattern cases are among
  the expected UB.

## 4. Controls (controls/, against my builds)
- 254, by kernel evaluation (decide +kernel on the interpreter's approximation evalCallIter, from module.initMem):
  v = 0, 2^63 (-0.0), 0x3FF0000000000000 (1.0) and 0x7FF0000000000000 (+inf) return a double. v = 0x7FF8000000000000,
  0x7FF0000000000001, 0xFFF8000000000000 and 2^64 - 1 end in UB "read of an indeterminate or ill-typed value".
- 132 and 566, by kernel evaluation: Float.ofBits of 1.0, -0.0 and +inf return exactly their bit patterns (isInt).
  Float.nan and Float.ofBits 0x7FF0000000000001 end in the same UB. #eval runs of the interpreter (compiled code, not
  a proof) agree on 9 inputs each.
- #print axioms on two or three control theorems per file: the three standard axioms only.
- The package's own first-pass cex log for 254 at e6ac99a agrees: UB on 0x7FF8000000000000, 0x7FF0000000000001 and
  2^64 - 1; a normal return on 0, 1, 1.0, +inf and -0.0.

## 5. Against the T2 records (ffab71e) and the census
- T2 records (checks/t2-20261026T0321Z, T2records/outcomes.tsv; that dir's SHA256SUMS 16/16 OK): 132 timeout (stuck),
  254 refuted (real_bug), 566 timeout (stuck). At ffab71e every input of 254 ended in UB (the T2 check re-ran v = 0, 1,
  2^62+... and 2^64 - 1); the unit logs of 132 and 566 name the union gap. The known-false-positives table lists all three.
- At e6ac99a: all three proved with the non-NaN hypothesis. 254's UB is now confined to NaN patterns.
- The census stays as recorded: 197 proved (3 mechanical), 10 conditional, 22 partial, 1 refuted (254), 459 blocked,
  311 timeout (132 and 566 among them); stratified proved share 18.7% (16.3-21.1). The re-check ran at another pin
  (e6ac99a, not T2's frozen ffab71e) and outside PREREG_T_v1. Its final pass also ran a second attempt after first
  attempts of $0.57 (254, 566), which T2's $0.25 per-unit budget, checked before each call, does not allow. Read under
  R6 (status, trust, replay, statement origin), these records would be "proved, model-stated" with an added hypothesis;
  they stay a labelled re-check.

## 6. Discrepancies and notes
- veriforch's message gives per-file hash prefixes (records 1b37971e, 94eb05b5, 1f6f5184; proofs 7424c8b9, d7b3a174,
  b58086cc) that match no file in the package or the run dirs (sha256, sha1, md5, b2 and git blob tried). The actual
  sha256 prefixes are records 181efc3f, fc920528, a8354e69 and proofs 67cfe800, 7e1c11b2, 6a1d9624 (hash_check.txt).
  The SHA256SUMS sha is as announced and verifies 23/23, so the package is consistent and the message's per-file
  prefixes are wrong.
- The message leaves out a first pass in the same package (01:53-01:56Z, run postfreeze_t2_unionpun_e6ac99a): attempt 1
  stuck and status budget for all three; the cex step gave real_bug for 254 (NaN patterns only) and unconfirmed for 132
  and 566. Model spend: first pass 6 calls $1.83; final pass 6 calls $1.43 ($0.15, $0.64 and $0.64, as announced);
  total $3.26 (costs.tsv).
- 132's hypothesis is named hneed_nan but states non-NaN (a name only).
- The records' needs fields hold model-written commentary; this check relies only on the Lean statements.

## 7. Compute
- Guarded Lean jobs: 0.031 core-h in all (logs in replay/.../logs). File copies and hash checks ran unguarded (seconds
  each). ~/veriforch and ~/cirlean* were only read.
- One slip: the three closure_verdicts.py runs went through evidence/tools/g1.sh, which wrote their guard logs
  (0.000 core-h each) to ~/fv_paper/evidence/logs/g1/ (20261027T022814Z_3231901.log, 20261027T022815Z_3234260.log,
  20261027T022817Z_3235653.log). I moved those three files to replay/.../logs/g1_closure/. All other writes are under
  the two dirs.

## Files
compile.tsv, axcheck.tsv; replay/ (closure_<order>.tsv, cir_43.tsv, pkg_6.tsv, ax_<order>.out, cir_closure.txt);
controls/ (Ctl0132, Ctl0254, Ctl0566: .lean and .out); hash_check.txt; costs.tsv; scripts/; SHA256SUMS.
