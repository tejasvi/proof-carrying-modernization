RESULT: COBSWAIT all-input theorem (coblean pin coblean-pinM7-cobswait-20261028T0554Z) CONFIRMED: items 1-6 PASS. cobswait_every, cobswait_digits, cobswait_waitstep and parmVal_digits use exactly [propext, Classical.choice, Quot.sound] (parmVal_spaces: [propext]); all 76 theorem constants of the three new modules stay within the three standard axioms; closure 44/44 leanchecker rc 0 with controls; the three new modules rebuild from source byte-identical to the pin's.

# Check by an agent: COBSWAIT all-input theorem, fork of the evidence-owner session, 20261028T060011Z to 2026-10-28T06:08:31Z (date -u)
Check dir: this directory; copy ~/fv_paper/replay/cobswait-20261028T060011Z/pin (rsync -aL of the pin without its Examples/Cobswait build
outputs, 0 symlinks), controls ~/fv_paper/replay/cobswait-20261028T060011Z/ctl, spot check ~/fv_paper/replay/cobswait-20261028T060011Z/spot. Method of
checks/csutl-20261027T201400Z. Read-only on the snapshots and the COBOL maintainer session's files (pin: 0 files newer than STAMP; build tree unchanged).

1. Sums and contents: pin SHA256SUMS 956392e2 (1146 entries) 1146/1146 rc 0 before and after; copy 1146/1146 before and
   after. diff -rq 0551Z vs pin (.lake, __pycache__ aside): only COBSWAIT_PROGRESS.md, Examples/Cobswait/, SHA256SUMS,
   examples/carddemo/cobswait.ir.json and lakefile.toml (4bc56c40; + lean_lib Cobswait, globs Examples.Cobswait.+).
   Build trees: 677 common files byte-identical (all 43 Cobol oleans, Cobol.olean be3132eb); 24 files only in the pin, all
   Examples/Cobswait (3 modules x 8). Sources: Cobswait.lean c535a43b, Model.lean 6b6d3e80, Prog.lean 228fd800 (= the COBOL maintainer session's). PASS
2. IR: CardDemo ~/coblean_corpus/carddemo/src at 59cc6c2f (clean), app/cbl/COBSWAIT.cbl sha256 38a8d282 (41 lines); the
   pin's front end (python3 -I -B tools/cobolfe/cobolfe.py ... -I app/cpy --tab-width 4), relative and absolute paths:
   f2ae5593 = stored IR (cmp), stderr empty. Prog.lean = cobol_program Cobswait from that IR file. PASS
3. Build and statements: lake build Cobswait in the copy (46 jobs; only Prog, Model, Cobswait built; 0.001 core-h): oleans
   and ileans byte-identical to the pin's (Prog c988861b, Model 88c1cbc0, Cobswait 6eb7eb2a); the other 677 build files
   unchanged. stmt/stmt.out (fresh process):
   - cobswait_every (env : Env) (m0 : Mem) (hm : m0.size = 12); r := run env 10 (initState m0); env.sysin = none -> fault
     unsupported "ACCEPT: no system input device", out = [], mem = m0; some recs: parmVal (parm recs (m0.read 4 8)) = none
     -> fault invalidData, out = []; some v: env.call "MVSWAIT" [be4 v.toNat] = none -> fault unsupported "CALL MVSWAIT",
     out = []; some [b] with b.length = 4 -> stop run, out = [call "MVSWAIT"], mem.read 0 12 = b ++ parm ...; other results
     -> fault unsupported "CALL MVSWAIT: bad result", out = []. No other hypothesis (env, m0 arbitrary; MVSWAIT abstract).
   - cobswait_digits: n < 10^8, (first record).take 8 = digits8 n, env.call "MVSWAIT" [be4 n] = some [b], b.length = 4
     -> stop run, out = [call "MVSWAIT"], mem.read 0 12 = b ++ digits8 n.
   - cobswait_waitstep: first record = waitstepCard, env.call "MVSWAIT" [[0,0,14,16]] = some [b], b.length = 4 -> stop
     run, ..., mem = b ++ digits8 3600. waitstepCard's text = the card of CardDemo's app/jcl/WAITSTEP.jcl (80 columns,
     identical; jcl sha256 36c98a55).
   - parmVal_digits: n < 10^8 -> parmVal (digits8 n) = some n; parmVal_spaces: parmVal (8 spaces) = none.
   - Fuel 10 is a numeral; Cobol.Program.run_mono (n <= n', result not outOfFuel -> same result) printed. PASS
4. Axioms and scan: the five named theorems as in RESULT; all 76 theorem constants of Prog (15), Model (0) and Cobswait (61)
   by module index: sets [] 22, [propext] 12, [Quot.sound, propext] 24, [propext, Classical.choice, Quot.sound] 18; none
   outside the three. Source scan of Examples/Cobswait (sorry, admit, axiom, native_decide, ofReduceBool, implemented_by,
   extern, unsafe, skipKernelTC): 0 hits; planted control 2 hits. The Cobol library has 8 hits, all "unsafe evalExpr" in
   tactic code (Logic/Bounds, Logic/Ground, Logic/Bytes), whose results the kernel checks. One "decide +kernel"
   (waitstep_digits). PASS
5. Kernel replay: closure of Examples.Cobswait.Cobswait in the package = 44 modules (41 Cobol incl. the root, Prog, Model,
   Cobswait; Cobol.Ext.CardDemo and Cobol.Logic.LoopExit are outside); leanchecker 44/44 rc 0 (61.8 s), all replayed, no
   reuse. BadCtl rc 1 (kernel declaration type mismatch), GoodCtl rc 0. PASS
6. Spot check (labelled; not a proof): GnuCOBOL 3.2 (the pin's third_party, scripts/cobc.sh of the copy) on the unmodified
   COBSWAIT.cbl with a stub MVSWAIT that DISPLAYs its PIC 9(8) COMP argument (spot/MVSWAIT_stub.cbl), three SYSIN cards:
   the WAITSTEP card, "00000042", "12345678 ...": the stub receives 00003600, 00000042, 12345678. cobolrun --sysin (EBCDIC
   decks, no --externals, so env.call MVSWAIT = none): fault unsupported "CALL MVSWAIT", out [], storage at the call
   [0,0,14,16 | F0F0F0F0F3F6F0F0], [0,0,0,42 | F0F0F0F0F0F0F4F2], [0,188,97,78 | F1F2F3F4F5F6F7F8], so the value passed
   (be4 n) agrees with GnuCOBOL on 3/3 cards. The listed GnuCOBOL SYSIN departures (eof, long, num, edit, just) do not
   apply to an 8-byte alphanumeric receiver read from an 80-byte card. PASS

Compute: 0.011 guarded core-h (53 guard logs); unguarded: hashing, diff, rsync copy, scans.
