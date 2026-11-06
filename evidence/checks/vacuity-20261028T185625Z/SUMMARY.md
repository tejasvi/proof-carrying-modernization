RESULT: CERTAIN for TFileTransport::~TFileTransport (D2, T3 unit 142): every execution of both versions goes wrong at its first step at cirlean ffab71e, e6ac99a and 424e821, so its equivalence verdict relates no execution. Five more of the 54 T3 equivalence verdicts relate no execution: deleting destructors (D0) of four abstract classes, whose bodies are a trap in both versions. No proved T2 C++ (or C) claim can be vacuous this way: all are total-correctness statements (Returns).

# An agent (fork of the evidence-owner session), written 2026-10-28T19:05:10Z by date -u; dir /home/user/fv_paper/evidence/checks/vacuity-20261028T185625Z
Inputs read only: ~/fv_paper/evidence/checks/t3-20261026T2147Z (outcomes/equivalent_list.tsv, 54 rows), replay copies
~/fv_paper/replay/t3-20261026T2147Z (runs/*/cir, runs/*/lean_cert/{VOEquiv,Gen}; deps/cirlean-ffab71e,
deps/equivlean-b171660-cir-ffab71e), ~/fv_paper/replay/t3sp-20261027T0244Z (e6ac99a re-check package),
~/fv_paper/replay/t23next2-20261028T061053Z (424e821 re-check package), ~/cirlean_frozen/next_e6ac99a_20261027 and
next2_424e821_20261027, ~/fv_paper/replay/t2-20261026T0321Z (T2 VO modules). sec-thrift.tex l.90-118 read.

## 1. TFileTransport D2 (commit 0835277ec274, old 58d385ee): CERTAIN at all three pins
- CIR: _ZN6apache6thrift9transport14TFileTransportD2Ev at unit.cir l.3444 in both versions; body lines 3445-3490
  identical old/new (loc references aside); first cir.vtt.address_point at l.3462 in both, before any branch or call.
- Program terms (Gen .../thrift_transport_TFileTransport/Unit.lean, fn_apache_thrift_transport_TFileTransport_TFileTransport_3):
  old def l.3947, new sym l.3955; body = alloca this, alloca vtt, tryOp { store, store, load, load, ten nested
  cleanupScope .all, then .unknown "cir.vtt.address_point" [6] } (old l.3987, new l.3994); the 57-line prologue is
  identical old/new. Same first op in the e6ac99a package (t3sp pkg Gen old l.3987, new l.3994; regen l.3994) and in the
  424e821 package (t23next2 pkgB Gen old l.3987, new l.3994; regen l.3988).
- Outcome class: Eval maps .unknown name _ to .ub ("unsupported operation " ++ name) at ffab71e (deps copy,
  CIR/Semantics/Eval.lean l.869), e6ac99a (l.912) and 424e821 (l.1112); no file under CIR/ of any of the three
  versions mentions vtt. Res = ok | ub | div; bind propagates .ub; cleanupScope and tryOp do not catch it
  (Eval l.790-833 at ffab71e). The ops before it (allocas, stores of the arguments, loads) cannot exit.
- Statement: theorem equivalent : Equiv (ObsEq m) (evalCall new ...) (evalCall old ...). equivlean b171660
  EquivLean/Core/Sim.lean: Equiv R t s := Sim R t s /\ Sim R' s t, Sim R t s := Safe s -> Safe t /\ ...;
  EquivLean/Bridge/Cir/Behaves.lean: Safe x := exists a, x = .ok a. Both sides are .ub on every input, so both Sim
  directions hold vacuously and the verdict relates no execution (changed_only_where_old_unsafe likewise).
- Dynamic: d0's probe (checks/stride-20261028T182920Z/vbase/results.txt) stops with 'unsupported operation
  cir.vtt.address_point' at c4ef58d, ffab71e, e6ac99a and 424e821 for a class with a virtual base.

## 2. Screen of all 54 T3 equivalence verdicts (scripts/vacuity_screen.py sha8 d228cbbf; t3_vacuity.tsv sha8 96d215ed)
Method: for the old and the new program term of each verdict's function (refs parsed from the VOEquiv statement), scan
the unconditional prefix in text order (entry block; tryOp/cleanupScope/scope bodies entered); CERTAIN if an
always-undefined op lies there (.unknown, .trap, .unreachable, .ehTerminate, .case, rethrow, unsupported .libc, a
direct call to a symbol missing from the unit or to a declaration with neither model nor body, or to a function that
is itself CERTAIN); stop at the first branch, loop, return, yield, throw, or call to a function not CERTAIN.
- CERTAIN on both versions: 6.
  - unit 142 TFileTransport D2 (section 1).
  - unit 50 TNonblockingServerTransport D0 (new Gen v733f40fc l.5549, old v6b42e7fd l.5476);
    unit 58 THttpTransport D0 (new da18006b l.2269, old v827236ca l.2140);
    unit 72 TBufferBase D0 (new c98e79ad l.5386, old d10129d4 l.5369);
    unit 72 TVirtualTransport<TMemoryBuffer,TBufferBase> D0 (new l.4706, old l.4689);
    unit 72 THttpTransport D0 (new l.1618, old l.1604).
    Each body is alloca this; try { store; load; trap } (cir.trap in the CIR itself), and .trap => .ub "trap"
    (Eval l.865). The four classes are abstract: their vtables carry 5, 2, 3 and 3 __cxa_pure_virtual slots
    (TNonblockingServerTransport, THttpTransport, TBufferBase, TVirtualTransport<TMemoryBuffer,TBufferBase>), so C++
    never calls these deleting destructors; the verdicts relate no execution, and none exists natively either.
- Not shown vacuous: 48. Stop reasons: 29 reach a return on the straight-line path with no always-undefined op before
  it, 14 stop at a direct call to a function not certain to go wrong (including all 11 TEvhttpServer::complete
  verdicts), 4 at an if, 1 at a ternary. None of these 48 function bodies contains an always-undefined op at all.
- Limits: callees are judged only by their unconditional prefix; data-dependent undefined behaviour (one-element
  meaning, stride, out-of-bounds) is not screened; a CERTAIN case after a completed nested region would be missed
  (none of the 48 bodies has an always-undefined op, so this limit does not hide one inside them).

## 3. T2 (proved C++ and C claims)
All 1,427 theorems of the T2 C++ VO modules in the replay copy (t2_cpp_vo_files.txt) and all 38 of the C ones
(t2_c_vo_files.txt) state Returns ctx sym args m post. CIR/Logic/WP.lean (ffab71e): Returns = Calls ... (.ret v =>
post | _ => False), Calls = (evalCall ...).holds Q, Res.holds (.ok a) Q = Q a and False otherwise. A function that always
goes wrong cannot satisfy it, so no proved T2 claim relates no execution in this sense (preconditions not examined).
