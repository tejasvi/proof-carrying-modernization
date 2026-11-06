RESULT: 16 of the 54 T3 equivalence verdicts pass fewer arguments to evalCall than the root's FuncDecl has parameters,
in both versions (a bool parameter dropped): the 11 TEvhttpServer::complete verdicts (2 args, 3 params), TSocket
setNoDelay, setKeepAlive (1 vs 2), setLinger (2 vs 3), TNonblockingIOThread setCurrentThreadHighPriority and breakLoop
(1 vs 2). At the T3 pin ffab71e, evalCall -> evalRegion body args -> evalBlock blocks 0 args -> bindArgs params args
(CIR/Semantics/Eval.lean l.983-993, l.730-734, l.744; Basic.lean l.144-153): fewer arguments than parameters give .ub
"block argument count mismatch", so these verdicts relate no execution. With the 19 of vacuity-20261028T185625Z/deep
(13 of them among these 16), 22 of the 54 relate no execution; 32 remain with a path that passes no certain failure.
Independent of the C maintainer session's scan (~/cirlean_work/scratch/extmodels/scan/t3args_v1.tsv), which gives the same 16.
# d0 check t3arity (written 2026-10-28T20:07:35Z by date -u). Script arity.py (read only): parses each VOEquiv 'theorem equivalent'
# statement, counts the top-level elements of each evalCall argument list, and the params list of the root's FuncDecl
# in the Gen Unit.lean named by the call. Output arity.tsv.
# Correction (2026-10-28T20:18:44Z by date -u, audit v48): the bindArgs mismatch case is Basic.lean l.154 (cite l.144-154); the C maintainer session's t3args_v1.tsv has 21 ARITY_LT rows over 940 T3 statements, the same 16 among the 54.
