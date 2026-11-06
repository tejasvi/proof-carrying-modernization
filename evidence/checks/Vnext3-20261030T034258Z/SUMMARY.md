RESULT: items 1-6 PASS. Item 7: the producer's met/not-met table is confirmed row by row (31/31 equal): 5 row expectations not met (false alarms 1 and 142 still UB; real-UB rows 34 -> MATCH, 158 and 162 -> UNSUPPORTED), all others met; 130 and 195 became UB under a declared kind of change (auditfix8), not a row expectation; 184 stays UB but with a new reason (a printf check).
# Check by an agent: labelled V re-run at cirlean next3 (7c73739), checked against prereg/V/ADDENDUM_V_rerun_next3.md (231bc40a, recorded 02:39:24Z)
Written 2026-10-30T03:58:27Z by date -u. Scripts s1-s9 in this dir, each run as one pjobs_v3 job under coreh_guard_v2 (guard/*.log, pjobs_run1-3.log).
1. Seal: runV_next3/SHA256SUMS f562ea17 (3130 lines), 3130/3130 OK, checked by absolute paths (only SHA256SUMS itself unlisted,
   0 missing; all files u+w, so the seal is the hash list). results.tsv 40b904ec (= run.log end line and outer_stdout.txt), 200 rows
   = sample_V (d0f38820): same order, ids and lang at every position; results.jsonl f4962e77, 200 records, 0 field differences.
2. Inputs: run.log line 1 names runner 8150b519 (= tools/run_prereg_v10.py now, = its scratch copy), sample d0f38820, cirrun
   2995b794 (the runner hashes the --cirrun file at start and stops unless it equals --cirrun-sha256; = the frozen next3 cirrun
   now), stop 2026-10-31T02:00:00Z, cores [120, 123], global cap 1.40: each equal to the addendum; outer guard cap 1.500 (addendum
   1.5). Fresh diff -u of v9 (7b85c170) and v10 = the stored diff a6bcc154 byte for byte (4 hunks: v10 docstring and usage, CIRRUN
   constant -> None, global CIRRUN, --stop-utc/--cirrun/--cirrun-sha256 required plus the sha check). cirrun env and clang/gcc/g++
   shas = next2's run.log. The cirrun path is named in no delivery record (sha only, as at next2). Start 02:47:36Z, 492 s after
   the record (02:39:24Z); delivery dir born 02:47:36.62Z; earliest file mtime and earliest row start 02:47:37Z; 794 per-step
   guard logs, none before the record; end 03:07:41Z.
3. Rows: native columns (lang, native_kind, native_sub, E, S) identical to all three earlier runs (0 diffs); no CRASH/oom row.
   next2 (813c52b6) -> next3: 50 changed = 26 kind (UB->MATCH 11: 34, 52, 80, 102, 123, 131, 144, 157, 160, 173, 196;
   UNSUPPORTED->MATCH 8: 53 and 180 cir.asm, 73 constant, 104 vec.create, 120 complex.real_ptr, 166 complex.create, 169 operand
   type, 199 ffs; TIMEOUT->MATCH 2: 40, 84; MATCH->UB 2: 130, 195; UB->UNSUPPORTED 2: 158, 162; UNSUPPORTED->TIMEOUT 1: 183)
   + 24 same kind, new reason (17 only lose "harness:"; new messages in 2 and 57 (memcmp not modelled), 127 (clause added), 139,
   142, 179, 184). All 24 harness rows of next2 now run main directly.
   e6ac99a (e8f4129c) -> next3: 76 = 54 kind (UNSUPPORTED->MATCH 21, EXIT->MATCH 13, UB->MATCH 9, UB->UNSUPPORTED 3,
   UNSUPPORTED->TIMEOUT 3, TIMEOUT->MATCH 2, MATCH->UB 2, MISMATCH->MATCH 1) + 22; runV (ac02a5a3) -> next3: 77 = 56 kind + 21.
   The producer's changed_rows_vs_*.tsv list exactly these 50/76/77 rows, with the same old and new values (0 diffs).
4. Counts at next3 (200): MATCH 140, UNSUPPORTED 31, UB 15, TIMEOUT 11, MISMATCH 3, EXIT 0, CRASH 0 (= interim.log and
   compare_next3.md). NATIVE_OK 177: MATCH 140 (79.1%, Wilson 72.5-84.4), MISMATCH 1 (46 widechar-3), UB 15, UNSUPPORTED 10,
   TIMEOUT 11, EXIT 0; verdicts 156, matches 140/156 = 89.7% (84.0-93.6). Control next2: 121/177 61.2-74.8, 121/148 74.8-87.1
   (as in the next2 check).
5. UB rows (labels from vtriage-20261028T190635Z/rows.tsv 5e070041: 13 real, 13 false alarms):
   leaving UB (13): false alarms 52, 80, 102, 123, 131, 144, 157, 160, 173, 196 -> MATCH; real 34 ("UB-STUCK element access into a
   non-array") -> MATCH; real 158 ("pointer arithmetic out of bounds") and 162 ("invalid memory write") -> UNSUPPORTED "type-punned
   access (byte-level access not modelled)" (cirrun printed "UB: type-punned access ..."; the runner's UB_UNSUP pattern turns
   "not modelled" into UNSUPPORTED).
   new UB (2; native OK, sanitizer none (status 0), MATCH at runV, e6ac99a and next2): 130 stdarg-4 "va_arg on a va_list after
   another function's va_arg on it (C11 7.16p3)"; 195 2006-12-11-LoadConstants "printf: an argument of another type than its
   conversion needs (C11 7.21.6.1p9)". Not triaged here.
   UB at next3 (15) = 10 real (15, 25, 36, 48, 51, 111, 127, 143, 179, 184) + 3 false alarms (1, 139, 142) + 130, 195.
6. Core-h: outer guard 0.451 (runner's count 0.390; per-row core_h sum 0.3895; 794 per-step logs sum 0.381); prep smoke 0.039;
   writing v10, pin facts, comparison and comparison test 0.000 each: 0.490 with prep. GUARD_LOGS.txt 769723e8 lists 801 logs,
   801/801 sha256 OK; its 794 per-step logs = those on disk; outer log = the delivery copy. This check: s1-s9 0.001.
7. Declared expectations, judged from the rows (s7) before reading the producer's files (s8):
   - the 11 false alarms: met for 9 (MATCH: 52, 102, 131, 173, 196, 123, 144, 160, 157); NOT met for 1 (UB, next2's message "read
     of an indeterminate or ill-typed value") and 142 (UB, now "UB-STUCK array-to-pointer decay of a non-array"; next2 "union
     member access outside the object").
   - 80: met (MATCH). 139: met (UB "invalid memory read"; next2 "read of an indeterminate or ill-typed value").
   - the 13 real UB rows stay UB: met for 10; NOT met for 34 (MATCH), 158 and 162 (UNSUPPORTED, see 5).
   - 179: met ("left shift overflow"; the row has no line; its UBSan column reports the shift of 137 by 24 places, the triage's
     :71). 48, 127, 184: met (harness 1 -> 0, no "harness:"). 158 flag: moot at next3 (UNSUPPORTED).
   - oom: 0 CRASH/oom rows (compare_next3.md: none). Declared-only rule: no row of any kind names an external object; the only
     "invalid memory read" row is 139, as in declared_only_rows.tsv (d8d020af).
   - declared_checks.tsv (62f09b2a): 31/31 verdicts equal ours; its next2/next3 fields equal the results. The producer's list in
     the brief is confirmed row by row, with three notes: (a) 130 and 195 (MATCH -> UB) had no row expectation; the addendum
     lists auditfix8's va_list-ownership and literal-printf-format checks among the kinds of change that can make a row UB;
     (b) "no row stopped at a return value of a class non-trivial for calls, not modelled" holds (0 rows at next3 and at next2)
     but is not in the addendum; (c) not in that list: 184 stays UB (met) but its message moved from the left shift of a negative
     value (the triaged real UB, :22) to "printf: an argument of the other signedness that does not fit the type its conversion
     needs (C11 7.21.6.1p9, 7.16.1.1p2)", while its UBSan column still reports "left shift of negative value -4"; 127 keeps
     next2's message, at the site the triage marked as not the real UB.
   Messages and kinds of the 7 rows (1, 142, 34, 158, 162, 130, 195) are quoted above; their triage is rog's.
SHA256SUMS: every file here except SHA256SUMS itself and the sums job's own guard/sums.log and pjobs_run4.log (written while it ran).
