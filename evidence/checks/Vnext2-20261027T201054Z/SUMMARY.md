# Check by an agent: labelled V re-run at cirlean next2 (424e821), checked against prereg/V/ADDENDUM_V_rerun_next2.md (ed2f75df, 19:42:51Z)
RESULT: all 6 items PASS.
1. Seal: runV_next2/SHA256SUMS 8e60b781, 3444/3444 OK (only SHA256SUMS itself unlisted; files u+w, seal = hash list).
   results.tsv 813c52b6, 200 rows = sample_V (d0f38820), 0 order/id mismatches.
2. Inputs: runner v9 7b85c170 = v8 (d21f1ef2) + docstring, CIRRUN next2 path, default stop (stored unified diff 3f30fb10 =
   same hunks); cirrun 85da63b4; run.log line 1 names runner/sample/cirrun by sha; start 19:43:07Z (16 s after the record),
   end 20:05:36Z.
3. Rows: e6ac99a -> next2 36 changes = 31 kind (EXIT->MATCH 13, UNSUPPORTED->MATCH 10, MISMATCH->MATCH 1 initp1, UB->MATCH 1
   InlinerAndAllocas, UNSUPPORTED->UB 3, UNSUPPORTED->TIMEOUT 2, UB->UNSUPPORTED 1 BitfieldInitialization) + 5 same kind new
   reason (87, 127, 142, 160, 199); runV -> next2 34 + 5 = 39; native columns identical (0 diffs); 0 CRASH/oom rows.
   next2 kinds: MATCH 121, UNSUPPORTED 38, UB 26, EXIT 0, TIMEOUT 12, MISMATCH 3.
4. NATIVE_OK 177 at next2: MATCH 121 (68.4%, Wilson 61.2-74.8), MISMATCH 1 (widechar-3), UB 26, UNSUPPORTED 17, EXIT 0,
   TIMEOUT 12; verdicts 148, matches 121/148 = 81.8% (74.8-87.1). Control e6ac99a: 96/177 46.9-61.4, 96/123 69.9-84.5.
5. New UB rows (native OK, sanitizer none, status 0): 131 pr47925 and 144 pr88739 "read of an indeterminate or ill-typed
   value"; 173 2003-05-07-VarArgs "va_arg: argument of another type"; at e6ac99a all three were UNSUPPORTED. Not triaged.
6. Core-h: outer guard 0.511 (runner 0.405), prep smokes 0.040 + 0.031, comparison 0.000; GUARD_LOGS.txt a5b9bbe0 (873 lines).
