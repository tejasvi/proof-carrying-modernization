D2 commons-lang3 HELD-OUT check (fork of the evidence owner), copy replay/vo-Dl3h-20261026T0056Z
- Copy (00:56-00:58Z, replay_copy.sh): runs/prereg_d2_lang3 (2.3G) and _w1 (725M) with oleans, records
  runs/prereg/D2/lang3/heldout (summary.json 7484d746..., outcomes.tsv a3611d1a... = announced), deps/JimpleLean-20261025T0300Z
  (SHA256SUMS 133/133 OK, hash 5d577584... = pins.json bridge_snapshot_sha256sums; its 25 Jimple sources = the 0300Z snapshot's).
- Outcomes (d2_outcomes/lang3_heldout_check.txt; sample prereg/D2/heldout_lang3.tsv 990ad46b... = SHA256SUMS_D2_v1 and pins):
  100 rows = the frozen sample; 99 agree; order 50 differs (record status proved, outcome blocked). Readings
  (outcome_readings.txt): order 84 negative-cache stuck after 3 ordinary proof failures -> timeout; orders 50 and 80 are the
  bridge collision (veriforch: the scheduler verified the bridge, the statement resolved to the real method) -> infrastructure
  errors pending the crash-fix re-run (runs/prereg/D2/lang3/heldout_bridgefix/); 7 wall kills, all timeouts.
  Driver: proved 14 [0.085, 0.221], conditional 7, partial 6, blocked 31, timeout 41, infra 1.
  R6 with the readings: proved 14 [0.085, 0.221], conditional 7, partial 5, blocked 30, timeout 42, infra 2 (50, 80 pending).
- Claims (26 = 14 proved + 7 conditional + 5 partial; 50 and 80 not counted): axioms std for all (axcheck 29/29 std incl.
  50, 73, 80); kernel replay 687/687 rc 0 (w0 604, w1 59, JimpleLean 24; Jimple import-only), of which the 26 claims' closure
  is w0 24 + w1 55 + JL 25, all rc 0 or import-only (claims26_closure_verdicts.tsv). 50/80 modules replayed in the batch, not claims.
- Double/Float.compare (dcompare/): 0 of 26 claims reach them at method level; one name-level hit (order 56
  CompareToBuilder#append(ZZ)) cleared: the boolean overload has no invoke. Controls pass.
- Interface defect, labelled post hoc (iface/): of the 30 blocked units (R6), 3 carry an own-interface gap token, 1 is blocked
  only by such tokens (order 10, Functions#getAsBoolean(FailableBooleanSupplier)).
- Negative cache: 26 unit logs mention it (timeout 12, blocked 10, partial 2, conditional 1, infra 1 = order 84).
- Core-h: copy 0.005 + 689 guarded jobs 1.116 (+ one-liners under g1.sh).
