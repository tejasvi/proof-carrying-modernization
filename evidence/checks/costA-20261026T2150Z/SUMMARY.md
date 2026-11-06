# A (migration study): all-in model cost from the sessions' records (written 2026-10-26T21:53Z by date -u)

RESULT: records sum $3,182.28 (paper: $3,180, or "about $3,200" with the unrecorded items below); my transcript
recomputation of the largest record (equiv-lean) equals its ledger total: $2,801.10 vs $2,801 for [10-24 08:30Z,
10-25 14:00Z). Opus 5.5 list prices ($4 in, $20 out, $0.20 cache read, $5 5-min write per MTok), dedup by message id.

| session | record (path, sha256) | window | A figure | how A is split |
|---|---|---|---:|---|
| equiv-lean | HANDOFF_20261023.md f9cc2b09 l.517-518 (copy here) | 10-24 08:30Z - 10-25 14:00Z | 2,398 | total $2,801 minus TRX ~$407, by agent by hand (spend_by_agent.py rows) |
| veriforch | runs/modernize/A_SPEND.md 5f2b5226 (copy here) | 10-24 08:30Z - 10-24 21:24Z | 159.37 | translation/repair/labelling calls 50.57 (exact) + runner helpers 30.30 + 60% of main 78.51 (estimate) |
| coblean | the COBOL maintainer session's 14:02Z report (E_PLAN.md l.108-112); my recompute coblean_spend_0830_now.txt | 10-24 08:30Z - 10-25 14:02Z | 343.58 | all attributed to A by coblean; its own per-file figure $347.35 double-counts 5 ids ($3.77) |
| JimpleLean | cost/README_A_SPEND.md 5a23b2a9 + A_spend_ledger_20261025.tsv fa354e3d (copies here) | 10-24 08:30:07Z - 10-25 03:00:59Z (A rows) | 281.33 | label column: A 281.33, D 24.85, mixed-unassigned 1.36, other 2.12 (sum 309.65) |
| **sum** | | | **3,182.28** | |

## My recomputation of equiv-lean (copies of the main transcript + 24 subagent jsonl, eq_transcripts.sha256)
- [10-24 08:30Z, 10-25 12:00Z): $2,674.75 (= 10-25 run and ledger $2,675); [.., 14:00Z): $2,801.10 (ledger $2,801);
  [.., 15:20Z): $2,820.55 (ledger arithmetic $2,820-2,821: totals "since 15:20Z" in later lines).
- The A/TRX split is the producer's hand attribution and not reproducible exactly: TRX agents eq-aeneas, eq-cir,
  cir-repin and rusttrn spent $351.60 in [10-25 04:28Z, 14:00Z) (116.72 + 89.41 + 81.05 + 64.42); the ledger's ~$407
  implies ~57% of main's $97.83 in that window (the 05:59Z line said ~40%). So equiv-lean A lies within ~$2,394-2,430
  depending on the main share; the ledger figure $2,398 is used.

## Not in the records (for the paper's wording)
- equiv-lean 10-25 14:00Z-15:20Z: $19.44 (main 12.00, aeneas-auto 7.45: TRX merge, README, freeze kit v2 on 751764f with
  A + TRX rows): shared, not attributed.
- veriforch after 10-24 21:24Z: coordination not recorded; A_SPEND projects ~$3/h (~$50 to the A freeze at ~10-25
  14:5xZ); translation calls unchanged ($50.57, 191 calls, re-checked 10-25 ~12:50Z per E_PLAN).
- Work before 10-24 08:30Z (semantics and bridge development) is outside every record's window.
- The sentence in sec-migration says "proof work" after stating the translation calls separately: the sum above
  INCLUDES veriforch's $50.57 of translation calls; without them it is $3,131.71.
- The coordinating sessions (d6 and successors) and the evidence owner's checks are not included.

## Files
- Copies: A_SPEND.md, README_A_SPEND.md, A_spend_ledger_20261025.tsv, HANDOFF_20261023.md, E_PLAN_copy.md,
  coblean_spend_0830_now.txt, jimplelean_spend_0830_now.txt, eq_transcripts/ (+ eq_transcripts.sha256).
- Runs (transcript_spend.py via g1.sh): eq_spend_0830_20261025T1200.txt, eq_spend_0830_20261025T1400.txt,
  eq_spend_0830_20261025T1520.txt, eq_spend_20261025T0428_20261025T1400.txt, eq_spend_20261025T1400_20261025T1520.txt.
