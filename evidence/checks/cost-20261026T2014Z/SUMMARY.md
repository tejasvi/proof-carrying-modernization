# All-in token cost of the rally items, recomputed from transcript copies (cost fork of the evidence-owner session; written 2026-10-26T20:21Z by date -u)

RESULT: every producer figure that names its transcripts reproduces to the cent (R1, R2-64, R3, R5 agents, R6, R7 helper);
R7 lead differs by $0.22 (window end); new figures: cirlean helpers and lead for R1/R2-64/R2-32; the a session
session ran on gemini-4-argon (208 calls in the R2-32 window) and needs a price; R3 phase-1 model calls $60.75 at the
5-minute cache-write rate vs $61.12 logged (1-hour rate).

Method: copies in transcripts/ (SHA256SUMS_copies.txt per subdir), evidence/tools/transcript_spend.py under g1.sh
(tools/spend1.sh; outputs in out/): Opus 5.5 list prices ($4 in, $20 out, $0.20 cache read, $5/$8 cache write 5 min/1 h),
dedup by message id over all files given, max per usage field, a call counts when its first entry lies in [since, until).
Max-per-field and first-entry totals were equal in every run. Only 2 message ids are shared between cirlean files, both
10-23 (no double counting in the rally windows).

| item | component | window (UTC) | calls | $ mine | $ producer | diff |
|---|---|---|---:|---:|---:|---:|
| R1 | veriforch workers (4), incremental | 10-25 18:53:18.001 - 10-26 09:14:33.000 | 1,662 | 427.37 | 427.37 | 0 |
| R1 | veriforch workers (4), whole transcripts | start - 10-26 09:14:33.000 | 2,399 | 540.34 | 540.34 | 0 |
| R1 | cirlean optim | 10-25 19:27:25.631 - 10-26 02:07 | 169 | 52.61 | - | |
| R1 | cirlean pobj | 10-25 19:27:16.980 - 10-26 02:54 | 305 | 59.22 | - | |
| R1 | cirlean cjlemmas | 10-25 19:27:33.693 - end (last call 22:58) | 145 | 33.20 | - | |
| R1 | cirlean floatnan | 10-25 20:30 - 10-26 02:26 | 313 | 100.55 | - | |
| R1 | cirlean lookup | 10-25 19:15:40.387 - 10-26 04:35 | 266 | 98.45 | - | |
| R1 | cirlean mutant | 10-25 20:32 - 10-26 01:33 | 219 | 42.20 | - | |
| R1 | cirlean rog | 10-25 22:31:40.408 - 10-26 04:35 | 149 | 98.95 | - | |
| R1 | cirlean vcgspeed | 10-25 20:50 - 23:17 and 10-26 01:06:59.238 - 01:26 | 173 | 42.39 | - | |
| R1 | cirlean wfglobal | 10-25 20:30:31.877 - 23:17 (from 21:00: 66 calls, 51.48) | 110 | 60.32 | - | |
| R1 | cirlean helpers, sum | | 1,849 | 587.89 | - | |
| R1 | cirlean lead | 10-25 19:15:40.387 - 10-26 04:41 | 496 | 119.60 | - | |
| R1 | TOTAL incremental (veriforch workers + cirlean helpers + lead; vo model calls $0, --no-llm) | | 4,007 | 1,134.86 | | |
| R2-64 | veriforch workers (4) | 10-26 09:14:33.001 - 14:47:40.000 | 157 | 29.59 | 29.59 | 0 |
| R2-64 | cirlean floatnan | 10-26 08:53 - 09:49 | 33 | 14.90 | - | |
| R2-64 | cirlean lead | 08:39 - 09:15 (12.04, 60 calls) + half of 09:15 - 10:06 (9.70, 61 calls) | | 16.89 | - | |
| R2-64 | TOTAL incremental | | | 61.38 | | |
| R2-32 | cirlean lead | half of 09:15 - 10:06 + 10:06 - 10:16 (2.80, 2) + 16:00 - 16:11 (3.61, 8) | | 11.26 | - | |
| R2-32 | a session (main transcript; its 4 subagents ran only at 05:3xZ) | 10-26 08:40 - 16:11 | 0 Opus; 208 gemini-4-argon | not priced | - | |
| R2-32 | gemini-4-argon tokens in that window | in 35,766,903; out 126,579; cache read 71,991,214; cache write 0 | | | | |
| R3 | veriforch three agents (whole, to 12:30:12) | start - 10-26 12:30:12.000 | 877 / 876 / 613 | 240.75 / 147.39 / 164.02 | same | 0 |
| R3 | veriforch an agent from 10-25 20:00 / whole | | 74 / 153 | 7.89 / 15.08 | same | 0 |
| R3 | phase-2 agents (yj1-3 + an agent from 20:00) | | | 560.05 | 560.05 | 0 |
| R3 | + w-theorem (whole, 343 calls) and an agent whole | | 2,862 | 635.75 | 635.75 | 0 |
| R3 | phase-1 vo model calls (runs/h_yajl_ruby_json_fuzzer/llm/usage.jsonl, 204 calls, 10-25 19:08:59 - 10-26 01:39:33) | | 204 | 60.75 (5-min cw) / 61.12 (1-h cw) | 61.12 | 0.37 at the 5-min rate |
| R5 | equiv-lean agents eq-cir 89.00 (311), eq-aeneas 57.48 (182), cir-repin 75.95 (503), rusttrn 39.94 (227) | 10-26 08:43 (R5 GO) - 15:18 | 1,223 | 262.37 | ~262 | ~0 |
| R5 | equiv-lean lead in the same window (also ran R7's clean build) | | 143 | 89.74 | ~65 (share) | lead window is an upper bound |
| R6 | StrictTS lead (48334536) | 10-26 08:39:34 - 09:53:30 | 169 | 29.13 | 29.13 | 0 (checks/r6cost-20261026) |
| R7 | JimpleLean lead | 10-26 08:45 - 10:07 (to 10:08: 242 calls, 32.45) | 239 | 32.04 | 31.82 | +0.22 |
| R7 | helper term-t4-a (whole, 09:08:25 - 09:47:17) | | 114 | 10.70 | 10.70 | 0 |
| R7 | TOTAL | | 353 | 42.74 | 42.52 | +0.22 |

Per-item totals (mine): R1 1,134.86 incremental FH (cumulative with the parse-only theorem's 394.17 already in the paper:
1,529.03); R2-64 61.38; R2-32 11.26 + the gemini-4-argon calls (unpriced); R3 635.75 agents + 61.12 phase-1 model = 696.87
(phase-2 agents only: 560.05); R5 262.37 agents + 65 (producer's coordination share; lead window 89.74) = 327.37; R6 29.13;
R7 42.74.

Shared tooling, not attributed: cirparser (10-23, an agent) 6.13 (45 calls); cirstd (10-23, an agent) 9.52
(42); string-walk helper (10-24, an agent) 0 Opus calls, 162 claude-sonnet-5-5 calls (in the paper's parse-only
total as "Sonnet string-walk 17.62"); rog's earlier frame lemma and vcgspeed's earlier profiling lie before their R1
windows and were not split out. Not counted by convention (as in the paper's parse-only paragraph): the veriforch,
cirlean-as-coordinator and coordination sessions' interleaved work outside the windows above.

Windows: veriforch windows are the producers' (AGENT_COST_*.json copies in producer/). cirlean windows follow cirlean's
message to the evidence-owner session (helper, start, end); task descriptions are left out here. Starts given only as a date were pinned to the
first lead message to that helper after the FH start (10-25 19:14:47Z): optim, pobj, cjlemmas, lookup; approximate starts
to the first lead message after the stated time: rog (~23:00 -> 22:31:40.408), vcgspeed's second window (01:1x ->
01:06:59.238), wfglobal (~21:00 -> its first FH-tagged lead message 20:30:31.877; 21:00 gives 51.48); the lead's R1 start
is the first lead-to-helper message after the FH start. End minutes are inclusive (until = next minute).
Transcripts: veriforch workers a session/subagents; cirlean a session; equiv-lean (the equiv-lean maintainer session) a session (found by
content: 52 mentions of r5-final); JimpleLean (the Java maintainer session) a session (term-t4-a in its subagents); a session
(customTitle).

Questions for producers / main: (1) price for gemini-4-argon (a session, R2-32); (2) whether veriforch workers
did R2-32 work (not found in AGENT_COST files); (3) the equiv-lean maintainer session's exact coordination share method ($65).
