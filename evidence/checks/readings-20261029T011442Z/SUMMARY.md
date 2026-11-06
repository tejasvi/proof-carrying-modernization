RESULT: (1) PASS: memo sha256 = announced; 76/76 quotes match their cached page exactly at the cited lines (own script; planted control fires); the cached manuals carry the stated titles, form numbers and versions. (2) R1: the quoted sentences rule out both earlier readings (statement dmax: LR "not affected by operations or operands outside the function"; narrow: LR "affected by other arguments for that function"), and the inner-dmax reading is the one reading consistent with all of them, but it rests on one interpretive step (an expression argument's dmax taken without result fields) and IBM gives no worked example with digits; NIST discriminates the narrow reading only, not inner-dmax vs statement dmax. "Settled" is defensible as "the reading IBM's text supports", not as IBM-verified digits. (3) R2 PASS: no ROUNDED MODE phrase or mode keyword in the cached 6.5 LR/PG/MG, 4.2 LR/PG or the 6.4 statement pages (only hits: the ROUNDED phrase's own sentence); planted control fires. (4) R3: memo 5(c)'s proof is correct; exhaustive check of 2,911,104 cases: "always" and "when needed" store exactly the rounded exact quotient (0 mismatches); "never" differs in 436,216 cases, all with base scale = receiver places. (5) The paper states no R3 assumption today; two App F sentences on R1/F7 would change (wording below).

# An agent (fork of the evidence-owner session): check of ~/coblean_runs/inr/READINGS_MEMO.md (written 2026-10-29T01:19:06Z by date -u)
Inputs read only: the memo (sha256 318c620554ad24360c4ec5cac63c78cb9d03675f654ecef9c04b1a83c6c4be7c, 626 lines) and
~/coblean_runs/inr/ibm/ (cached pages). No web access. Paper files read by name: sec-appendix-later.tex, sec-limits.tex,
sec-migration.tex, sec-stack.tex, sec-example.tex (never sec-ub.tex).

## (1) Quotes and sources
- scripts/verify_quotes.py (own; parses section 7: key, 'local `ibm/FILE` line(s) N[-M]', the '> ' quote; normalises
  whitespace; tests the quote against the cited lines, then the whole file): out/quotes.tsv (sha8 6815c213): 76 quotes, 76
  EXACT_AT_CITED. Planted control out/memo_planted.md (one quote altered by 'not', one line number moved): NOT_FOUND
  and EXACT_ELSEWHERE reported (out/quotes_planted.tsv).
- Sources: the 14 6.4 web pages behind the R1/R2/R3 quotes carry the title "<section> | IBM Enterprise COBOL for z/OS
  6.4.0 | IBM Documentation" (the URL itself is not in the saved html; the file name is the topic id of the stated
  URL). PDFs: SC27-8713-04 (6.5 LR, 5 October 2026), SC27-8714-04 (6.5 PG, 5 October 2026), GC27-8715-04 (6.5 MG, 31
  May 2026), SC23-8528-01 and SC23-8529-01 (V4.2, August 2009), SC27-1412-05 (V3.4, November 2006), SC26-9046-04,
  SC26-9049-05, GC26-4764-05 (OS/390 & VM, September 2000), each found in the first pages of its text.

## (2) R1 in context
- LR 'Function definition and evaluation' (e64_rlinfspea.txt): R1.1 stands in a paragraph on what determines a
  function's value; "function evaluation is not affected by operations or operands outside the function. However,
  evaluation of a function can be affected by the attributes of its arguments." LR 'Arguments' (e64_rlinfsped.txt):
  argument evaluation is part of function evaluation ("When a function is evaluated, its arguments are evaluated
  individually ..."), and R1.3/R1.4: "Only those arguments at the same function level interact ... The computation of
  an arithmetic expression that appears as a function argument is affected by other arguments for that function."
  PG 'Terminology' (e64_rpinr03.txt) defines inner-dmax over a function's arguments; PG rpinr08: "The compiler
  determines the inner-dmax and outer-dmax values for an intrinsic function from the characteristics of the function."
- Assessment: R1.1 excludes the statement's receivers and outside operands; R1.4 excludes the narrow reading. No
  sentence says in so many words that the division rule's dmax inside an argument is the inner-dmax, nor gives digits;
  that is the memo's inference, the only one that fits R1.1, R1.4 and the definitions, with one stated interpretive
  step (an expression argument's dmax is taken on its own operands, since R1.1 excludes the statement's result fields).
  The ROUNDED-place exclusion (F0) also rests on R1.1's "context". So: settled in direction by IBM's text; the exact
  mechanism is a reading of it.
- NIST corroboration: by hand, IF119A (MAX = 35), IF123A (MIN = 2), IF124A (MOD = -2), IF133A (3/2 at 2 places = 1.50,
  REM 0) and IF138A (B/2 at 5 places = 3.5, SUM 82.76) pass under inner-dmax; the narrow reading fails IF133A (REM 0.25)
  and IF138A (82.26). The statement-dmax reading (receivers of 6 or 7 places) also passes all five, so NIST rules out
  only the narrow reading.

## (3) R2 absence scan
- scripts/absence_scan.py (own; hyphenated breaks joined, whitespace normalised, case-insensitive): out/absence.tsv
  (sha8 3b79f8bd) over e65_lrmvs, e65_pgmvs, e65_mg, e42_lr, e42_pg and e64 rlpdsrou, rlpsdivi, rlpscomp, rlpdssto, rlpdsaso,
  rlpdsari, rlpdsgiv, rlpdssiz: 0 matches for ROUNDED MODE, "MODE IS" within 40 characters after ROUNDED, NEAREST-AWAY,
  NEAREST-EVEN, NEAREST-TOWARD, TOWARD-GREATER, TOWARD-LESSER, AWAY-FROM-ZERO, PROHIBITED near ROUNDED. The only
  TRUNCATION-near-ROUNDED matches (e42_lr, e64_rlpdsrou, e65_lrmvs, one each) are R2.2's own sentence "truncation occurs
  unless ROUNDED is specified". Planted copy out/planted_rlpdsrou.txt (two planted ROUNDED MODE lines): all planted
  patterns found.

## (4) R3: memo 5(c)
- "Needs it" in the memo: one more decimal place is carried exactly when IBM's base scale s = max(d2 - d1, dmax) does not
  exceed the receiver's places p (s >= p always, because dmax counts the receivers), i.e. when s = p.
- Proof checked: for k >= p + 1, N = 5*10^(k-p-1) is an integer and m = 10^(k-p), so floor(T_k(q)*10^p + 1/2) =
  floor((floor(q*10^k) + N)/m) = floor((q*10^k + N)/m) = floor(q*10^p + 1/2); "always" (k = s + 1) and "when needed"
  (k = s or p + 1) both have k >= p + 1; "never" with s = p stores T_p(q). Negatives follow from oddness of truncation
  toward zero and half-away rounding.
- Exhaustive check scripts/r3_check.py (exact integers): dividends n2/10^d2 (n2 -199..199, d2 0-3), divisors n1/10^d1
  (n1 -19..19 nonzero, d1 0-2), p 0-3, other operand places 0-3, dmax = max(p, other, d2): 2,911,104 cases; "always" 0,
  "when needed" 0 mismatches against rounding the exact quotient; "never" 436,216 mismatches, none with s > p;
  truncation receivers: T_p(T_s(q)) = T_p(q) in all cases. out/r3_check.txt (sha8 e0eedc4d).
- Scope: lone quotients into the receivers (the memo's case); a quotient inside a larger expression of a ROUNDED
  COMPUTE is left open by the memo (no corpus statement, by its scan).

## (5) Paper wording (current text, App F 'Arithmetic' paragraph, sec-appendix-later.tex l.155-160)
- Current: "Under an open reading of IBM's rule for divisions inside function arguments, five more NIST divisions, in
  programs that pass and in no theorem program, carry six or seven places where IBM carries none."
  Proposed: "IBM's manuals exclude both readings of its rule for divisions inside function arguments that the session
  first gave: such a division takes the function's inner dmax, the most decimal places over that function's arguments,
  and neither the statement's receivers nor operands outside the function affect it; no IBM example gives digits for
  this case. Under that rule, five more NIST divisions, in programs that pass and in no theorem program, carry more
  places than IBM gives (six or seven against none, two or five), and the session's hand evaluation finds that all five
  tests keep their verdicts."
- Current: "...where IBM gives it at least those of the argument's own operands, under either reading of its rule."
  Proposed: "...where IBM's rule gives it the function's inner dmax, at least the places of the argument's own operands."
- R3: the named files state no ROUNDED-place assumption, and no paper theorem program divides into a ROUNDED receiver
  (memo's scan: CardDemo 0, pins 0; the two hits are coblean's acctint examples, not paper theorems). No change needed;
  if a sentence is wanted: "IBM's Programming Guide says that with ROUNDED one more decimal place 'might be carried for
  accuracy if necessary'; the semantics always carries it, which stores the same value as carrying it only when the
  receiver's rounding needs it."
- R2: the named files do not mention ROUNDED MODE; no change.
