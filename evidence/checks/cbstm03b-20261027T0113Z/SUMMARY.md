RESULT: CBSTM03B checks out. The snapshot is 2306Z plus exactly the two new files; the IR regenerates byte-identically
from the unmodified CardDemo source; CardDemo.Cbstm03b.cbstm03b_call compiles from the copy, prints exactly [propext,
Classical.choice, Quot.sound], and its module and the 43 Cobol modules replay rc 0; the seed-1 GnuCOBOL differential
agrees on all 720 lines and the RC-mutant control differs on 376 of 720, as coblean reported.

# CBSTM03B all-input theorem (checks/cbstm03b-20261027T0113Z; copy replay/cbstm03b-20261027T0113Z; written 2026-10-27T01:23Z by date -u)

## Copy and diff
- Copy of ~/coblean_snapshots/coblean-pin2306Z-cbstm03b-20261027T0112Z (cp -a; 4 symlinks, all relative inside
  third_party/gnucobol); diff -rq copy vs snapshot empty (copy_identity.txt).
- diff -rq coblean-20261024T2306Z vs the snapshot: only Examples/Cbstm03b.lean (36018f2898f6b971...) and
  examples/carddemo/cbstm03b.ir.json (38fa862f3d1269b9...) are new; every other file, all oleans included, identical;
  Cobol.olean be3132eb (diff_2306Z_vs_snapshot.txt).

## IR regeneration (regen/)
- CBSTM03B.CBL from CardDemo 59cc6c2f (git show HEAD:app/cbl/CBSTM03B.CBL, ac004f7f...; ~/veriforch/targets/carddemo_src,
  no promisor) and its 30 copybooks (each = the HEAD blob); the copy's tools/cobolfe/cobolfe.py --sub --tab-width 4 -I cpy
  gives cbstm03b.ir.json byte-identical to the snapshot's (38fa862f...).

## Compile, axioms, kernel replay
- compile_and_axioms.sh: lean (v4.35.0, the lakefile's options autoImplicit/relaxedAutoImplicit/Elab.async false) compiles
  Examples/Cbstm03b.lean to my out/lib (rc 0); a fresh process prints 'CardDemo.Cbstm03b.cbstm03b_call' depends on axioms:
  [propext, Classical.choice, Quot.sound] (logs/axioms_check.out, with the #check).
- leancheck1lp.sh over the module and its closure (43 Cobol modules incl. Cobol.olean, from the copy's build): 44/44 rc 0
  (replay/*.tsv; Examples.Cbstm03b 5.4 s, largest Cobol 29.3 s). Negative control lc_neg: BadCtl rc 1, GoodCtl rc 0.

## Statement in words (from #check)
For every environment env, every storage m of 2248 bytes, every state fs of the four files (TRNX, XREF, CUST, ACCT) and all
integers k, v: if every TRNX record has 350 bytes, every XREF record 50, every CUST record 500 and every ACCT record 300;
if, when the operation byte is K and the DD name is CUSTFILE or ACCTFILE, KEY-LN (4 bytes at 1244) decodes to k with
1 <= k <= 25; and if, when the operation is K on ACCTFILE, the first k key bytes (at 1219) decode as digits to v; then
CBSTM03B's run from storage m and files fs, with fuel 50, stops with GOBACK in exactly the state of the model call3b:
its storage and its four file states (full equality). call3b dispatches on the DD name (8 EBCDIC bytes at 1208) and the
operation byte (1216): TRNX and XREF (sequential): O = OPEN INPUT (00; 41 if already open; else the environment's open
error), R = READ next (00 with the record; 10 at end of file; 46 after it; 47 if not open for reading), C = CLOSE (00; 42
if closed); CUST and ACCT (keyed): O and C as above, K = keyed READ (the key moved into the record key field first; 00 with
the first record with that key; 23 if none; 47 if not open). The status goes to the file's status item and to
LK-M03B-RC (1217); a record read goes to the record area and, space-padded to 1000 bytes, to LK-M03B-FLDT (1248). Any
other operation copies the file's last status to RC; any other DD name changes nothing. (Cbstm03b.lean 49-147, 419.)

## GnuCOBOL differential (diff/; coblean's gen3b_v2.py 688b06a0, diff3b_v1.sh c1cbb557, compare3b_v1.py 1d2011e5, copies)
- Data: CardDemo app/data/ASCII (dailytran, cardxref, custdata, acctdata = the 59cc6c2f blobs); gen3b_v2 seed 1, 300 random
  calls -> 720 calls. GnuCOBOL 3.2 (-std=ibm, the snapshot's third_party build) 720 lines; cobolrun (front end + link.py,
  the copy's 2306Z build) 720 lines; differ 0; AGREE (logs/diff_seed1.out).
- Control: the ours side runs the mutant callee (CBSTM03B_mut.CBL 98b797ff: line 152 moves XREFFILE-STATUS instead of
  TRNXFILE-STATUS into LK-M03B-RC): 376 of 720 lines differ, DISAGREE (logs/ctl.out) = coblean's figure.

## The noted fault (outside the precondition)
- gen3b_v1 (04f477a4, coblean's first generator) at seed 1: call 400 is a K read of ACCTFILE with key '000000000' (9
  digits) and KEY-LN 11, so key bytes 10-11 are spaces: the theorem's ACCT-digits precondition fails. cobolrun stops
  with fault invalidData after 399 lines that all agree; GnuCOBOL continues to 720 (logs/fault_seed1_v1.out).

## Compute and disclosures
- Guard totals: compile 0.013, replay 0.020, differential and fault runs reported 0.000 (seconds of work; under 0.01) core-h.
- Reads outside my dirs: ~/coblean_corpus/carddemo/src/app (the driver script's fixed CD path; read only, files = the
  pinned blobs) and git reads of ~/veriforch/targets/carddemo_src with --no-optional-locks. No writes outside my dirs.
