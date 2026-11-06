# lctest.py: planted errors (Python mutants of the leading-comma fix)

Each mutant is one exact text replacement in `tools/cobolfe/lexer.py` (the text occurs once), in the
separator test that the fix changed,

    if c in ",;" and not (pic_next and c == "," and _at(s, i + 1) not in (" ", "")):

made in place in the scratch tree (front end only, no rebuild), then `lctest.py --root <tree> --n 60
--seed 1` and the hand cases `lc_cases/v_lc1.cob`, `v_lcsep.cob` and `g_editlc.cob` (`--run`), then the
fixed file restored and its sha256 checked. The fixed tree passes 60 of 60 programs at seed 1 (ok 19,
ok-g 41), agrees with GnuCOBOL on all 28 lines of `v_lc1.cob` and `v_lcsep.cob`, and differs only in
the G-editlc lines L01-L10 of `g_editlc.cob`.

| id | the test becomes | what it plants | seed 1 | hand cases |
|---|---|---|---|---|
| MLC1 | `if c in ",;":` | the version before the fix (a comma right after PIC is always a separator) | mismatch 60: caught | v_lc1 P01-P17, v_lcsep Q07-Q11 |
| MLC2 | `… and not (pic_next and c == ","):` | a comma followed by a space or by the end of the line after PIC also begins the string | fe-error 36 (empty PICTURE: the twins written `PIC , body`), ok 19, ok-g 5: caught | v_lcsep fe-error (`PIC , ZZ9`) |

How they were run (2026-10-28, helper lc-fix): `~/coblean_runs/lcfix/scripts/lc_mutant_v1.sh ID` (check the
fixed sha256, apply `mut/ID.old` -> `mut/ID.new` with `mutate_lc_v1.py`, run, restore with `cp -p`, sha256
checked) in `~/coblean_lcfix`. The diffs are `mut/ID.diff`, the outputs `mut/ID_s1`, `mut/ID_hand.txt`.
