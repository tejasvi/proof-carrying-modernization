# Normalization of the released trees

The source bundles in `sources/` and the records in `evidence/` are copies of our working trees, changed in two ways.
Everything else is byte-identical to the cited commit or frozen copy.

## Files left out

The following were left out. `sources/EXCLUDED.tsv` and `evidence/EXCLUDED.tsv` count each pattern.
- Build outputs and caches: `.lake/`, `build/`, `target/`, `.git/`, `.venv/`, `__pycache__/`. Symbolic links.
- Internal notes and coordination files (`HANDOFF*`, `PROGRESS*`, `NOTES*`, `RESUME*`, one other named progress
  file) and agent instruction files, matched without regard to case.
- Agent transcripts (`*.jsonl`) and logs (`*.log`).
- The GnuCOBOL binary packages under coblean's `third_party/`.
- The material of the harness study, which is released as it was prepared in `harness_study/`.
- Binary files that contain one of the strings that rules 1-7 below replace. `sources/EXCLUDED_BINARIES.tsv` lists them.

## Substitutions

In every remaining text file, the following substitutions were applied once, in this order:

| Rule | What is replaced | Replacement |
|---|---|---|
| 1 | the absolute path of the build account's home directory, also written with escaped slashes | `/home/user` |
| 2 | every other form of the account name (any case, joined with `_` or `-`), and one other account handle of the author | `user` |
| 3 | e-mail addresses with a common top-level domain (the `git` user of code-hosting sites is not an address) | `user@example.org` |
| 4 | fully qualified internal host names of cloud machines (`*.internal`) | `host` |
| 5 | CPU model strings | `<cpu>` |
| 6 | cloud machine-type names and machine families | `<machine-type>` |
| 7 | operating-system distribution and image names, and cloud kernel version strings | `<os-image>` |

The third-party files listed in `THIRD_PARTY.md` received rules 1 and 2 only. Their notices, including the authors'
e-mail addresses, are unchanged, as their licences require.

## Session and agent names

The work was done by AI sessions and agents under the author's direction. Their names were replaced by neutral words:
- rule 8 applies to all text files;
- rules 9, 10 and 12 apply to the evidence records and to the documentation files of the source bundles (`.md`, `.txt`,
  `.rst`, `README`);
- rule 11 applies to those files and also to comments and strings in code.

| Rule | What is replaced | Replacement |
|---|---|---|
| 8 | session names that, after rule 2, read as `user` with a two-character suffix | the session's role (see rule 11) or `a session` |
| 9 | display names of sessions; inside file names the same names | `the coordinating session`, `the orchestrator session`, `the evidence-owner session` or `a session`; `coordinator` in file names |
| 10 | agent names (checker, auditor, writer and helper agents), together with a preceding `fork` or `checker` | `an agent`; a list of agent names becomes `two agents`, `three agents`, ... |
| 11 | two-character session labels written with a leading hyphen, when neither neighbour is a letter or a digit | the session's role where the records make it clear (`the COBOL maintainer session`, likewise C, Java, TypeScript, equiv-lean; `the orchestrator session`, `the harness-study session`, `the coordinating session`, `the evidence-owner session`), otherwise `a session`; a label in parentheses right after a phrase such as "X's session" is dropped |
| 12 | the same labels without the hyphen, after `fork of`, `by`, `via`, `from`, `to`, `for`, `asked`, `told` or `per` | as in rule 11 |

Rule 11 leaves negative numbers as they are.
- In documentation it skips decimal numbers (a label followed by `.` or `,` and a digit), labels inside inline code or
  code blocks, numeric labels after an arithmetic sign, and numeric table cells.
- In code, labels that look like letters-and-digits are replaced. Purely numeric labels are replaced only when the
  text marks them as a session (a following `'s`, a preceding `by`, `via`, `per`, `once`, `from`, `of`, `to`, `for`,
  `asked`, `told`, `ruling`, or a comment marker).

AI model and product names were not changed, and neither were `~/` relative paths.

Counts:
- rule 8: 9;
- rule 9: 28;
- rule 10: 293 replacements, covering 6 more names inside lists;
- rule 11, documentation: 507, with 1 decimal number left as it is;
- rule 11, code: 337 labels replaced and 4,589 dropped after an explicit session phrase; 68 decimals and 540
  numeric literals were left as they are;
- rule 12: 19.
A name followed by its own label in parentheses was merged into one phrase once. Later, 34 agent names written with
an underscore inside file names (32 in `evidence/freeze/paper_v2_20261031T0643Z/SHA256SUMS`, 2 in
`evidence/prereg/DEVIATIONS.md`) became `agent` with their numbers kept, and one agent name in a heading of
`evidence/checks/EARLY_FREEZE_SUMMARY.md` became its role, `Referee`.

## Other projects and transcript ids

These rules apply to all text files, documentation and code alike:

| Rule | What is replaced | Replacement |
|---|---|---|
| 13 | the names of two other, private projects of the author, in any case | `another project` and `a second project`; inside paths and identifiers `another-project` and `second-project` |
| 14 | the identifiers of five session transcripts (eight hexadecimal digits) | `a session`; dropped where the text already says which session it is |

Counts:
- rule 13: 990 for the first name (704 in paths and identifiers) and 368 for the second (256 in paths and
  identifiers); 11 articles adjusted ("the other project").
- rule 14: 10.
The code of those projects is not part of this artifact. The files mention them only by name, module name, path and aggregate counts.

## The technical report

`paper/technical_report_src/` is the source of the frozen technical report, whose hash list is
`evidence/freeze/paper_v2_20261031T0643Z/SHA256SUMS`, with four changes: LaTeX comments were removed (comment lines
dropped, end-of-line comments cut to a bare `%`); the class option `review`, which numbers the lines, was dropped; and
`main.tex` gained the subtitle "Technical Report" and a line that sets the PDF producer field to `pdfTeX`.
`paper/technical_report.pdf` was built from this source. Apart from the line numbers and the subtitle, it has the same
words as the frozen build (`src/main.pdf` in that hash list); its layout and its bytes differ.

## Checking a file against its original

- `sources/NORMALIZED_HASHES.tsv` and `evidence/NORMALIZED_HASHES.tsv` give the SHA-256 of the original bytes and of
  the normalized bytes for every changed file.
- A file not listed there is unchanged. For git versions, the tree hash in `sources/SNAPSHOTS.tsv` identifies the
  commit's original tree. For frozen copies that have a manifest, its SHA-256 is in the same table.
- The pre-registrations and addenda whose hash prefixes the technical report prints are in `evidence/prereg/`. Where
  one was normalized, `evidence/NORMALIZED_HASHES.tsv` gives its original SHA-256, whose prefix the report prints.
