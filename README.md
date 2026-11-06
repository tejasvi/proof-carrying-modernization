# Proof-Carrying Modernization

LaTeX source of the paper *Proof-Carrying Modernization: LLM Translations of COBOL Batch Programs, Each Proved
Against the Original in Lean* by Tejasvi Singh Tomar (2026).

The paper shows that LLM translations of whole, unmodified COBOL programs into Rust and Java can be proved in Lean 4 to
behave like our executable semantics of the originals on every admissible input. For the eight standalone batch
programs of AWS CardDemo that our COBOL front end covers, all 16 translations are proved, as equivalences for Rust and
as refinements with partial correctness for Java.

- Paper: https://doi.org/10.5281/zenodo.23996135
- Artifact and technical report: https://doi.org/10.5281/zenodo.23996137, with the full study, the sources of our
  semantics, tools and proofs, and the records of our checks.

## Building the PDF

    ./build.sh

`build.sh` runs pdflatex and bibtex. It needs a TeX Live installation with the `acmart` class.

## Files

- `main.tex` and the `sec-*.tex` files that it inputs: the paper;
- `numbers_v2.tex`: macros for many of the numbers that the paper prints;
- `refs.bib`: the bibliography.

## Licence

The text of the paper is licensed under CC BY 4.0 (`LICENSE`).
