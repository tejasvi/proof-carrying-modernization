#!/bin/sh
# Build main.pdf from the LaTeX source.
set -e
pdflatex -interaction=nonstopmode main
bibtex main
pdflatex -interaction=nonstopmode main
pdflatex -interaction=nonstopmode main
