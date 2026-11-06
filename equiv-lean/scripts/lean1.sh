#!/bin/bash
# Check (and with -o, compile) ONE Lean file against the built workspace, without Lake.
# No Lake lock is taken, so several agents can check files at the same time.
#   scripts/lean1.sh F.lean        elaborate F.lean
#   scripts/lean1.sh -o F.lean     also write F's .olean/.ilean under .lake/build/lib/lean
# 1 Lean thread, no async elaboration, 64 GiB address-space cap (LRUN_AS in KiB), nice 10,
# timeout (default 10 min, LRUN_TIMEOUT).
ulimit -v ${LRUN_AS:-67108864}
R="$(cd "$(dirname "$0")/.." && pwd)"
W=/home/user/equivlean_work
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0
LP="$R/.lake/build/lib/lean"
# the pinned encodings: the vendor copies that lakefile.toml requires (a re-pin there moves this too)
PINS=$(sed -n 's|^path = "\.\./equivlean_work/vendor/\([^"]*\)"$|\1|p' "$R/lakefile.toml")
for d in $PINS; do LP="$LP:$W/vendor/$d/.lake/build/lib/lean"; done
LP="$LP:$W/dl/aeneas/backends/lean/.lake/build/lib/lean"
for p in "$R"/.lake/packages/*; do LP="$LP:$p/.lake/build/lib/lean"; done
export LEAN_PATH="$LP:$TC/lib/lean"
export LEAN_NUM_THREADS=1
mkdir -p "$R/.lake/tmp"; export TMPDIR="$R/.lake/tmp"
OUT=()
if [ "$1" = "-o" ]; then
  shift
  rel="$(realpath --relative-to="$R" "$1")"; mod="${rel%.lean}"
  mkdir -p "$R/.lake/build/lib/lean/$(dirname "$mod")"
  OUT=(-o "$R/.lake/build/lib/lean/$mod.olean" -i "$R/.lake/build/lib/lean/$mod.ilean")
fi
# JimpleLean precompiles its tactics and importer (precompileModules): load its shared library,
# as Lake does for the modules that import it (built by `lake build`; without it the same code
# runs in the interpreter, more slowly)
JSO=$W/vendor/$(printf '%s\n' $PINS | command grep '^JimpleLean')/.lake/build/lib/libJimpleLean_Jimple.so
DL=(); [ -f "$JSO" ] && DL=(--load-dynlib="$JSO")
exec nice -n 10 timeout "${LRUN_TIMEOUT:-600}" "$TC/bin/lean" "${DL[@]}" -DElab.async=false -DautoImplicit=false -DrelaxedAutoImplicit=false "${OUT[@]}" "$@"
