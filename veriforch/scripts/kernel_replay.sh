#!/usr/bin/env bash
# Kernel replay of veriforch theorem modules (pre-registrations C and D, R2). In the package that built a module,
# `lake env leanchecker <module>` (Lean v4.35.0) re-checks the module's declarations in Lean's kernel, independently
# of the elaborator that produced the .olean. One line per module on stdout:
#   PASS <module> (<seconds> s)    or    FAIL <module> (<seconds> s, exit <rc>): <first line of the checker's output>
# The checker's full output goes to <log dir>/<module>.log. Each check runs under scripts/run1.sh.
#
#   scripts/kernel_replay.sh [--extra-lean-path DIR]... [--log-dir DIR] [-t SECONDS] PACKAGE_DIR MODULE...
#
# --extra-lean-path: a library directory the package uses without Lake (the certificate package puts equiv-lean
# on LEAN_PATH this way). Exit status: 0 when every module passes, 1 otherwise, 2 on bad usage.
set -u
VO_ROOT="${VO_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
EXTRA=""; LOGDIR=""; T=1800
while [ $# -gt 0 ]; do
  case "$1" in
    --extra-lean-path) EXTRA="${EXTRA:+$EXTRA:}$2"; shift 2 ;;
    --log-dir) LOGDIR="$2"; shift 2 ;;
    -t) T="$2"; shift 2 ;;
    *) break ;;
  esac
done
[ $# -ge 2 ] || { echo "usage: kernel_replay.sh [--extra-lean-path DIR]... [--log-dir DIR] [-t S] PACKAGE_DIR MODULE..." >&2; exit 2; }
PKG="$(cd "$1" && pwd)" || exit 2; shift
WANT="leanprover/lean4:v4.35.0"
HAVE="$(cat "$PKG/lean-toolchain" 2>/dev/null | tr -d '[:space:]')"
[ "$HAVE" = "$WANT" ] || { echo "kernel_replay: $PKG uses toolchain '$HAVE', not $WANT" >&2; exit 2; }
LOGDIR="${LOGDIR:-$PKG/kernel_replay}"
mkdir -p "$LOGDIR"
fail=0
for mod in "$@"; do
  log="$LOGDIR/$mod.log"
  t0=$(date +%s.%N)
  # leanchecker is the one of the package's toolchain (lake env puts its bin first); the extra library path is
  # appended to the LEAN_PATH lake computes
  (cd "$PKG" && "$VO_ROOT/scripts/run1.sh" -t "$T" -m 64 -c "$(python3 -c "print(max(0.05, 1.25*$T/3600))")" -- \
     lake env bash -c 'echo "checker: $(command -v leanchecker)"; LEAN_PATH="$LEAN_PATH${0:+:$0}" exec leanchecker "$1"' \
     "$EXTRA" "$mod") > "$log" 2>&1
  rc=$?
  dt=$(python3 -c "import time; print(round(time.time() - $t0, 1))")
  out="$(grep -v '^checker: ' "$log" | grep -v '^[[:space:]]*$' | head -n 1)"
  if [ $rc -eq 0 ] && [ -z "$out" ]; then
    echo "PASS $mod (${dt} s)"
  else
    echo "FAIL $mod (${dt} s, exit $rc): ${out:-no output}"
    fail=1
  fi
done
exit $fail
