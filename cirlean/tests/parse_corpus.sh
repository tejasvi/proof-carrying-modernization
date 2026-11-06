#!/bin/bash
# Parse every corpus CIR file with cir2lean, then compile a representative
# subset of the generated Lean files. One core only (shared machine).
set -u
ROOT=/home/user/cirlean
CORPUS=/home/user/cirlean_work/corpus/cir
PROBE=/home/user/cirlean_work/probe
OUT=$ROOT/tests/gen
CORE=${CORE:-17}
RUN="nice -n 10 taskset -c $CORE"
mkdir -p "$OUT"
cd "$ROOT" || exit 1
$RUN lake build cir2lean > /dev/null || { echo "build of cir2lean failed"; exit 1; }
n=0; fail=0
for f in "$CORPUS"/*.cir "$PROBE"/*.cir; do
  b=$(basename "$f" .cir | tr -c 'A-Za-z0-9_\n' '_')
  n=$((n+1))
  if ! $RUN .lake/build/bin/cir2lean "$f" "Gen.$b" "$OUT/$b.lean" > "$OUT/$b.summary" 2>&1; then
    fail=$((fail+1)); echo "PARSE FAIL $b"; cat "$OUT/$b.summary"
  fi
done
echo "parsed $((n-fail))/$n files"
echo "unknown ops (all files):"
cat "$OUT"/*.summary | grep -o 'cir\.[a-z_.]*×[0-9]*' | awk -F'×' '{c[$1]+=$2} END {for (k in c) print "  " k, c[k]}' | sort -k2 -nr
cfail=0
for b in p1 p2_libcxx_nocc test_scope_raii_cpp test_raii_loop_exits_cpp test_eh_raii_throw_cpp \
         test_swap_vector_cpp test_structs_c test_virtual_dispatch_cpp test_nf_switch_fallthrough_c \
         test_scope_early_return_dtor_cpp; do
  start=$(date +%s.%N)
  if $RUN lake env lean "$OUT/$b.lean" > "$OUT/$b.compile.log" 2>&1; then
    printf "  compiled %-36s %5.1f s\n" "$b" "$(echo "$(date +%s.%N) - $start" | bc)"
  else
    cfail=$((cfail+1)); echo "  COMPILE FAIL $b"; head -20 "$OUT/$b.compile.log"
  fi
done
[ $fail -eq 0 ] && [ $cfail -eq 0 ] && echo "ALL OK" || echo "FAILURES: parse $fail, compile $cfail"
