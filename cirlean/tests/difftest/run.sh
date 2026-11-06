#!/bin/bash
# Differential test: native execution (g++, libstdc++) against the Lean
# semantics (`cirrun` on the ClangIR of the same source).
#   LIB=libcxx (default) compiles the CIR side with libc++ headers,
#   LIB=libstdcxx with the system libstdc++ headers.
#   FILTER=regex limits the cases (matched against "file func").
#   DIFF_W=dir replaces the scratch directory, DIFF_CORE=n the core (taskset; 19).
#   CASES=file replaces cases.txt (e.g. floats_cases.txt).
#   MODE=status compares exit statuses instead of printed results (exit_cases.txt):
#     the driver returns the test function's result from main (C11 5.1.2.2.3:
#     as exit would), a file whose cases name `main` is a program with its own
#     main (no driver), and cirrun's integer is taken modulo 256.
# Otherwise a function `exit_*` takes an `int *out`: the case compares the value left in `*out`
# once the program has exited (after the atexit handlers and the static destructors).
# A source f.c (with no f.cpp) is C: gcc -std=gnu17 natively, clang in C mode for the CIR, and
# the driver declares its functions extern "C".
# Standard input is empty (/dev/null) on both sides.
# A library outside the C and C++ standard libraries (libevent: libevent_cases.txt) comes from the
# environment: DT_CFLAGS goes to both compilers (its include directory, -I...), DT_LIBS to the
# native link (its static library); both are empty by default.
# Output: one line per case: file func args | native | cirrun | MATCH/MISMATCH/UB
#   (MODE=status: native = the exit status, then the program's output lines joined by '/')
set -u
D=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$D/../.." && pwd)
LIB=${LIB:-libcxx}
FILTER=${FILTER:-.}
CASES=${CASES:-$D/cases.txt}
MODE=${MODE:-value}
DT_CFLAGS=${DT_CFLAGS:-}
DT_LIBS=${DT_LIBS:-}
W=${DIFF_W:-/home/user/cirlean_work/std_scratch/difftest}
TC=/home/user/cirlean_work/toolchain/upstream-4955d32b/bin
CX=/home/user/cirlean_work/dl_cir2c_eb2a332/cir2c-eb2a332/libcxx/include/c++/v1
RUN="nice -n 10 taskset -c ${DIFF_CORE:-19}"
CIRRUN=$ROOT/.lake/build/bin/cirrun
mkdir -p "$W"
if [ "$LIB" = libcxx ]; then CIRFLAGS="-nostdinc++ -isystem $CX"; else CIRFLAGS=""; fi

files=$(grep -v '^#' "$CASES" | grep -E "$FILTER" | awk '{print $1}' | sort -u)
for f in $files; do
  src="$D/$f.cpp"; ext=""
  if [ ! -f "$src" ] && [ -f "$D/$f.c" ]; then src="$D/$f.c"; ext='extern "C" '; fi
  drv="$W/${f}_driver.cpp"
  if [ "$MODE" = status ] && grep -v '^#' "$CASES" | awk -v f="$f" '$1==f && $2=="main" {m=1} END {exit !m}'; then
    drv=""  # a program with its own main
  else
    {
      echo '#include <cstdio>'
      echo '#include <cstdlib>'
      echo '#include <cstring>'
      grep -v '^#' "$CASES" | awk -v f="$f" '$1==f {print $2, NF-2}' | sort -u | while read -r fn ar; do
        ps=""; for ((i=0; i<ar; i++)); do ps="$ps${ps:+, }int"; done
        case "$fn" in exit_*) ps="int *";; esac
        echo "${ext}int $fn($ps);"
      done
      # runs after every other destructor (101 is the first priority not reserved)
      echo 'static int exit_out = 0, exit_case = 0;'
      echo '__attribute__((destructor(101))) static void exit_report() { if (exit_case) printf("%d\n", exit_out); }'
      echo 'int main(int argc, char **argv) {'
      echo '  int a[8] = {0}; for (int i = 2; i < argc && i < 10; ++i) a[i - 2] = atoi(argv[i]);'
      echo '  try {'
      grep -v '^#' "$CASES" | awk -v f="$f" '$1==f {print $2, NF-2}' | sort -u | while read -r fn ar; do
        as=""; for ((i=0; i<ar; i++)); do as="$as${as:+, }a[$i]"; done
        if [ "$MODE" = status ]; then echo "    if (!strcmp(argv[1], \"$fn\")) return $fn($as);"
        else
          case "$fn" in
            exit_*) echo "    if (!strcmp(argv[1], \"$fn\")) { exit_case = 1; $fn(&exit_out); return 0; }";;
            *) echo "    if (!strcmp(argv[1], \"$fn\")) { printf(\"%d\\n\", $fn($as)); return 0; }";;
          esac
        fi
      done
      echo '  } catch (...) { printf("exception\n"); return 0; }'
      echo '  return 2;'
      echo '}'
    } > "$drv"
  fi
  if [ -n "$ext" ]; then
    { $RUN gcc -std=gnu17 -O0 $DT_CFLAGS -c -o "$W/${f}_native.o" "$src" &&
      $RUN g++ -std=c++20 -O0 -o "$W/${f}_native" "$W/${f}_native.o" $drv $DT_LIBS; } 2> "$W/${f}_native.err" ||
      echo "NATIVE BUILD FAILED: $f (see $W/${f}_native.err)"
    timeout 300 $RUN "$TC/clang" $DT_CFLAGS -fclangir -emit-cir \
      -Xclang -fno-clangir-call-conv-lowering "$src" -o "$W/$f.$LIB.cir" 2> "$W/$f.$LIB.err" ||
      echo "CIR BUILD FAILED: $f (see $W/$f.$LIB.err)"
  else
    $RUN g++ -std=c++20 -O0 $DT_CFLAGS -o "$W/${f}_native" "$src" $drv $DT_LIBS 2> "$W/${f}_native.err" ||
      echo "NATIVE BUILD FAILED: $f (see $W/${f}_native.err)"
    timeout 300 $RUN "$TC/clang++" -std=c++20 $CIRFLAGS $DT_CFLAGS -fclangir -emit-cir \
      -Xclang -fno-clangir-call-conv-lowering "$src" -o "$W/$f.$LIB.cir" 2> "$W/$f.$LIB.err" ||
      echo "CIR BUILD FAILED: $f (see $W/$f.$LIB.err)"
  fi
done

nm=0; nmm=0; nub=0
while read -r f fn args; do
  case "$f" in \#*|"") continue;; esac
  echo "$f $fn" | grep -qE "$FILTER" || continue
  if [ "$MODE" = status ]; then
    # a program with its own main gets no function name
    if [ "$fn" = main ]; then out=$(timeout 20 "$W/${f}_native" $args 2>&1 < /dev/null); code=$?
    else out=$(timeout 20 "$W/${f}_native" "$fn" $args 2>&1 < /dev/null); code=$?
    fi
    nat="$code${out:+ $(printf '%s\n' "$out" | paste -sd/ -)}"
    cir=$(timeout 600 $RUN "$CIRRUN" "$W/$f.$LIB.cir" "$fn" $args 2>&1 < /dev/null | head -1)
  else
    nat=$(timeout 20 "$W/${f}_native" "$fn" $args 2>&1 < /dev/null | head -1)
    case "$fn" in
      exit_*) cir=$(timeout 600 $RUN "$CIRRUN" --show "$W/$f.$LIB.cir" "$fn" '&0' 2>&1 < /dev/null |
        awk 'NR == 1 && !/^[-0-9]/ { print; exit } /^args / { print $2; exit }');;
      *) cir=$(timeout 600 $RUN "$CIRRUN" "$W/$f.$LIB.cir" "$fn" $args 2>&1 < /dev/null | head -1);;
    esac
  fi
  cmp="$cir"; case "$cir" in exception*) cmp=exception;; esac
  key=$nat
  if [ "$MODE" = status ]; then
    key=$code
    [[ "$cir" =~ ^-?[0-9]+$ ]] && cmp=$(( (cir % 256 + 256) % 256 ))
  fi
  if [ "$key" = "$cmp" ]; then st=MATCH; nm=$((nm+1))
  else case "$cir" in UB*|"") st=UB; nub=$((nub+1));; *) st=MISMATCH; nmm=$((nmm+1));; esac
  fi
  printf '%-10s %-22s %-14s | %-12s | %-60s | %s\n' "$f" "$fn" "$args" "$nat" "${cir:0:60}" "$st"
done < "$CASES"
echo "LIB=$LIB  MATCH=$nm  MISMATCH=$nmm  UB/other=$nub"
