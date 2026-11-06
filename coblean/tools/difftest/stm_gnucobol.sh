#!/bin/bash
# CBSTM03A + CBSTM03B under GnuCOBOL on stm_ascii.py's ASCII inputs, for the comparison with the
# semantics (stm_compare.py).
# usage: tools/difftest/stm_gnucobol.sh WORKDIR   (WORKDIR holds f3.dat .. f6.dat and no src/)
# Writes WORKDIR/stdout.txt, stmt.out (80-byte records), html.out (100-byte records) and
# gnucobol_rc.txt (the program's exit status, i.e. its RETURN-CODE).
# The copy of CBSTM03A drops lines 266-291, the control-block walk (SET ADDRESS OF over the PSA,
# TCB and TIOT, and its DISPLAYs): it reads z/OS storage at fixed addresses, which a GnuCOBOL
# process does not have. Nothing after the walk reads its items. CBSTM03B is unchanged.
# Storage without VALUE starts as zeros (-fdefaultbyte=0), as in cobolrun without --mem.
set -eu
W="$(cd "${1:?workdir}" && pwd)"
R="$(cd "$(dirname "$0")/../.." && pwd)"
C=${CD:-/home/user/coblean_corpus/carddemo/src}/app
A="$C/cbl/CBSTM03A.CBL"
sed -n 266p "$A" | grep -q 'SET ADDRESS OF PSA-BLOCK   TO PSAPTR\.' || { echo "line 266 moved"; exit 2; }
sed -n 291p "$A" | grep -q '^           END-IF\.' || { echo "line 291 moved"; exit 2; }
sed -n 293p "$A" | grep -q 'OPEN OUTPUT STMT-FILE HTML-FILE\.' || { echo "line 293 moved"; exit 2; }
mkdir "$W/src" "$W/ks"
sed '266,291d' "$A" > "$W/src/CBSTM03A.CBL"
cp "$C/cbl/CBSTM03B.CBL" "$W/src/CBSTM03B.CBL"
mkdir "$W/tmp"; export TMPDIR="$W/tmp"
export LD_LIBRARY_PATH="$R/third_party/gnucobol/usr/lib/x86_64-linux-gnu"
FLAGS="-std=ibm -fbinary-truncate -fno-arithmetic-osvs -ftab-width=4 -fdefaultbyte=0"
# one loader per KSDS: fixed-length sequential records -> indexed file (random WRITE, status 00 required)
load() {  # load FILE-ID RECLEN KEYLEN
  local f=$1 n=$2 k=$3
  cat > "$W/src/LOAD$f.cbl" <<EOF
       IDENTIFICATION DIVISION.
       PROGRAM-ID. LOAD$f.
       ENVIRONMENT DIVISION.
       INPUT-OUTPUT SECTION.
       FILE-CONTROL.
           SELECT IN-FILE ASSIGN TO INFILE ORGANIZATION IS SEQUENTIAL.
           SELECT KS-FILE ASSIGN TO KSFILE ORGANIZATION IS INDEXED
                  ACCESS MODE IS RANDOM RECORD KEY IS KS-KEY
                  FILE STATUS IS KS-STATUS.
       DATA DIVISION.
       FILE SECTION.
       FD  IN-FILE.
       01  IN-REC PIC X($n).
       FD  KS-FILE.
       01  KS-REC.
           05 KS-KEY PIC X($k).
           05 FILLER PIC X($((n - k))).
       WORKING-STORAGE SECTION.
       01  KS-STATUS PIC XX.
       01  EOF-SW PIC X VALUE 'N'.
       01  CNT PIC 9(6) VALUE 0.
       PROCEDURE DIVISION.
           OPEN INPUT IN-FILE OUTPUT KS-FILE
           PERFORM UNTIL EOF-SW = 'Y'
             READ IN-FILE AT END MOVE 'Y' TO EOF-SW
               NOT AT END
                 MOVE IN-REC TO KS-REC
                 WRITE KS-REC
                 IF KS-STATUS NOT = '00'
                   DISPLAY 'WRITE STATUS ' KS-STATUS
                   MOVE 1 TO RETURN-CODE
                   STOP RUN
                 END-IF
                 ADD 1 TO CNT
             END-READ
           END-PERFORM
           CLOSE IN-FILE KS-FILE
           DISPLAY 'LOADED $f ' CNT
           STOP RUN.
EOF
  "$R/scripts/cobc.sh" -x $FLAGS -o "$W/src/load$f" "$W/src/LOAD$f.cbl"
  DD_INFILE="$W/f$f.dat" DD_KSFILE="$W/ks/f$f" "$W/src/load$f"
}
load 3 350 32
load 4 50 16
load 5 500 9
load 6 300 11
"$R/scripts/cobc.sh" -x $FLAGS -I "$C/cpy" -o "$W/src/stm" "$W/src/CBSTM03A.CBL" "$W/src/CBSTM03B.CBL"
rc=0
DD_TRNXFILE="$W/ks/f3" DD_XREFFILE="$W/ks/f4" DD_CUSTFILE="$W/ks/f5" DD_ACCTFILE="$W/ks/f6" \
  DD_STMTFILE="$W/stmt.out" DD_HTMLFILE="$W/html.out" "$W/src/stm" > "$W/stdout.txt" || rc=$?
# the exit status is the program's RETURN-CODE: stm_compare.py compares it with the model's
echo "$rc" > "$W/gnucobol_rc.txt"
echo "rc $rc; $(wc -l < "$W/stdout.txt") stdout lines, $(stat -c %s "$W/stmt.out") + $(stat -c %s "$W/html.out") bytes"
