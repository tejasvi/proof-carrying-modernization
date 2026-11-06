#!/usr/bin/env bash
# Compile one example directory with javac and convert it to Jimple with Soot 4.7.1
# (the invocation of JimpleLean's tools/difftest.sh, with --release 17).
#   examples/java/build_jimple.sh NAME   examples/java/NAME/*.java -> EquivLean/Demo/Gen/Jimple/NAME/*.jimple
# Class files and logs go to the scratch directory; JDK 17, 1 CPU, nice 10.
set -eu
N="$1"
[[ "$N" =~ ^[a-z0-9_]+$ ]] || { echo "bad name $N" >&2; exit 2; }
R=/home/user/equivlean
S=/home/user/equivlean_work/scratch/eq-jimple
JDK=/usr/lib/jvm/java-17-openjdk-amd64/bin
SOOT=/home/user/jimplelean_work/toolchain/soot-4.7.1-jar-with-dependencies.jar
JFLAGS="-XX:+UseSerialGC -XX:ActiveProcessorCount=1 -XX:-UsePerfData -Xmx1g -Djava.io.tmpdir=$S/tmp"
export TMPDIR=$S/tmp
ulimit -v 67108864
C=$S/build/$N/classes
J=$R/EquivLean/Demo/Gen/Jimple/$N
mkdir -p "$S/tmp" "$C" "$J"
rm -f "$C"/*.class "$J"/*.jimple
nice -n 10 timeout 300 $JDK/javac -J-XX:+UseSerialGC -J-XX:ActiveProcessorCount=1 -J-XX:-UsePerfData \
  -J-Djava.io.tmpdir=$S/tmp --release 17 -nowarn -d "$C" "$R"/examples/java/$N/*.java
nice -n 10 timeout 300 $JDK/java $JFLAGS -cp "$SOOT" soot.Main -pp -allow-phantom-refs \
  -cp "$C" -process-dir "$C" -f J -d "$J" > "$S/build/$N/soot.log" 2>&1 || { tail -20 "$S/build/$N/soot.log"; exit 1; }
ls -la "$J"
