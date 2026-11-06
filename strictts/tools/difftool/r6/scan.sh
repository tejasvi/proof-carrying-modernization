#!/bin/bash
# R6: rescan es-toolkit's history with the instance-aware subset check (refactor/perf/style/chore, then the rest).
cd /home/user/strictts_ws/rally
H=/home/user/strictts/scratch/hist_es
R=/home/user/strictts/scratch/projects_hist/es-toolkit
for part in rpsc other; do
  C=$(paste -sd, $H/commits_$part.txt)
  tools/run.sh 1.0 2400 node tools/difftool/dist/cli.js history --repo $R --out $H/scan2_$part --paths src --phase scan --commits "$C" > $H/scan2_$part.log 2>&1
  echo "$part rc=$? $(date -u +%H:%M:%S)" >> $H/rescan.log
done
echo "RESCAN DONE $(date -u +%H:%M:%S)" >> $H/rescan.log
