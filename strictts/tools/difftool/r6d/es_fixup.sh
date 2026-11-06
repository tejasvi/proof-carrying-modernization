#!/bin/bash
# R6d es post-processing, steps redone after post_run.sh: (1) the confirmation files of the es run's
# window only (from its start to the remeda run's start; post_run.sh's collect also took 3 blocks of the
# remeda run, which had started in the same checkout; that attempt is kept in scratch/r6d/es_confirm_mixed/),
# (2) the replay (post_run.sh's failed: the replay script's relative path to typescript), (3) the table.
cd /home/user/strictts_ws/r6d
D=scratch/r6d/es; P=/home/user/strictts/scratch/hist_es
LOG=$D/post_fixup.log
say() { echo "$(date -u +%Y-%m-%dT%H:%M:%SZ) $*" >> "$LOG"; }
FROM=$(cat $D/FROM_STAMP); TO=$(cat scratch/r6d/re/FROM_STAMP)
say "start: HEAD $(git rev-parse HEAD) window $FROM .. $TO"
[ -e scratch/r6d/es_confirm_mixed ] && { say "es_confirm_mixed exists: stop"; exit 1; }
mv $D/evidence_confirm scratch/r6d/es_confirm_mixed
tools/run.sh 0.05 300 node $D/collect_confirm.js scratch/difftool "$FROM" $D/evidence_confirm "$TO" >> "$LOG" 2>&1
say "collect_confirm rc=$?"
tools/run.sh 0.3 590 node $D/cex_replay_v2.js $D/chunks "$P" $D/replay_v2 >> "$LOG" 2>&1
say "replay rc=$?"
TABLE_NAME=r6d_table.tsv DRAFT_NAME=R6D_draft.md tools/run.sh 0.05 120 node $D/report.js $D "$P" >> "$LOG" 2>&1
say "report rc=$?"
say "FIXUP DONE"
