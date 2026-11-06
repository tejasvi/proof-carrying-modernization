#!/bin/bash
# R6d: the es-toolkit chain, then the remeda chain (each two lanes), recording each start stamp.
cd /home/user/strictts_ws/r6d
bash scratch/r6d/es/run_chain.sh
date -u +%Y%m%dT%H%M%SZ > scratch/r6d/re/FROM_STAMP
bash scratch/r6d/re/run_chain.sh
echo "BOTH DONE $(date -u +%H:%M:%S)" >> scratch/r6d/run_both.log
