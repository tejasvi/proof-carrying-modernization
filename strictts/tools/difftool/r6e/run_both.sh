#!/bin/bash
# R6d: the es-toolkit chain, then the remeda chain (each two lanes), recording each start stamp.
cd /home/user/strictts_ws/r6e
bash scratch/r6e/es/run_chain.sh
date -u +%Y%m%dT%H%M%SZ > scratch/r6e/re/FROM_STAMP
bash scratch/r6e/re/run_chain.sh
echo "BOTH DONE $(date -u +%H:%M:%S)" >> scratch/r6e/run_both.log
