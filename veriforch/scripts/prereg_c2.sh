#!/usr/bin/env bash
# Pre-registration C, study C2, exactly as frozen (PREREG_C_v2.md): see scripts/prereg_c.py for the procedure.
#   scripts/prereg_c2.sh [--dry-run N] [--frozen DIR]
# A real run makes a frozen copy of veriforch (R10) unless --frozen names one, records the pins in
# runs/prereg/C/pins.json and refuses to start when the pins do not fit C (cirlean with --link, equiv-lean built
# against it). Run it under nohup; it is a light driver, every heavy step runs under run1.sh.
set -u
VO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1
exec "$VO_ROOT/.venv/bin/python" -B "$VO_ROOT/scripts/prereg_c.py" c2 "$@"
