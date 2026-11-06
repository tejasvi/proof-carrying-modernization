#!/usr/bin/env bash
# Pre-registration C1b (PREREG_C1b_v1.md): pass 2 of C1's 47 unknown + 7 blocked commits, C1's procedure; see
# scripts/prereg_c.py. A real run needs the C1b cert pin file (VO_CERT_PIN_ENV: cirlean bd8614f + the equiv-lean
# built on it) and a frozen copy (--frozen DIR).
#   VO_CERT_PIN_ENV=... scripts/prereg_c1b.sh [--dry-run N] [--frozen DIR] [--workers N] [--resume] [--free-slots K]
set -u
VO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 RAYON_NUM_THREADS=1
exec "$VO_ROOT/.venv/bin/python" -B "$VO_ROOT/scripts/prereg_c.py" c1b "$@"
