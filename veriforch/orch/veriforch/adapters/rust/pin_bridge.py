"""Compile equiv-lean's Aeneas bridge in a pinned copy: python3 -I pin_bridge.py EQUIVLEAN_COPY (scripts/pin_rust.sh)."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from veriforch.adapters.rust.build import build_bridge  # noqa: E402

build_bridge(Path(sys.argv[1]).resolve())
print("built", sys.argv[1])
