#!/bin/bash
# GnuCOBOL 3.2 from the <os-image> debs unpacked in third_party/gnucobol (no system install).
G="$(cd "$(dirname "$0")/.." && pwd)/third_party/gnucobol/usr"
export PATH="$G/bin:$PATH"
export LD_LIBRARY_PATH="$G/lib/x86_64-linux-gnu${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export COB_CONFIG_DIR="$G/share/gnucobol/config"
export COB_COPY_DIR="$G/share/gnucobol/copy"
export COB_CFLAGS="-I$G/include -pipe -Wno-unused -fsigned-char -Wno-pointer-sign"
export COB_LDFLAGS="-L$G/lib/x86_64-linux-gnu"
export COB_LIBS="-L$G/lib/x86_64-linux-gnu -lcob -lm -lgmp"
exec nice -n 10 "$G/bin/cobc" "$@"
