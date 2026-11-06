"""Compare the semantics' run of CBSTM03A/B with GnuCOBOL's (stm_gnucobol.sh), record by record.

usage: python3 -I tools/difftest/stm_compare.py OURS.json WORKDIR [WALK_DISPLAYS] [--addrspace AS.json]

OURS.json: cobolrun's output on WORKDIR/ir_ascii.json and WORKDIR/inputs_ascii.json (stm_ascii.py).
Compares
* the records written to STMT-FILE (file 1, 80 bytes) and HTML-FILE (file 2, 100 bytes) with
  WORKDIR/stmt.out and WORKDIR/html.out;
* the DISPLAY lines after the control-block walk (the first WALK_DISPLAYS lines, default 11, which
  GnuCOBOL's copy does not have) with WORKDIR/stdout.txt;
* with --addrspace, the walk's own DISPLAY lines with the lines that follow from the address space
  file (creastmt_inputs.py's construction), computed here without the model;
* RETURN-CODE: GnuCOBOL's exit status (WORKDIR/gnucobol_rc.txt, written by stm_gnucobol.sh) with the
  model's RETURN-CODE (0 when the program never names RETURN-CODE; else the item, which the front end
  places as the last top-level item).
Exit status 0 iff everything agrees and the run ended with GOBACK.
"""
import json, os, sys


def walk_lines(aspath):
    """The DISPLAY lines of CBSTM03A's control-block walk (its lines 266-291), followed through the
    address space file itself: PSA+536 holds the TCB address, TCB+12 the TIOT address; the TIOT starts
    with the job, step and procedure step names (8 bytes each), then 20-byte DD entries (TIO-LEN at 0,
    DD name at 4, UCB address at 17). Bytes outside the segments are zeros, as for cobolrun."""
    mem = {}
    for base, bs in json.load(open(aspath)):
        for i, b in enumerate(bs):
            mem[base + i] = b
    rd = lambda a, n: bytes(mem.get(a + i, 0) for i in range(n))
    u32 = lambda a: int.from_bytes(rd(a, 4), "big")
    tiot = u32(u32(536) + 12)
    out = [b"Running JCL : " + rd(tiot, 8) + b" Step " + rd(tiot + 8, 8), b"DD Names from TIOT: "]

    def line(e, null_text):
        return b": " + rd(e + 4, 8) + (null_text if rd(e + 17, 3) == bytes(3) else b" -- valid UCB")
    e = tiot + 24                      # BUMP-TIOT + LENGTH OF TIOT-BLOCK
    # PERFORM UNTIL END-OF-TIOT (the 4 bytes after the entry) OR TIO-LEN = LOW-VALUES, test before
    while not (rd(e + 20, 4) == bytes(4) or rd(e, 1) == bytes(1)):
        out.append(line(e, b" --  null UCB"))
        e += 20                        # LENGTH OF TIOT-SEG
    out.append(line(e, b" -- null  UCB"))
    return out


def model_return_code(ir_path, mem):
    """The model's RETURN-CODE at the end: (value, how), or (None, reason) when it cannot be read."""
    ir = json.load(open(ir_path))
    top = ir["data"]
    named = [k for k, it in enumerate(top) if it.get("name") == "RETURN-CODE"]
    if not named:
        return 0, "never named by the program"
    if named != [len(top) - 1]:
        return None, "RETURN-CODE is not the last top-level item"
    bs = bytes(mem[-2:])
    le = ir["config"].get("binaryLE", False)
    return int.from_bytes(bs, "little" if le else "big", signed=True), "item"


def main():
    args = sys.argv[1:]
    aspath = None
    if "--addrspace" in args:
        i = args.index("--addrspace")
        aspath = args[i + 1]
        del args[i:i + 2]
    ours_path, w = args[:2]
    walk = int(args[2]) if len(args) > 2 else 11
    r = json.load(open(ours_path))
    ok = r["signal"] == "stop:Cobol.StopKind.goback"
    print("end:", r["signal"])
    for fid, name, n in [(1, "stmt.out", 80), (2, "html.out", 100)]:
        ours = [bytes(e["write"]["rec"]) for e in r["out"] if "write" in e and e["write"]["file"] == fid]
        d = open(os.path.join(w, name), "rb").read()
        gnu = [d[i:i + n] for i in range(0, len(d), n)]
        bad = [i for i, (a, b) in enumerate(zip(ours, gnu)) if a != b]
        same = len(ours) == len(gnu) and not bad
        ok = ok and same
        print(f"file {fid} ({name}): {len(ours)} records, GnuCOBOL {len(gnu)}, {len(bad)} differ"
              + ("" if same else f"; first at {bad[0] if bad else min(len(ours), len(gnu))}"))
        for i in bad[:3]:
            print("  ours", ours[i])
            print("  gnu ", gnu[i])
    displays = [bytes(e["display"]) for e in r["out"] if "display" in e]
    disp = displays[walk:]
    gnu = open(os.path.join(w, "stdout.txt"), "rb").read().split(b"\n")[:-1]
    same = disp == gnu
    ok = ok and same
    print(f"displays after the walk: {len(disp)}, GnuCOBOL {len(gnu)}, {'same' if same else 'DIFFER'}")
    if aspath is not None:
        exp = walk_lines(aspath)
        same = displays[:walk] == exp
        ok = ok and same
        print(f"walk displays: {len(displays[:walk])}, from the address space {len(exp)}, "
              f"{'same' if same else 'DIFFER'}")
        if not same:
            for k, (a, b) in enumerate(zip(displays[:walk], exp)):
                if a != b:
                    print(f"  line {k}: ours {a!r} expected {b!r}")
                    break
    rc_path = os.path.join(w, "gnucobol_rc.txt")
    if os.path.exists(rc_path):
        g_rc = int(open(rc_path).read().split()[0])
        m_rc, how = model_return_code(os.path.join(w, "ir_ascii.json"), r["mem"])
        same = m_rc is not None and m_rc == g_rc
        ok = ok and same
        print(f"RETURN-CODE: model {m_rc} ({how}), GnuCOBOL exit status {g_rc}, {'same' if same else 'DIFFER'}")
    print("AGREE" if ok else "DISAGREE")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
