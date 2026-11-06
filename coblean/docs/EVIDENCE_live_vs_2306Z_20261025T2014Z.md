| row | 2306Z (recorded) | live, strengthened testers |
|---|---|---|
| V.dt_std | {"ok": 195, "ok-negzero": 5} | {"ok":195,"ok-negzero":3,"ok-packed-fc":2} 200 cases, tester exit 1 |
| V.dt_bin | {"mismatch": 2, "ok": 198} | {"mismatch":3,"ok":197} 200 cases, tester exit 1 |
| V.ct | {"lean-unsupported-recursion": 10, "lean-unsupported-resume": 2, "ok": 88} | {"lean-unsupported-recursion":10,"lean-unsupported-resume":2,"ok":88} 100 cases, tester exit 1 |
| V.dt_fe | {"ok": 98, "ok-negzero": 2} | {"ok":98,"ok-packed-fc":2} 100 cases, tester exit 1 |
| V.ct_fe | {"lean-unsupported-recursion": 2, "ok": 58} | {"lean-unsupported-recursion":2,"ok":58} 60 cases, tester exit 1 |
| V.ft | {"ok": 99, "ok-abend": 1} | {"ok":99,"ok-abend":1} 100 cases, tester exit 0 |
| V.us | {"ok": 60} | {"ok":60} 60 cases, tester exit 0 |
| V.in | {"ok": 60} | {"ok":60} 60 cases, tester exit 0 |
| V.st | {"ok": 60} | {"ok":60} 60 cases, tester exit 0 |
| V.ex_acctint | {"ok": 100} | {"ok":100} 100 cases, tester exit 0 |
| V.ex_binary | {"ok": 100} | {"ok":100} 100 cases, tester exit 0 |
| V.ex_recsum | {"ok": 100} | {"ok":100} 100 cases, tester exit 0 |
| V.tt | {"ok": 500} | {"ok":500} 500 cases, tester exit 0 |

Other rows with the same value in both: 150.

| other row | 2306Z | live |
|---|---|---|
| T7 | 3145 | 3208 |
| S2 | c28e1f6e2f27edc4742fa9dabedc3fd160b5d178889e14e06b827d8f8dad2cc9 | 69d6b1c7f5d39ff7c6747e4007fdd7448b678bae8f28a1c97eb8a3022abda11a |
| IRB.examples | (new row) | 6 of 6 IR files rebuilt identical |
| V.st_negzero | 600 | 740 746 |
| V.st_packedfc | (new row) | 738 |
| V.st_bytes | (new row) | 629 |
| V.st_trace | (new row) | 818 852 |
| V.st_okabend | 826 | 853 |
| V.dt_bin_mm | 101: GnuCOBOL shows N2=-1015755407, final N4 GnuCOBOL=535156792 model=435156792 | 197: GnuCOBOL shows N2=-0613264838, final N5 GnuCOBOL=+611167186 model=2846833 | 101: GnuCOBOL shows N2=-1015755407, final N4 GnuCOBOL=535156792 model=435156792 | 130: GnuCOBOL shows N5=+01999; ADD N5 TO N6 N4: GnuCOBOL NOT ON SIZE ERROR, N6 |
| V.hand | 28 lines compared, 0 differ | 4 programs, 4 end normally on both sides, 28 lines compared, 0 differ |
| V.stm | end: stop:Cobol.StopKind.goback file 1 (stmt.out): 1212 records, GnuCOBOL 1212, 0 differ file 2 (html.out): 6082 records, GnuCOBOL 6082, 0 differ displays after | end: stop:Cobol.StopKind.goback file 1 (stmt.out): 1212 records, GnuCOBOL 1212, 0 differ file 2 (html.out): 6082 records, GnuCOBOL 6082, 0 differ displays after |

Rows only in 2306Z: none.
