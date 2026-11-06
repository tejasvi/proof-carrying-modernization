# Check by an agent: CSUTLDTC all-input theorem (coblean pin coblean-pinM3-csutldtc-20261027T2010Z), fork of the evidence-owner session, 2026-10-27

1. Sums: pin SHA256SUMS 3e7d6fbc 992/992 rc 0 before and after; cp -rL copy (0 links) 992/992 before and after. diff -rq
   2008Z vs pin (.lake, __pycache__ aside): Examples/Csutl, examples/carddemo/csutldtc.ir.json, lakefile.toml (3915e28c;
   + lean_lib Csutl), CSUTL_PROGRESS.md, SHA256SUMS. 43 Cobol oleans identical to 2008Z; Cobol.olean be3132eb. PASS
2. IR: front end of the pin on unmodified CSUTLDTC.cbl (58c165dc), both the cd/relative command and absolute paths with
   --tab-width 4: b38f9a39 = stored IR, cmp identical. PASS
3. Statements (stmt/stmt.out): csutldtc_every binders env, m and m.size = 714 only (no CEEDAYS hypothesis); fuel 10; split
   on env.call "CEEDAYS" (ceedaysArgs m): none -> unsupported fault; [d,f,l,fb] with lengths 258/258/4/12 -> if halfOk d,
   0 <= half d <= 256, halfOk fb and halfOk (drop 2 fb): EXIT PROGRAM, out = [call CEEDAYS], bytes 632..712 = lsResult msg,
   712..714 = halfBytes |half fb|, all 714 bytes given, fillers preserved iff; else invalidData / range / invalidData;
   wrong lengths or shape -> "bad result" unsupported fault. csutldtc_result: fillers m, CEEDAYS returns both vstrings
   unchanged plus lil (4) and fb (12) with halfOk fb, halfOk (drop 2 fb) -> EXIT PROGRAM with LS-RESULT spelled out and
   RETURN-CODE. fillers_init (initState), fillers_kept (EXIT PROGRAM preserves fillers). PASS
4. Axioms: 4/4 exactly [propext, Classical.choice, Quot.sound], fresh process. PASS
5. Scan Examples/Csutl: no sorry/admit/native_decide/axiom (planted control hits). PASS
6. leanchecker: 47/47 rc 0 (42 Cobol modules + Cobol root + Prog, Model, Summ, Csutldtc), all replayed (no reuse);
   BadCtl rc 1 (kernel declaration type mismatch), GoodCtl rc 0. PASS
7. Cobol.Program.run_mono: n <= n' -> (P.run env n st).fst != outOfFuel -> P.run env n' st = P.run env n st. PASS
