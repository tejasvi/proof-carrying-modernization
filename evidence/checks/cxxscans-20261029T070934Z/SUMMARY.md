RESULT: all three scans CONFIRMED for the claimed closures, with one scanner gap that has no exposure. (a) the three
SHA256SUMS verify (byvalscan 5375c61a 2059/2059, retscan 1198adc7 2343/2343, sealscan 0339317d 19201/19201, sha256sum -c
rc 0, out/sums_*.txt). (b) on d0's probes the by-value scanner flags the moved-from parameter EXPOSED/live, the untouched
parameter CLEAN/live and the trivial record not at all; the declared-only scanner finds both extern reads (ext_val,
ext_arr) and nothing for the defined global; the RETURN scanner gives NO row for the evidence-owner session's self-referential return (ret.cpp:
class S with a self-pointer, user copy constructor elided by NRVO, no destructor), which cirrun reports as an invalid read
- a gap: its non-triviality test needs an emitted copy/move constructor or destructor (cxx_ctor/cxx_dtor) in the module.
Three of each scanner's own controls reproduce (out/producer_controls_rerun.txt: b_raii_move EXPOSED, neg_trivial_dtor
CLEAN, c_trivial none; r_self SELFREF/EXPOSED, r_list SELFREF/EXPOSED, c_trivial none). (c) own screen (scripts/
own_screen_v2.py, CIR text, closures of coreexpB's 506 claimed job rows): by-value calls of non-trivial records 0 in
every study (= byvalscan 0 BYVAL); non-trivial record parameters only T2 130, 463 and 549 (two) = the 4 BYVALP; records
returned by value: the sites retscan lists (T3 50 getPath old/new, T3 142 string returns, T2 74/338/483, D2 38/61, T4
string +) plus std::allocator returns (empty class, harmless; not in retscan); records returned by value that the
emitted-member rule cannot see: only __normal_iterator and std::thread::id (trivially copyable), so the gap in (b) has no
exposure here (out/ret_trivial_by_rule.tsv); declared-only get_global: T2 189/193/463/532 __libc_single_threaded (=
sealscan) and, at the T3 pin ffab71e (not among sealscan's 11 sets; f7's earlier expo2 scan covered it),
__libc_single_threaded in exactly the 12 vacuous closures plus std::cerr and GlobalOutput address uses (escapes, as the C maintainer session
reported). (d) T3 50 getPath at ffab71e, both versions: __retval, call of basic_string's copy constructor whose FuncDecl
has model strCopyCtor (Std/Models.lean l.701: readVec other, writeVec this xs), load, ret: the returned value is a vector
of chars with no pointer into the callee's frame. (e) 10 of the 45 declared-only hits sampled, all reasons confirmed:
DEEP (T3sp 50, 142 D2; T23next2 138, 142 complete: MUSTFAIL in both versions in vacuity deep/sp_e6ac99a.tsv and
sp_424e821.tsv), SAMECB (T2 189: member and argument share control block c in the spec), NULLCB (T2 193, 463: null
control blocks in the spec), OTHERVER (C1 349ef187 new re_compile, VO2 1073521741 and e0ec012db4 re_match: the own CIR
has no declared-only global).
Coverage: own screen over coreexpB's closures (c2_jsmn, c2_trc, trx, d1/d2 tinyxml2 and zlib, musl, t2_C, t2_Cpp,
t2_recheck, t3_old/new, t4_cpp); not over the T3sp/T23next2/tier-0 packages, the T4 fac6c38 branch, C1/C2/VO2. Static
screens; direct calls only.
# An agent (fork of the evidence-owner session), written 2026-10-29T07:17:20Z by date -u. Inputs read only. Scripts: scripts/run_probes.sh, own_screen_v2.py,
# ret_any.py (own_screen.py = first version with a parameter-list parsing error, superseded). Outputs: ctl/, out/.
