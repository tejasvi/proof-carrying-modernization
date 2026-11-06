RESULT: NOT CONFIRMED as a build of e1c9a85; CONFIRMED for the producer's oleans. Every check of the producer's build passes: the kernel replay of the closure of all 176 claimed theorems (2371 modules: 649 of 649 replayed by leanchecker with rc 0, 1722 carried over from the next2 re-check with byte-identical oleans and olean-import closures), leanchecker --fresh on the producer's 6 roots (6 of 6 rc 0), 171 of 176 statements identical to fac6c38 plus the 5 announced changes, and axioms (175 use exactly propext, Classical.choice, Quot.sound; 1 uses none). But 2 of the 109 modules recompiled here from the committed sources against the producer's final oleans do not compile: EquivLean.Demo.XLang.Jsmn.CPrim, EquivLean.Demo.XLang.Jsmn.CTok ('simp' made no progress at 'simp only [Mem.endScope]'; 2 more stopped at the 32 GiB address-space cap: EquivLean.Demo.XLang.Jsmn.CString, EquivLean.Demo.XLang.TinyRegex.CCompile). Their oleans were compiled before the producer's last change to EquivLean.Bridge.Cir.Tactic and the rebuild of its oleans, so the commit does not reproduce them; Jsmn.CPrim holds the claimed jsmn_parse_primitive_pspec.

# Check of equiv-lean unified-next3 e1c9a85 (cirlean 7c73739, coblean 20261028T0109Z unchanged)
An agent of the evidence-owner session; check dir /home/user/fv_paper/evidence/checks/next3el-20261030T153456Z (stamp from date -u at creation; first script start 2026-10-30T15:38:27Z). Inputs read
only: the producer worktree ~/equivlean_wt_next3 and ~/equivlean/.git (git reads with GIT_ALLOW_PROTOCOL=file, no optional
locks; no promisor, no remote), ~/cirlean/.git, ~/equivlean_work/{vendor,dl,logs}, ~/cirlean_frozen/next3_7c73739_20261030,
the cirlean freeze manifest, and the two next2 replay copies (first copy RP2, re-check copy C2). Replay copy /home/user/fv_paper/replay/next3el-20261030T154128Z.
Every script, Lean and leanchecker run, multi-file scan and interpreter run was one job under coreh_guard_v2 (ulimit -v 32 GiB,
LEAN_NUM_THREADS=1) through pjobs_v3 (N <= 8, 450 150 2). Template: checks/next2-20261028T161321Z and its re-check.

## 1. Commit and files: PASS
- HEAD = e1c9a85 full sha: yes; branch: refs/heads/unified-next3; parent = fac6c38 full sha, single parent: yes
  (parent fac6c38f7a5d5b8d199f808a8a2fbb27e1cfdb95 (parents: 1)).
- tracked: commit 2893, worktree 2893, diff bytes 0; untracked, not ignored: 0; index vs commit: 0 paths differ; ignored entries: .lake/ .
- Promisor/remote: /home/user/equivlean/.git: remote/partialclone config lines 0, .promisor packs 0, alternates no, remotes 0; /home/user/cirlean/.git: remote/partialclone config lines 0, .promisor packs 0, alternates no, remotes 0.
- fac6c38..e1c9a85: status A: 1, status M: 33 (changed files: 34; .lean: 32); the added file is EquivLean/Bridge/Cir/Congr.lean.
- Producer patch: producer patch = git diff fac6c38 e1c9a85: identical (sha256 261d4c17569147ef3f90e3962fe7c7509783facd767cc98c8ff3c1a74df93c97); patch file list = git name-status list (34 files); patch: new files 1, deleted 0, renames 0.
- Forbidden tokens (sorry, admit, native_decide, axiom, extern, implemented_by, unsafe, ofReduceBool, skipKernelTC, decide +kernel
  and kernel := true; word match) in the 32 changed .lean files at e1c9a85: files scanned: 32; token hits (word match): 0; added-line token hits: 0.
  The only case-insensitive substring hits in added lines are 'extern' inside the identifier 'external' (substring (any case) in added lines: extern 16).
- Branches: refs/heads/master 8ed869e, refs/heads/unified 8ed869e, refs/heads/unified-next2 fac6c38, refs/heads/unified-next3 e1c9a85.

## 2. Pins: PASS
- lakefile.toml / lake-manifest.json: the only changes are the cirlean path: -   "dir": "../equivlean_work/vendor/cirlean-424e821", | +   "dir": "../equivlean_work/vendor/cirlean-7c73739", | -path = "../equivlean_work/vendor/cirlean-424e821" | +path = "../equivlean_work/vendor/cirlean-7c73739".
- cirlean 7c73739 = 7c73739c0cb655d07f4a452cc3317cafb2b1bcb4; vendor/cirlean-7c73739 tracked: git 663, vendor 663, diff bytes 0; vendor files outside .lake: 664; not tracked: .git ; tracked but missing: 0; symlinks: 0.
- vendor/cirlean-7c73739 vs frozen tree (all files incl. .lake, diff -rq): rc=0, 0 differences; vendor files with link count > 1: 2452 of 2452 (the vendor dir is a hard-link copy of the frozen tree);
  vendor .lake/build vs cirlean freeze MANIFEST_build.sha256 (1017 entries): rc=0, failure lines 0 (vendor .lake/build files: 1788).
- Other pins, unchanged since fac6c38's check (same paths in both commits; contents compared with both next2 copies):
  vendor/coblean-20261028T0109Z: files 2114 (symlinks 0); diff -rq vs C2 rc=0 lines 0; vs RP2 rc=0 lines 0
  vendor/strictts-a15926a: files 2304 (symlinks 0); diff -rq vs C2 rc=0 lines 0; vs RP2 rc=0 lines 0
  vendor/JimpleLean-20261026T2035Z: files 570 (symlinks 0); diff -rq vs C2 rc=0 lines 0; vs RP2 rc=0 lines 0
  dl/aeneas/backends/lean: files 4698 (symlinks 0); diff -rq vs C2 rc=0 lines 0; vs RP2 rc=0 lines 0
- Copy: 2026-10-30T15:41:28Z -> /home/user/fv_paper/replay/next3el-20261030T154128Z; copied 2026-10-30T15:43:31Z; symlinks in copy: 0; files in copy: 187507; files with link count > 1: 0.
  copy olean files hashed: 30907 (.olean 11941, .server 9483, .private 9483) 2026-10-30T15:43:39Z; copy = sources: all olean files identical; olean files at the sources (find -L over the copied roots): 30907.
- The next2 copies now equal their records: C2 now (3616 files) vs recorded c2_olean_sha256.txt: compared 2748, identical 2748, not in the record 868; RP2 now (30763 files) vs recorded copy_olean_sha256.txt: compared 11797, identical 11797, not in the record 18966.
- Olean files of this copy byte-identical to the next2 copies (paths mapped equivlean_wt_next3 -> equivlean_wt_next2, cirlean-7c73739 ->
  cirlean-424e821; RP2 = first next2 copy, C2 = re-check copy = the final fac6c38 build, which holds no Mathlib-side packages):
  EquivLean olean files 2220 | RP2 same 1537 differ 682 absent 1 | C2 same 1582 differ 637 absent 1
  EquivLean part files 330 | RP2 same 330 differ 0 absent 0 | C2 same 330 differ 0 absent 0
  JimpleLean-20261026T2035Z olean files 28 | RP2 same 28 differ 0 absent 0 | C2 same 28 differ 0 absent 0
  TOTAL olean files 11941 | RP2 same 11006 differ 791 absent 144 | C2 same 2002 differ 746 absent 9193
  TOTAL part files 18966 | RP2 same 18966 differ 0 absent 0 | C2 same 868 differ 0 absent 18098
  aeneas olean files 269 | RP2 same 269 differ 0 absent 0 | C2 same 269 differ 0 absent 0
  aeneas part files 538 | RP2 same 538 differ 0 absent 0 | C2 same 538 differ 0 absent 0
  cirlean-7c73739 olean files 201 | RP2 same 17 differ 109 absent 75 | C2 same 17 differ 109 absent 75
  coblean-20261028T0109Z olean files 68 | RP2 same 68 differ 0 absent 0 | C2 same 68 differ 0 absent 0
  pkg:LeanSearchClient olean files 4 | RP2 same 4 differ 0 absent 0 | C2 same 0 differ 0 absent 4
  pkg:LeanSearchClient part files 8 | RP2 same 8 differ 0 absent 0 | C2 same 0 differ 0 absent 8
  pkg:Qq olean files 14 | RP2 same 14 differ 0 absent 0 | C2 same 0 differ 0 absent 14
  pkg:Qq part files 28 | RP2 same 28 differ 0 absent 0 | C2 same 0 differ 0 absent 28
  pkg:aesop olean files 132 | RP2 same 132 differ 0 absent 0 | C2 same 0 differ 0 absent 132
  pkg:aesop part files 264 | RP2 same 264 differ 0 absent 0 | C2 same 0 differ 0 absent 264
  pkg:batteries olean files 195 | RP2 same 195 differ 0 absent 0 | C2 same 0 differ 0 absent 195
  pkg:batteries part files 390 | RP2 same 390 differ 0 absent 0 | C2 same 0 differ 0 absent 390
  pkg:coblean olean files 68 | RP2 same 0 differ 0 absent 68 | C2 same 0 differ 0 absent 68
  pkg:importGraph olean files 35 | RP2 same 35 differ 0 absent 0 | C2 same 0 differ 0 absent 35
  pkg:importGraph part files 70 | RP2 same 70 differ 0 absent 0 | C2 same 0 differ 0 absent 70
  pkg:mathlib olean files 8643 | RP2 same 8643 differ 0 absent 0 | C2 same 0 differ 0 absent 8643
  pkg:mathlib part files 17286 | RP2 same 17286 differ 0 absent 0 | C2 same 0 differ 0 absent 17286
  pkg:plausible olean files 13 | RP2 same 13 differ 0 absent 0 | C2 same 0 differ 0 absent 13
  pkg:plausible part files 26 | RP2 same 26 differ 0 absent 0 | C2 same 0 differ 0 absent 26
  pkg:proofwidgets olean files 13 | RP2 same 13 differ 0 absent 0 | C2 same 0 differ 0 absent 13
  pkg:proofwidgets part files 26 | RP2 same 26 differ 0 absent 0 | C2 same 0 differ 0 absent 26
  strictts-a15926a olean files 38 | RP2 same 38 differ 0 absent 0 | C2 same 38 differ 0 absent 0
  The producer's EquivLean counts '1,582 identical, 638 rebuilt' hold (C2 column); its other figure '1,586 non-CIR .olean files' matches no count here.
- Toolchain: lean bf8d54e4714cc4b0, leanchecker 12c38901cdbfab17 (v4.35.0); toolchain olean files: 7632; list sha256 74e78f7800639a75e42b83ca9089ea9131de1f2b42cbd609aadfb50983f2c8e9.

## 3. Statements (stmt/, clos/)
Method (template's): fresh Lean processes print every theorem of the dumped modules (pp.fullNames, pp.proofs) with its type's
Expr hash and the hashes of its statement dependencies (scripts/stmt_body.lean = the template's StmtDump body), at fac6c38 on the
next2 re-check copy (leanpath_fac6c38.txt) and at e1c9a85 on this copy (leanpath_next3.txt): group processes plus one process per
Modernize module on each side. Dumped modules (181): the 89 claimed modules, the 32 changed .lean modules, and every
non-generated EquivLean module whose .olean differs from next2's (no rebuilt Demo.Gen module declares a theorem). Claimed set:
claimed176.tsv (= the template's, sha256 prefix 1d7d39a8c4371ddd), the file the producer's row numbers refer to.

### 3a. The 176 claimed theorems
- Found at both commits: 176 of 176. Identical text and type hash: 171. Text changed: 5 (the producer's 5). Same text
  with another type hash: 0.
- All dumped theorems: e1c9a85 2212, fac6c38 1856; 1835 identical text and hash, 6 same text with another type
  hash (renumbered match_/_proof_ auxiliaries and CIR.Exit's new longjmp constructor: holds_* elimination lemmas, TinyRegex
  mp_step/mp_nomatch), 15 text changes, 356 new, 0 removed.

### 3b. The 5 changed claimed statements (the lines that differ, ignoring indentation; all other lines identical; full texts in stmt/changed_text.txt)
1. EquivLean.Demo.Cir.Musl.musl_strlen_nonchar_ub (claimed row 91):
    new:     (∃ es tlen, ty = (CIR.Ty.int es 8).array tlen) →
   WEAKER: the new statement adds the hypothesis that block b is a char array, so it covers only char-array blocks; the
   conclusion (strlen on &b[i], where element i holds an int value outside [-128, 255], has no normal outcome) is unchanged.
   Needed at next3: cirlean 7c73739 types every load by the block's type, and a char access into a non-char object reads a
   byte of that object (defined behaviour; CHANGES_next3, "Character access"), so the invalid-char conclusion holds only for
   char arrays. The kept hypothesis (i + 1) % 8 != 0 is next2's alignment encoding; the theorem is proved with it at next3.
2. EquivLean.Demo.Cir.Musl.musl_strlen_aligned_ub (claimed row 99):
    old:       (i + 1) % 8 = 0 →
    new:       (if b + 1 < 2 ^ 29 ∧ i < 2 ^ 32 then i else i + 1) % 8 = 0 →
   DIFFERENT (neither implies the other): both hypotheses say "the integer value of s = &b[i] is a multiple of 8", each in
   its pin's pointer-to-integer conversion. next2 converted &b[i] to an index code equal to i + 1 mod 8; cirlean 7c73739
   converts it to the flat address (b + 1) * 2^32 + i when b + 1 < 2^29 and i < 2^32 (Ctx.addrOf?), and to a code equal to
   i + 1 mod 8 otherwise (Ctx.otherAddr). The conclusion (no normal outcome of strlen) is unchanged. Inside the flat range
   the covered offsets move from i = 7 to i = 0 (mod 8); outside it the two statements coincide. Needed because musl's
   strlen tests (uintptr_t)s % ALIGN, which next3 evaluates on flat addresses. The producer's report gives the old
   hypothesis as i % 8 = 0; the fac6c38 statement reads (i + 1) % 8 = 0.
3. EquivLean.Demo.Cir.Musl.musl_memcpy_cex_ub (claimed row 94):
    new:             m.next < 2 ^ 29 →
4. EquivLean.Demo.Cir.Musl.musl_memcpy_ne_model (claimed row 95):
    new:             m.next < 2 ^ 29 →
    old:                   [CIR.Val.ptr (CIR.Ptr.loc bd [CIR.PathElem.idx 0]), CIR.Val.ptr (CIR.Ptr.loc bs [CIR.PathElem.idx 0]),
    old:                     CIR.Val.int 7]
    new:                     [CIR.Val.ptr (CIR.Ptr.loc bd [CIR.PathElem.idx 0]),
    new:                       CIR.Val.ptr (CIR.Ptr.loc bs [CIR.PathElem.idx 0]), CIR.Val.int 7]
    old:                   [CIR.Val.ptr (CIR.Ptr.loc bd [CIR.PathElem.idx 0]), CIR.Val.ptr (CIR.Ptr.loc bs [CIR.PathElem.idx 0]),
    old:                     CIR.Val.int 7]
    new:                     [CIR.Val.ptr (CIR.Ptr.loc bd [CIR.PathElem.idx 0]),
    new:                       CIR.Val.ptr (CIR.Ptr.loc bs [CIR.PathElem.idx 0]), CIR.Val.int 7]
   3 and 4 are WEAKER: each adds the bound m.next < 2^29 (every allocated block, bs and bd included, lies in the flat-address
   range); the conclusions (musl_memcpy on the 7-byte counterexample arrays has no normal outcome; its outcome differs from
   the reference model's) are unchanged. Needed because musl's memcpy branches on the alignment of (uintptr_t)d and s, which
   next3 computes from flat addresses only for blocks with b + 1 < 2^29; the bound fixes the alignment the proof follows.
   The other differing lines of 4 are the same argument list, re-wrapped by the pretty-printer.
5. EquivLean.Demo.XLang.Jsmn.C.jsmn_parse_primitive_pspec (claimed row 88):
    old: ∀ (js : List ℕ) (n : ℕ) (st : EquivLean.Demo.XLang.Jsmn.St) (m : CIR.Mem) (bp bj bt : ℕ) (kp kj kt : CIR.BlockKind)
    old:   (tyJ tyT : CIR.Ty),
    new: ∀ (js : List ℕ) (n : ℕ) (st : EquivLean.Demo.XLang.Jsmn.St) (m : CIR.Mem) (bp bj bt : ℕ) (kp kj kt : CIR.BlockKind),
    old:           { kind := kj, alive := Bool.true, ty := tyJ, val := CIR.Val.arr (List.map (fun b => CIR.Val.int ↑b) js) } →
    new:           { kind := kj, alive := Bool.true, ty := (CIR.Ty.int Bool.true 8).array js.length,
    new:             val := CIR.Val.arr (List.map (fun b => CIR.Val.int ↑b) js) } →
    old:             { kind := kt, alive := Bool.true, ty := tyT,
    new:             { kind := kt, alive := Bool.true, ty := (CIR.Ty.record "jsmntok").array n,
    old:                                                     { kind := kt, alive := Bool.true, ty := tyT,
    new:                                                     { kind := kt, alive := Bool.true,
    new:                                                       ty := (CIR.Ty.record "jsmntok").array n,
   WEAKER (an instance of the old statement): the block types, free before (tyJ tyT : CIR.Ty), are fixed to the char array of
   length js.length for the input and the jsmntok array of length n for the tokens, in the hypotheses and in the
   postcondition's description of the token block; the contract is otherwise unchanged. These are the types the callers'
   contracts already state (parse_string_pspec has the same block types at e1c9a85). Needed because next3 computes pointer
   arithmetic in the pointee's units from the block's type and member access through the block's record type.

### 3c. Non-claimed theorems whose text changed (10)
- The producer's 7 helpers (confirmed):
  memcpy_model_zero    new:   CIR.Std.validMemArg m Bool.true d = Bool.true →
  memcpy_model_zero    new:     CIR.Std.validMemArg m Bool.false s = Bool.true →
  (WEAKER: next3's memcpy model checks both pointers also for n = 0; discharged inside musl_memcpy_refines, whose statement is
  unchanged. The producer wrote these hypotheses as 'Std.validMemArg ctx m pd 0'.)
  jsmn_fill_token_pspec, jsmn_alloc_token_pspec (Jsmn.CTok), final_scan_elim (Jsmn.CScan), comma_search_elim, close_second_elim,
  close_first_elim (Jsmn.CSearch): the token block's type, free before (tyT), becomes the jsmntok array (WEAKER), e.g.
  jsmn_alloc_token_pspec    old: ∀ (m : CIR.Mem) (bp bt : ℕ) (kp kt : CIR.BlockKind) (tyT : CIR.Ty) (pos tn : ℕ) (sup : ℤ) (N : ℕ) (vs : List CIR.Val)
  jsmn_alloc_token_pspec    new: ∀ (m : CIR.Mem) (bp bt : ℕ) (kp kt : CIR.BlockKind) (pos tn : ℕ) (sup : ℤ) (N : ℕ) (vs : List CIR.Val)
  jsmn_alloc_token_pspec    old:     m.blocks bt = Option.some { kind := kt, alive := Bool.true, ty := tyT, val := CIR.Val.arr vs } →
  jsmn_alloc_token_pspec    new:     m.blocks bt =
  jsmn_alloc_token_pspec    new:         Option.some { kind := kt, alive := Bool.true, ty := (CIR.Ty.record "jsmntok").array N, val := CIR.Val.arr vs } →
  jsmn_alloc_token_pspec    old:                                       { kind := kt, alive := Bool.true, ty := tyT,
  jsmn_alloc_token_pspec    new:                                       { kind := kt, alive := Bool.true, ty := (CIR.Ty.record "jsmntok").array N,
- 3 more, in EquivLean.Bridge.Cir modules outside the producer's comparison set (its user_thms lists cover Demo modules only):
  EquivLean.Cir.evalF_mono (Bridge.Cir.Loops; source unchanged: its statement contains the unfolded CIR evaluator, which next3
  redefines); EquivLean.Cir.holds_evalCall_body_elim (Bridge.Cir.Tactic; adds the hypothesis autoParam (fd.special !=
  CIR.SpecialMember.dtor) and the Exit.longjmp case of the unfolded call); EquivLean.Cir.holds_evalRegion_cons_elim
  (Bridge.Cir.Tactic; the memory after a region, Mem.endScope of the final state, becomes Exit.leaveMem of the exit).
- The producer's own lists (user_thms_next2/next3.tsv) give the same changes in its scope: producer lists: next2 604 rows, next3 613;      12 DIFF       9 NEW .

### 3d. Meaning through definitions (clos/: closure of each claimed statement over the project packages, constant hashes)
- 122 of 176 closures identical at both commits (COBOL (Modernize) 73, Thrift Java 29, Adler-32 4, tiny-regex 2, Thrift Rust 8, TypeScript 6; the XLang rows among them, Adler-32 4, tiny-regex 2, are Rust-side).
- 54 changed. 50 reach changed cirlean 7c73739 constants (Thrift C++ 9, musl 11, jsmn 4, Adler-32 21, tiny-regex 5): their meaning is now next3's semantics, with
  unchanged text (45) or the text changes of 3b (5); they also reach the regenerated program definitions
  (EquivLean.Demo.Gen.Cir.*, Demo.Cir.Musl.Gen.*). Over all claimed closures: CIR: same 660, changed 431, new 1146, gone 129.
- The other 4 (EquivLean.Demo.XLang.Jsmn.Rust.rust_spec, EquivLean.Demo.XLang.Jsmn.rust_rspec, EquivLean.Demo.XLang.TinyRegex.Rust.re_compile_eq, EquivLean.Demo.XLang.TinyRegex.Rust.re_match_spec) differ only by renumbered match auxiliaries (Jsmn.step.match_2 -> match_3,
  TinyRegex.compStep.match_2 -> match_3; s6/clos_constant_changes_by_theorem.tsv) and the definitions naming them. Both model modules import
  only Init and their sources are unchanged. AuxRenameCmp: EquivLean.Demo.XLang.TinyRegex.Model equal_after_renaming equal=196 (s6/auxrename.out); EquivLean.Demo.XLang.Jsmn.Model equal_after_renaming equal=107 (s6/auxrename_v2.out, with the private matcher names);
  control with a wrong renaming: differ. So their meaning is unchanged.
- Constants that changed in the claimed closures, by package: CIR: same 660, changed 431, new 1146, gone 129; EquivLean: same 4074, changed 116, new 2, gone 2; all other packages unchanged.
- OleanCmp3 (s6/): of the 637 EquivLean oleans that differ from C2, 15 have equal constants, 88 are equal up to
  auxiliaries, 534 differ (515 of them generated Demo.Gen modules); of the 45 CIR modules in both pins, 17 equal, 5 up to auxiliaries,
  23 differ.

## 4. Axioms (fresh processes on this copy): PASS
- 89 processes, one per claimed module, '#print axioms' for each claimed theorem (last lines: 89 rc=0): 176 lines; 175 exactly
  [propext, Classical.choice, Quot.sound]; 1 fewer: EquivLean.Demo.Thrift.Java.thrift_classes_length ((none)); 0 others; claimed theorems without an axiom line: 0.
- Planted controls: Ctl.lean (the template's, importing EquivLean.Bridge.TS.Sets) and Ctl2.lean (in the CIR environment of
  EquivLean.Demo.Cir.Musl.StrlenRefines):
  Ctl: plantedSorry -> sorryAx
  Ctl: plantedAx -> plantedAxiom
  Ctl: plantedNative -> plantedNative._native.native_decide.ax_1
  Ctl: EquivLean.TS.svz_num_equiv -> propext,Classical.choice,Quot.sound
  Ctl2: plantedSorry2 -> sorryAx
  Ctl2: plantedAx2 -> plantedAxiom2
  Ctl2: plantedNative2 -> plantedNative2._native.native_decide.ax_1
  Ctl2: EquivLean.Demo.Cir.Musl.musl_strlen_pspec -> propext,Classical.choice,Quot.sound
  Ctl2: EquivLean.Demo.Cir.Musl.musl_strlen_nonchar_ub -> propext,Classical.choice,Quot.sound

## 5. Kernel replay: PASS
- Closure of the 89 claimed modules from the import lists stored in the .olean headers (s4/imports_N.out, scripts/OleanImports.lean;
  what leanchecker imports), over the six project roots: 2371 modules (Aeneas=249 AeneasMeta=17 CIR=53 Cobol=43 EquivLean=1957 Jimple=28 StrictTS=24);
  the template's source-import closure (closure_multi.py) gives the same set (template source-import closure 2371: in olean closure but not source closure 0, in source but not olean 0).
  N closure vs C2 closure: new 9, gone 0; imports outside the project roots are Mathlib-side and toolchain modules only.
- Reuse rule (the template's delta rule, made stricter): a module's next2 pass is reused only if it passed on the re-check copy C2
  (re-check rc=0 154 (of 154 results), re-check reused 2191, AeneasMeta first-run rc=0 with unchanged olean 17; union 2362; C2 closure modules without a pass 0), its .olean equals the hash RECORDED for C2 when
  C2 was made (and its .olean.server/.private parts equal C2's), and the same holds for every module of its olean-import closure.
  Result: closure 2371: reuse 1722, replay 649. replay reasons: an import's olean differs 12; new module 9; olean differs 628; replay per prefix: CIR=50 EquivLean=599.
  The 12 modules whose .olean is byte-identical to next2's while an import changed (the failure mode of next2's first run)
  were replayed: CIR.Lib.List, CIR.Std.Ctype, CIR.Std.FloatLemmas, CIR.Tactic.Elems, CIR.Tactic.Focus, CIR.Tactic.Frame, CIR.Tactic.Lookup, CIR.Tactic.Loop, CIR.Tactic.Nlin, EquivLean.Demo.XLang.Adler32.Equiv, EquivLean.Demo.XLang.Adler32.Final, EquivLean.Demo.XLang.Jsmn.Equiv.
- leanchecker, one process per module (tools/leancheck1lp.sh, timeout 1800 s): 649 of 649 rc 0 (649 planned); 3131 s of
  leanchecker wall time; longest EquivLean.Demo.Gen.Cir.Thrift.ProtoTT 363.7s (leanchecker also replays every module with
  that name prefix: the 490 ProtoTT.* modules). 50 of the 53 CIR modules of the closure were replayed (changed or new
  in 7c73739; the others are byte-identical to 424e821's with unchanged closures); the producer's per-module table has no CIR module.
- leanchecker --fresh (scripts/leancheck_fresh_v1.sh) on the producer's 6 roots: EquivLean.Demo.Cir.Musl.MemcpyCex rc=0 100.7s; EquivLean.Demo.Cir.Musl.MemcpyFindings rc=0 99.4s; EquivLean.Demo.Cir.Musl.MemcpyRefines rc=0 113.6s; EquivLean.Demo.Cir.Musl.StrlenRefines rc=0 100.6s; EquivLean.Demo.XLang.Adler32.CZSpec rc=0 266.4s; EquivLean rc=0 82.4s.
- Controls (replay_controls/, replay_fresh_controls/): BadCtl rc=1; GoodCtl rc=0; StaleA rc=0; StaleB rc=1; --fresh: BadCtl rc=1; GoodCtl rc=0.
  BadCtl: a False theorem added with the kernel check skipped; StaleB: compiled against StaleA v1 (staleVal = 1) and replayed
  against StaleA v2 (staleVal = 2). Messages: [BadCtl] leanchecker found a problem in BadCtl uncaught exception: while replaying declaration 'badCtl': (kernel) declaration type mismatch, 'badCtl' has type   True but it is exp | [StaleB] leanchecker found a problem in StaleB uncaught exception: while replaying declaration 'staleB': (kernel) declaration type mismatch, 'staleB' has type   Eq staleVal 2 but .

## 6. Recompile from the committed sources (template item 6): 2 FAIL, 2 stopped by the address-space cap
- Each module compiled from this copy's sources (= the e1c9a85 blobs, item 1) with the lakefile options as -D flags, imports = the
  producer's oleans in the copy, output to the copy's recompile/lib (scripts/recompile_v1.sh). Wave 1 (34): the 32 changed .lean
  modules and the 2 model modules with renumbered matchers; wave 2 (75): every other non-generated EquivLean module of the claimed
  closure whose .olean differs from next2's, and the EquivLean modules with an identical .olean but a changed import. Result: 105 of
  109 rc 0; 2 compile errors, 2 stopped by the 32 GiB address-space cap, 0 other.
- FAIL EquivLean.Demo.XLang.Jsmn.CPrim (compile_error)
- FAIL EquivLean.Demo.XLang.Jsmn.CTok (compile_error)
- STOPPED EquivLean.Demo.XLang.Jsmn.CString (address_space_cap)
- STOPPED EquivLean.Demo.XLang.TinyRegex.CCompile (address_space_cap)
    EquivLean.Demo.XLang.Jsmn.CPrim: EquivLean/Demo/XLang/Jsmn/CPrim.lean:231:21: error: `simp` made no progress
    EquivLean.Demo.XLang.Jsmn.CPrim: EquivLean/Demo/XLang/Jsmn/CPrim.lean:253:21: error: `simp` made no progress
    EquivLean.Demo.XLang.Jsmn.CPrim: EquivLean/Demo/XLang/Jsmn/CPrim.lean:265:17: error: `simp` made no progress
    EquivLean.Demo.XLang.Jsmn.CTok: EquivLean/Demo/XLang/Jsmn/CTok.lean:81:17: error: `simp` made no progress
    EquivLean.Demo.XLang.Jsmn.CTok: EquivLean/Demo/XLang/Jsmn/CTok.lean:99:20: error: `simp` made no progress
    EquivLean.Demo.XLang.Jsmn.CString: INTERNAL PANIC: out of memory
    EquivLean.Demo.XLang.TinyRegex.CCompile: INTERNAL PANIC: out of memory
  The failing lines are 'refine <by simp only [Mem.endScope]; omega, ...>' after cir_hrun_c: against the final
  EquivLean.Bridge.Cir.Tactic the goal shows Exit.leaveMem, so the simp set has nothing to rewrite. Build order (mtimes kept by the
  copy, read with date -u -r): Jsmn/CTok.olean 2026-10-30T11:07:03Z, Jsmn/CPrim.olean 2026-10-30T11:15:03Z;
  Bridge/Cir/Tactic.lean 2026-10-30T13:23:30Z, Bridge/Cir/Tactic.olean 2026-10-30T14:45:10Z (Bridge/Cir oleans from
  2026-10-30T14:39:01Z to 2026-10-30T14:45:57Z). The kernel accepts the stored proofs in the
  final environment (section 5), but e1c9a85 does not rebuild them.
- Build order inside the producer's rebuild (s6/stale_rebuilt.out): rebuilt modules in the claimed closure: 596; of them compiled before a rebuilt transitive import was last written: 44
  (newest such import mostly EquivLean.Bridge.Cir.Tactic); recompiled here: recompile=rc=0 41; recompile=rc=1 3.
- Recompiled vs producer oleans (OleanCmp3, s6/oleancmp_recompile.out): equal_up_to_auxiliaries 73, differ 7, consts_equal 25; bytes: bytes_differ 94, bytes_same 11, no_recompiled_olean 4.
  Differing: EquivLean.Bridge.Cir.Congr (only mine 226, only producer 238); EquivLean.Bridge.Cir.Tactic (only mine 49, only producer 51); EquivLean.Demo.Cir.Musl.Memcpy (only mine 351, only producer 344); EquivLean.Demo.Thrift.Cpp.Transport (only mine 3, only producer 3); EquivLean.Demo.XLang.Jsmn.Model (only mine 4, only producer 4); EquivLean.Demo.XLang.TinyRegex.CMatchPat (only mine 264, only producer 269); EquivLean.Demo.XLang.TinyRegex.Model (only mine 1, only producer 1).
  For the two model modules this check's recompile equals next2's oleans exactly (EquivLean.Demo.XLang.Jsmn.Model consts_equal; EquivLean.Demo.XLang.TinyRegex.Model consts_equal):
  the committed sources with the lakefile options give next2's matcher numbering, the producer's oleans another (equal after renaming, 3d).
  For the other differing modules the differing types and values name auxiliary constants (match_, _proof_, simproc and private
  names) whose sets differ, consistent with another compile setting in the producer's plain-lean rounds; not examined further.

## 7. Wording for the paper
At the next3 pins (equiv-lean e1c9a85: cirlean 7c73739, coblean 20261028T0109Z unchanged) the producer's build proves all 176
claimed theorems with at most the standard axioms, the kernel replay of their whole import closure and of the six --fresh roots
passes, 171 statements print as at next2, and the COBOL, TypeScript, Thrift Java/Rust and Rust-side statements keep their
meaning (identical definition closures, 4 of them up to a renumbered match auxiliary). The 50 C-side statements (musl,
Thrift C++, Adler-32, jsmn, tiny-regex) are now statements about cirlean 7c73739's semantics (flat pointer addresses, typed byte
access, pointer arithmetic in the pointee's units), and 5 of them change form: musl_strlen_nonchar_ub, musl_memcpy_cex_ub,
musl_memcpy_ne_model and jsmn_parse_primitive_pspec gain a hypothesis (char-array block, the bound m.next < 2^29, concrete block
types) and musl_strlen_aligned_ub restates its alignment hypothesis on flat addresses.
Until EquivLean.Demo.XLang.Jsmn.CPrim, EquivLean.Demo.XLang.Jsmn.CTok compile from the commit (section 6), a paper sentence can cite the kernel-checked oleans of the producer's build,
not the commit's sources, for the theorems of those modules (jsmn_parse_primitive_pspec among the claimed ones).

## Notes on the producer's report (REPORT_next3.md, sha256 prefix 6ae24e0be1667c0d)
- All announced sha256 prefixes match (patch, oleancmp diff, axioms table, per-module and --fresh tables, report).
- The old musl_strlen_aligned_ub hypothesis is misstated (3b.2); memcpy_model_zero's added hypotheses are written in another form (3c).
- 'Seven internal helpers' holds within the producer's Demo-module scope; 3 Bridge.Cir lemmas also change text (3c).
- '1,586 non-CIR .olean files byte-identical' does not match (the EquivLean count is 1,582; section 2).
- Its per-module replay table covers the rebuilt EquivLean modules only; this check also replayed the CIR modules (section 5).
- The rebuilt modules were compiled with plain lean in several rounds (Lake traces older than the oleans; Congr has no trace);
  some predate the last Bridge.Cir change and do not recompile from the commit (section 6).
- Its two model oleans (Jsmn.Model, TinyRegex.Model; sources unchanged since next2, importing only Init) are not the standard
  compile of their sources: a recompile here equals next2's oleans, the producer's differ from it by a renumbered matcher (section 6).

## Limits
(i) The replayed oleans are the producer's build (copy = sources byte for byte). Reused results rest on the next2 re-check copy's
    replay and records (re-hashed now: unchanged). Rebuilt EquivLean modules outside the claimed closure (42) were not replayed here.
(ii) Lean core and the Mathlib-side packages are not replayed per module (byte-identical to the next2 copy; --fresh replays Lean
    core for the 6 roots).
(iii) Statement and closure comparisons use pretty-printed text and Lean Expr hashes; renumbered auxiliaries count as changes.
(iv) Each recompile uses the producer's oleans of its imports; a full rebuild from the commit was not run.
(v) Bare shell use: single-file reads, mkdir, heredoc writes of scripts and command files, progress appends; a few progress
    tallies read several of this check's own output files at once (cat replay/*.tsv | awk), read-only.

## Cost
Guarded jobs: 3.049 core-h over 1068 guard logs (guard_core_s.tsv): replay 1.106,
statement/closure/axiom dumps 0.380, recompiles 1.510. Priced before the replay at about 2.5 core-h
from the template's 2.224 core-h for 1742 modules (before the second recompile wave was added); budget about 6 core-h.

## Files
s1/ (commit, pins), s2/ (copy, hashes), s3/ (olean comparison, module lists, job sources), s4/ (olean imports, closure, delta),
stmt/, clos/, axioms/, replay/, replay_controls/, replay_fresh/, replay_fresh_controls/, recompile/, s6/ (OleanCmp3, renaming,
staleness, recompile classes), scripts/ (a script superseded by a higher version was never run, except s3_gen_v1.sh, whose part D output
cmds_s3.txt was not used, and mk_summary_v9.sh, whose SUMMARY.md is kept as SUMMARY_v9_superseded.md; cmds_summary5.txt ran v9, cmds_summary6.txt this version, cmds_summary.txt to cmds_summary4.txt did not run), cmds_*.txt, pjobs_*.log, guard/, guard_core_s.tsv, post_*.out. SHA256SUMS lists every file except
itself and the files of the job that writes it (guard/sums.log, pjobs_sums.*, sums_check.txt).

Written 2026-10-30T16:41:26Z (date -u).
