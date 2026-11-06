# Addendum to ADDENDUM_C1ATTR_coblean.md (b677baab): the built variant tree (recorded 2026-10-28T10:51:13Z)
Sent by the COBOL maintainer session before the first module (NC) started; recorded here at the time above, shortly after that start.
Hashes verified by us at about 10:51Z (sha256 prefixes):
- tree ~/coblean_runs/c1var/tree, built by build_c1var_v1.sh f1015319862227d7 (= N3's build_nist3_v1.sh plus the patch
  step; build_c1var_v1_vs_nist3.diff ab7fb5f377b50b4f); patch applied with --fuzz=0, no offset (per the COBOL maintainer session).
- Cobol/Frontend/Resolve.lean in the tree: dd5de24106ab7417 (= the patched file named in the plan).
- manifest tree_manifest_c1var.sha256: 387a13c03c2669e1, 2,165 lines (N3 manifest bf1403be: 2,165 lines).
- diff against the N3 manifest manifest_diff_vs_n3.txt ab5e42de536144de (notes manifest_diff_explained.txt
  b47f898540af9dd6): per the COBOL maintainer session, 23 paths changed in place, 0 added, 0 removed: Resolve.lean (source) and 22 build outputs
  (cobolrun and its hash/rsp/trace, Resolve's IR/olean/ilean/trace files, setup/trace files that carry the tree path and
  the new Resolve dependency hash); Load.olean, Cobol.olean, CobolRun.olean, CobolRun.c unchanged.
- runner tools/nist/run_nist.py in the tree = 6635004c (per the COBOL maintainer session); inputs (frozen-hash list, extract5 + gc4 listing,
  2,174 files) byte-identical to N3's (per the COBOL maintainer session).
