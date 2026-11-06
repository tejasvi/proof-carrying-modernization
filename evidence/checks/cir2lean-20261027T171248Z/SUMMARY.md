# Check by an agent: provenance of the generated C-side Lean modules (written 2026-10-27T17:16:23Z)

Question (the C maintainer session): the frozen cirlean copies ~/cirlean_frozen/28e2380_20261025 and 266d1ed_20261025 hold a leftover 10-23
bin/cir2lean (sha 913d792b0bcca6c3..., mtime 2026-10-23 20:04; confirmed). Did our claimed C results use it?

Binaries (sha256 prefix, mtime):
- The C maintainer session clean builds: ~/cirlean_build_28e2380 and ~/cirlean_build_266d1ed .lake/build/bin/cir2lean: 12d2c1baf5672ed8 (both).
- Producer gen.sh scripts: tiny-regex-c uses equivlean_work/vendor/cirlean-ec40522 cir2lean (12d2c1baf5672ed8, 10-25 03:11);
  jsmn, Adler-32 and musl use equivlean_work/vendor/cirlean-28e2380 cir2lean (12d2c1baf5672ed8, 10-25 10:39).
- Our earlier regeneration checks (eqT, eqr5, adler32) used the replay copies' vendor/cirlean-28e2380 cir2lean: 12d2c1baf5672ed8.
- cJSON harness package (veriforch lean_v266d1ed): its deps/cirlean-266d1ed cir2lean 12d2c1baf5672ed8 (10-25 02:51), cirrun
  d12dee102125dff2 (= the C maintainer session's clean 266d1ed cirrun).
- None of these is 913d792b.

Regeneration with the C maintainer session's clean binaries (regen.sh; inputs read in place, sha256 in inputs.sha256; outputs in out/):
- tiny-regex-c (re.cir of the eqT copy): identical except header line 2 (the input path).
- jsmn (jsmn_run.cir of the eqr5 copy): identical except header line 2.
- Adler-32 (adler32.cir of the adler32 copy): identical except header line 2.
- musl strlen, memcpy (eqmusl copy): identical except header line 2.
- cJSON harness (cir2lean --link Gen.v0_cjson_parse_fuzzer.Unit, from the cjh records' two .cir, 266d1ed binary): 128/128 files
  (127 Lean modules + manifest.json) byte-identical, headers included. First regeneration of this Gen (the cjh check had not done it).
Guard: g1.sh, total 0.000 core-h.
