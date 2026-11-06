# Addendum T2: the frozen T2 sample (PREREG_T_v1)

Written by the paper's evidence owner at 2026-10-25T16:32:45Z, before any T2 run. As for PREREG_T_v1, this file is never
edited; later changes go to DEVIATIONS.md. Its files are listed with their sha256 in SHA256SUMS_T2_addendum.

## Inputs: T1's unit lists (copied from veriforch, read-only here)

- `t1_inputs/T1_cxx_units.tsv`: 5197 units {'C': 589, 'C++': 4608}; sha256 e4c328781ccb122ab0079e4f0ca02a5e8c2113e171592dbfaadc93a301c1bafc
- `t1_inputs/T1_java_units.tsv`: 1948 units {'Java': 1948}, synthetic=1: 256; sha256 908fd092b768a493ae57131484346f3a62818fb2cd7349cb2566ba6af5525a09
- `t1_inputs/T1_rust_units.tsv`: 781 units {'Rust': 781}, kind=test: 245; sha256 f6da27f5f3c775dd83e2f5ac085fcd571752fb5d70350b8a2fb24cced092fd92
- TS: no library TypeScript at the pin (DEVIATIONS, T clarification of the frame), so every TS stratum has N_s = 0.

## Frame

- Built by `build_t2_frame.py` (sha256 d22aa826be23711f941dc45a7d2c4137d1e54e6032056e4c262482a981d2dc6f) under the T clarifications
  recorded in DEVIATIONS.md on 2026-10-25 before any draw (frame files; not-emitted definitions kept as blocked;
  Rust #[cfg(test)] code excluded; compiler-synthetic Java units excluded; stamp correction of 15:54Z).
- Builder output: `kept: {'C': 589, 'C++': 4608, 'Java': 1692, 'Rust': 536} excluded: {'synthetic': 256, 'kind=test': 245}`
- `frame_T2.tsv`: 7425 units {'C': 589, 'C++': 4608, 'Java': 1692, 'Rust': 536}; sha256 1888c77712fbfa05deee41a90fc4e6f53d4ac73a94611e2b9935fcf7023b3d15

## Sample

- Drawn by the frozen `tools/draw_t2.py` (sha256 11a7b794250f4952c395cecc855c65accc6da5a2a2259f7f0855c1f03777a5a5, in
  SHA256SUMS_T_v1) with its defaults N = 1000, MIN = 20 and seed `fv-paper-prereg-T-2026-10-25`; run twice, the
  two outputs byte-identical.
- Draw output, first line: `frame 7425 units in 17 strata; sample 1000`; the strata below are the rest of it.
- `sample_T2.tsv`: 1000 units {'C': 127, 'C++': 520, 'Java': 230, 'Rust': 123}; sha256 83a361fc678d43b94f42b428d1978e0bc5a4b218faa24900e83df834ff67dddf
- Processing order: the column `order` (one seeded permutation of the whole sample).

| language | component | N_s | n_s | weight N_s/n_s |
|---|---|---:|---:|---:|
| C | other | 65 | 24 | 2.7083 |
| C | protocol | 266 | 43 | 6.1860 |
| C | server | 20 | 20 | 1.0000 |
| C | transport | 238 | 40 | 5.9500 |
| C++ | compiler | 2539 | 255 | 9.9569 |
| C++ | other | 161 | 33 | 4.8788 |
| C++ | protocol | 699 | 83 | 8.4217 |
| C++ | server | 382 | 54 | 7.0741 |
| C++ | transport | 827 | 95 | 8.7053 |
| Java | other | 452 | 60 | 7.5333 |
| Java | protocol | 465 | 61 | 7.6230 |
| Java | server | 221 | 39 | 5.6667 |
| Java | transport | 554 | 70 | 7.9143 |
| Rust | other | 62 | 24 | 2.5833 |
| Rust | protocol | 315 | 48 | 6.5625 |
| Rust | server | 21 | 20 | 1.0500 |
| Rust | transport | 138 | 31 | 4.4516 |
| all | | 7425 | 1000 | |

## Pins

- veriforch records the tool pins when T2 starts (frozen copy with a SHA256 manifest), with the Java adapter fixes
  listed in DEVIATIONS.md; nothing in this addendum depends on them.
