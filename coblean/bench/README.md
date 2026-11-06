# Scaling benchmarks

`seqif.py N` writes `seqif_N.ir.json`: *N* sequential
`IF F-i > 0 ADD 1 TO CNT ADD F-i TO TOTAL END-IF` statements. `mklean.py N` writes
`SeqIf_N.lean`, which proves the program equal to a Java-style fold and reports the
heartbeats (deterministic cost) of the proof. `mklean.py N sym` stops after symbolic execution
instead.

```sh
cd bench && python3 seqif.py 32 && python3 mklean.py 32 && cd ..
scripts/lean1.sh bench/SeqIf_32.lean
```

`perfs.py N` writes `perfs_N.ir.json` and `PerfS_N.lean`: `MAIN` performs *N* paragraphs, each
`IF F-i > 0 ADD F-i TO TOTAL ELSE SUBTRACT F-i FROM TOTAL END-IF. ADD 1 TO CNT.`, proved equal
to a fold computing the total of the absolute values and the count.

Results (thousands of heartbeats for the whole proof, before / after flat memories
`Cobol/Logic/MemNorm.lean`, 2026-10-24): `seqif` N=32 118 648 / 64 069, N=64 459 584 / 156 128,
N=128 – / 425 531; `perfs` N=32 137 863 / 58 774, N=64 545 594 / 128 734. Heartbeats are
deterministic; wall times on the shared VM are not.
