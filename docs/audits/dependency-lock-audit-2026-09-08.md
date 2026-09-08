# Dependency lock audit — 8 September 2026

The repository locks Lean `leanprover/lean4:v4.33.0`, Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`, AlgebraicAnalysis
`46f2c819deca0e9735a436bed94ebed03ae35090`, and Stafford38 formal
`e77e176c381ca2d6b20c030f9227f1b031415d2e`.

The public remote heads were queried directly:

```text
https://github.com/itpplasma/algebraic-analysis.git refs/heads/main
46f2c819deca0e9735a436bed94ebed03ae35090
https://github.com/itpplasma/stafford38-formal.git refs/heads/main
e77e176c381ca2d6b20c030f9227f1b031415d2e
```

Both public heads were cloned into isolated temporary checkouts and were
clean. The current Stafford38 formal main commit records Lean
`leanprover/lean4:v4.33.0`, Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`, and its released AlgebraicAnalysis
tag commit `4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8`; this checkout
intentionally overrides that transitive dependency with the newer public
AlgebraicAnalysis main head `46f2c819deca0e9735a436bed94ebed03ae35090` and
replayed the downstream build. The downstream `lake build SymplecticStafford`
completed successfully with the isolated latest Stafford38 checkout, followed
by a successful `./scripts/verify.sh --phase-i` replay and direct
`--trust=0` checks of every newly integrated module/oracle. The lock and
manifest both record the full 40-hex revisions; no floating branch is used.

This is dependency reproducibility evidence only. It does not assert that the
paper's M01–M11 producer or the release gates are complete.
