# Agent guidance

- Target theorem A (the affine same-divisor theorem) is proved in
  `SymplecticStafford/Paper/`.
  - The development imports Mathlib only.
  - The Palomar pair is `Challenge.lean` / `Solution.lean`.
  - `README.md` and `docs/target-a-submission-scope.md` describe the scope.
- Do not add `sorry`, axioms, `native_decide` or conditional wrappers to the
  `Paper/` development or to the Challenge/Solution pair.
  - Keep `Challenge.lean` Mathlib-only.
  - Keep `Solution.lean` free of any import of `Challenge`.
- Preserve the pinned Lean/Mathlib revisions. A toolchain or Mathlib bump
  requires a full rebuild and a fresh comparator replay.
- The legacy scaffolds outside `Paper/` are historical. Treat their earlier
  status notes in `docs/history/` as superseded, not as current open
  obligations.
- The paper source of truth is `itpplasma/symplectic-stafford`. Corrections
  found while formalizing go into its `docs/formal-proof-route-2026-09-30.md`.
- Remaining release steps are human decisions: independent review, public
  clean replay, Palomar registration and Zenodo release. See
  `docs/release-runbook.md`.
