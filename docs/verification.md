# Verification record

## Palomar comparison of Target A (local run, 1 October 2026)

Source commit: `75b286cf01673abd9a33e104aa66480a91b90be5` (branch `claude/kind-bell-rk5gmv`). The
Challenge/Solution sources at that commit are the compared pair.

| Check | Result |
| --- | --- |
| `lake env lean Challenge.lean` | compiles; only the deliberate `sorry` |
| `lake env lean --trust=0 Solution.lean` | compiles |
| `#print axioms SymplecticStaffordChallenge.universalStatement` | `propext, Classical.choice, Quot.sound` |
| `scripts/check-import-closure.sh Challenge` | 3108 modules, Lean/Mathlib only |
| `scripts/check-import-closure.sh Solution` | 3535 modules, no `Challenge` import |
| Comparator `5756749` with lean4export `15f6055`, NanoDa `68d5ca9`, Landrun `811cfff` | "nanoda kernel accepts the solution", "Lean default kernel accepts the solution", "Your solution is okay!" |
| `lake env lean --trust=0 tests/PaperTargetAOracle.lean` | passes; the main theorems report only the three standard axioms |
| `lake env lean --trust=0 tests/WeylNonVacuityOracle.lean` | passes; `stafford38_universalStatement` reports only the three standard axioms |
| `scripts/verify.sh full` | passes: pins, source audit, full library build (9202 jobs), axiom audit of all endpoints, all 181 oracle files in `tests/` |
| `scripts/verify-palomar.sh` | passes: configuration, import-closure audits, comparator |

The project was compiled and exported with Lean 4.33.0 and Mathlib
`db584cd`. The comparator executable is built with `leanprover/lean4:v4.34.0-rc1`,
the toolchain pinned by the comparator repository at that revision.

The comparator run used `comparator.json` unchanged:

- theorem `SymplecticStaffordChallenge.universalStatement`;
- permitted axioms `propext`, `Quot.sound` and `Classical.choice`;
- NanoDa enabled.

This is a local replay in the development container. The release runbook's
clean-checkout replay, human review and registration remain separate steps.

Four legacy oracles and two legacy `Filtered` modules had drifted from the
pinned Mathlib and were never built by `verify.sh`; they were repaired and
are now part of the umbrella build.

Earlier checkpoint records are archived in `docs/history/`.
