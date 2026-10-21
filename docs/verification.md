# Verification record

## Target A release migration (local run, 21 October 2026)

Checked proof/configuration source: fc39ccadbfbc77940c2298a447374dacdadb55f9. The later release records may
change metadata; the map fingerprints identify the exact proof inputs.
Lean is v4.35.0-rc3 and Mathlib is
c55e6e786f49471c72fbddbec5415808896aec1e. The earlier toolchain's results
below remain historical evidence of their own snapshot.

The native build of `SymplecticStafford.Paper`, `Challenge` and `Solution`
passes. `scripts/verify.sh full`, with the private research checkout supplied
through `PAPER_REPO`, passes:

- all 18 current endpoint axiom reports contain only the three standard axioms;
- Challenge, Solution and Paper load 3142, 3577 and 3584 modules, respectively,
  with Mathlib-only external imports and no Challenge import in Solution;
- the source audit checks all 392 Lean files, including unused historical files;
- the 34-card map checks nine immutable paper sources, 22 formal inputs and
  96 compiled declaration references with their actual owning modules;
- `PaperTargetAOracle.lean` passes with `--trust=0`;
- four verification-guard regression tests pass.

The theorem statements and proof bodies are unchanged. The migration adds
module/public visibility and two explicit Mathlib imports. The independent
source-level terminal audit found no hidden premise or handedness mismatch;
its scope is the statement, filtered-data encoding and terminal composition,
not a second audit of every internal lemma. The correspondence map records
the dimension convention and omitted/generalized manuscript assertions.

This is a local macOS replay. The public CI replay and the complete pinned
Palomar Linux workflow must finish before registration. Bundled Comparator,
NanoDa, con-ron and Lean-kernel acceptance are not inferred from this build.
Independent human mathematical review remains pending.

## Palomar comparison of Target A (local run, 30 September 2026)

Source commit: `f8e97fc20e62699a96e46bd4091f16b4b210b797` (branch `claude/kind-bell-rk5gmv`). The
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

The project was compiled and exported with Lean 4.33.0 and Mathlib
`db584cd`. The comparator executable is built with `leanprover/lean4:v4.34.0-rc1`,
the toolchain pinned by the comparator repository at that revision.

The comparator run used `comparator.json` unchanged:

- theorem `SymplecticStaffordChallenge.universalStatement`;
- permitted axioms `propext`, `Quot.sound` and `Classical.choice`;
- NanoDa enabled.

This is a local replay in the development container. The release runbook's
clean-checkout replay, human review and registration remain separate steps.

Earlier checkpoint records are archived in `docs/history/`.
