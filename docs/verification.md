# Verification record

## Current Target A release replay (21 October 2026)

Checked source: 8b94e4a2c9114a63a44a7e057e3b03fcafbb95f3. The protected
[source inventory](../evidence/source-inventory.json) covers all 414 tracked
Lean, verifier, consumer, workflow and root build/license inputs. The release
gate checks those hashes against both this Git commit and the working tree;
metadata-only successors cannot silently change the checked sources.

Lean is v4.35.0-rc3 and Mathlib is
c55e6e786f49471c72fbddbec5415808896aec1e, the sole direct dependency.
The native macOS replay with `PAPER_REPO` and the
[clean Linux project CI](https://github.com/itpplasma/symplectic-stafford-formal/actions/runs/39578127875)
both pass. Native replay also checks the nine immutable private research
sources at c495a2c4c702c25cdb236034273c71cf94e86476. Public CI explicitly
uses the formal-only map check and makes no private-source check claim.

The full proof contract verifies:

- all 18 endpoint axiom reports use only `propext`, `Classical.choice` and `Quot.sound`;
- Challenge, Solution and Paper load 3142, 3577 and 3584 modules, respectively,
  with Mathlib-only external imports and no Challenge import in Solution;
- all 392 Lean files pass the source audit, including unused historical files;
- the 34-card map fingerprints 22 formal inputs and checks 96 compiled
  declaration references with their actual owning modules;
- `PaperTargetAOracle.lean` passes with `--trust=0`;
- all six verification-guard regression tests pass.

The [CI receipt and log hashes](../evidence/native-ci/run.json) retain the
actual clean-run evidence. The theorem statements and mathematical proof
bodies are unchanged by the toolchain migration: module/public visibility
and two explicit Mathlib imports changed. Unused historical dependencies
were then removed after they shadowed the root Challenge in official preflight.
They remain reproducible at the documented frozen historical revision.

The independent source-level terminal audit found no hidden premise or
handedness mismatch. Its scope is the statement, filtered-data encoding and
terminal composition, not a second audit of every internal lemma. The map
records route substitutions, omitted manuscript assertions and the dimension
convention. Independent human mathematical review remains pending, and the
final typeset paper is deferred.

The [complete official Palomar preflight](https://github.com/itpplasma/symplectic-stafford-formal/actions/runs/39578128284)
passes for the exact checked source under `palomar-standard-v1`, pinned pipeline
d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44. The retained
[mechanical report](../evidence/palomar-mechanical-report.json) has `status: pass`,
`stage: complete`, and no errors or warnings. It confirms exact statement
comparison and acceptance of the selected Target A export by con-ron (19,824
declarations), NanoDa and Lean's default kernel. It does not separately
register every section 7 theorem. Tool digests, resource use and canonical
Challenge provenance are retained in that report and the [run receipt](../evidence/palomar-run.json).

The mechanical release gates pass. Palomar intake and its permanent
registration decision still require the author-agreement steps in the runbook;
there is no registration receipt yet.

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
