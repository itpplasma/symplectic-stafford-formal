# Building and verification

## Toolchain and dependencies

The package pins Lean `leanprover/lean4:v4.35.0-rc3` (`lean-toolchain`) and
has exactly one direct dependency, Mathlib at
`c55e6e786f49471c72fbddbec5415808896aec1e` (`lakefile.toml`,
`lake-manifest.json`). A toolchain or Mathlib bump requires a full rebuild
and a fresh comparator replay.

```sh
lake exe cache get   # prebuilt Mathlib
lake build           # SymplecticStafford.Paper, Challenge, Solution
```

## Full verification

```sh
bash scripts/verify.sh
```

The script, which is also what CI runs (`.github/workflows/verify.yml`),

1. checks disk headroom, dependency pins and the source policy (no `sorry`,
   axioms or `native_decide` in the proof sources);
2. checks the paper/Lean declaration map. Without the environment variable
   `PAPER_REPO` only the formal side is checked; with `PAPER_REPO` pointing
   at a checkout of the companion research repository, the pinned paper
   sources are checked as well;
3. builds `SymplecticStafford.Paper` and `Challenge`, and compiles
   `Solution.lean` with `--trust=0`;
4. checks that the import closures of `Challenge`, `Solution` and
   `SymplecticStafford.Paper` contain only Lean and Mathlib modules, and that
   `Solution` does not import `Challenge`;
5. runs `#print axioms` on each declaration in `docs/endpoints.txt` and fails
   if anything beyond `propext`, `Classical.choice` and `Quot.sound` appears;
6. builds and replays `tests/PaperTargetAOracle.lean` with `--trust=0`.

Logs are written to `.lake/verification/`. The Python regression tests for
the verifier itself are run with

```sh
python3 -m unittest discover -s tests/python -p 'test_*.py'
```

(they need PyYAML).

## Comparator replay

`Challenge.lean` states the theorem using Mathlib only and ends in a single
intentional `sorry`; `Solution.lean` proves the same statement.
`comparator.json` names the theorem and the permitted axioms. To replay the
statement comparison and independent kernel checks locally:

```sh
bash scripts/bootstrap-palomar-tools.sh
bash scripts/verify-palomar.sh
```

The bootstrap script checks the pinned toolchain and the bundled
`leanexport`, `leanchecker`, `nanoda_bin` and `con-ron` tools. The sandboxed
replay requires Linux and `bwrap`. The comparison covers the Target A
statement only, not the section 7 consequences.

## Historical scaffolds

The older conditional scaffolds under `SymplecticStafford/` (outside
`Paper/`) depended on AlgebraicAnalysis and Stafford38 and are not part of the
current package. Replay them only from the frozen checkout described in
[history/legacy-build-environment.md](history/legacy-build-environment.md).
