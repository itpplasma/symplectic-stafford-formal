# Symplectic Stafford formalization plan

```yaml
phase: target-a-formalized
terminal_theorem_formalized: true
terminal_theorem: SymplecticStafford.Paper.FilteredAlgebraData.targetA
palomar_statement: SymplecticStaffordChallenge.universalStatement
axioms: [propext, Classical.choice, Quot.sound]
public_release: false
palomar_registration: not-submitted
```

## Mathematical status

Target theorem A of the manuscript is proved in Lean from the standing
hypotheses of §1.1 alone, with no localization, source-selection or support
hypotheses. Every earlier project obligation M01–M11 is discharged by the
`SymplecticStafford/Paper/` development:

| Obligation | Discharged in |
| --- | --- |
| M01 semantics, structural filtered layers | `Setting.lean` (§1.1 data, degree, symbol, `gr I`) |
| M02 filtered Noetherianity, good subquotients | `Setting.lean` (`artinRees`) |
| M03 full-symbol Ore localization | `Localization.lean` (`ore_condition`, `Tloc`, `isRightFractions`) |
| M04 faithful detection | `Localization.lean` (`unit_of_neg`, `nakayama_rows`, `survival`) |
| M05 minimal-prime local length | `Localization.lean` (`finiteLength`) |
| M06 division-coefficient LLD, finite tests | `DivisionPencil.lean`, `NoFiniteRank.lean`, `SourceSelection.lean` |
| M07 activated and generating pencils | `Pencil.lean` |
| M08 common colon, support union | `Induction.lean` (`colonJ`, `colonJ_le_Id`, `support_union`), `Dimension.lean` |
| M09 strong `P_h` with test lists | `Test.lean`, `Induction.lean` (`Ph`, `Ph_zero`) |
| M10 two-call successor, termination | `Induction.lean` (`Ph_succ`, `Ph_all`) |
| M11 original cofactors, opposite, package | `Induction.lean` (`targetA`), `Opposite.lean`, `Consequences*.lean` |

## Active build scope

The current package has exactly one direct dependency, Mathlib. Target A, the
Challenge/Solution pair and their native consumers form the release build.
AlgebraicAnalysis and Stafford38 requirements were removed after official
preflight detected a shadowing dependency Challenge module. Retired scaffolds
replay only at the [frozen historical checkout](docs/history/legacy-build-environment.md);
the active verifier has no historical-scaffold replay mode. Recorded local
and CI passes apply to their exact source snapshots. The dependency-pruned
source at 8b94e4a2c9114a63a44a7e057e3b03fcafbb95f3 passes native full
private-source verification and [clean Linux CI](https://github.com/itpplasma/symplectic-stafford-formal/actions/runs/39578127875),
including six verifier regression tests and its 414-file source inventory.
[Complete official Palomar preflight](https://github.com/itpplasma/symplectic-stafford-formal/actions/runs/39578128284)
passes for that same source and the selected Target A theorem, with con-ron,
NanoDa and Lean acceptance. The actual mechanical report is retained in
`evidence/palomar-mechanical-report.json`. Section 7 is proved in Lean but is
not independently registered by this Target A comparison.

## Remaining release steps

The 3 October 2026 synchronization brings both canonical host checkouts to
the shared `main`. Target A and section 7 sources are in
`SymplecticStafford/Paper/`. Four legacy boundary/probe files from the research
checkout are preserved separately in `itpplasma/symplectic-stafford` on
`wip/sync-20261003/local/symplectic-stafford` (`636f3479c458`); that repository's
PLAN lists their exact paths and unverified status. They are not a replacement
for this canonical proof. No new proof replay or release is claimed by sync.

1. Independent human review:
   - of the manuscript, including the Zariskian closure note and the
     formal-route corrections in the research repository;
   - of the statement correspondence in `docs/target-a-submission-scope.md`.
2. Replay complete official Palomar preflight for the final metadata commit
   before intake. Native full verification, clean Linux CI and official
   preflight already pass at the source commit above. Retain the evidence
   files named in `release-gates.yaml`. Phase I records Target A proof
   closure, and Phase II records the independent replay of that complete
   theorem; their historical names do not reopen discharged scaffolding.
3. Palomar submission and its exact commit and registration receipt, following
   `docs/release-runbook.md`. The author authorized release preparation and
   Palomar submission on 21 October 2026. No receipt is retained yet.
4. A final human-readable manuscript and any signed GitHub/Zenodo release are
   separate deliverables. Keep the manuscript synchronized with the formal
   correspondence map and the research corrections. No final typeset paper
   or independent human review is claimed by agent completion.

The previous plan and its wave-by-wave history are archived in
`docs/history/PLAN-before-target-a-2026-09-30.md`.
