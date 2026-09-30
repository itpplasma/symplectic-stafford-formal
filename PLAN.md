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

## Status (30 September 2026)

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

## Remaining release steps

1. Independent human review:
   - of the manuscript, including the Zariskian closure note and the
     formal-route corrections in the research repository;
   - of the statement correspondence in `docs/target-a-submission-scope.md`.
2. Public clean replay from a fresh checkout using `scripts/verify.sh` and
   `scripts/verify-palomar.sh`; record the evidence files named in
   `release-gates.yaml`.
3. The human decisions on repository visibility, Palomar registration and a
   Zenodo release, following `docs/release-runbook.md`.

The previous plan and its wave-by-wave history are archived in
`docs/history/PLAN-before-target-a-2026-09-30.md`.
