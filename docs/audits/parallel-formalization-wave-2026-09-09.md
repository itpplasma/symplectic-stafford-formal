# Parallel formalization wave — 2026-09-09

This audit records the disjoint Luna lanes integrated by the controller on the
shared `main` branch. It is a checkpoint provenance record, not a Phase I,
Phase II, Palomar, or publication certificate. The paper source remains frozen
at `502b65a1dea53cac52220a08e321bfba525bc72e`; the exact dependency pins are
Lean 4.33.0, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`,
AlgebraicAnalysis `46f2c819deca0e9735a436bed94ebed03ae35090`, and Stafford38
formal `e77e176c381ca2d6b20c030f9227f1b031415d2e`.

## Integrated lanes

The worker commits and their bounded scopes are:

- `4ca3311b0d07294fec8f3090a800061c8178ebdd` —
  `FullSymbolRightPowerBridge`: derives right power-clearing/Ore witnesses
  from an already supplied actual right localization, plus a rational
  localization oracle.
- `894cb302531120c3bd9ddfc1e7812e7a2be8d948` —
  `WeightedMatrixInverse`: finite geometric inverse and faithful row-action
  lemma for nilpotent correction matrices, plus a 2-by-2 oracle.
- `150c9a9d0bfb281e1f203aa03a90ec3dbae817ce` —
  `FilteredMinimalPrimeBridge`: nontriviality and finite-length consumers for
  actual prime localization from a minimal-support/annihilator hypothesis.
- `ebec96af5d0ed0ac271847c66127778672ae7604` — scalar-extension
  `FiniteOrbitPencil`: finite-exception and activation theorems from a supplied
  orbit basis over a commutative extension, with a `RatFunc` oracle.
- `5055a31e07dea1b4d3c807444ca85c0c7a99dbbf` — `ActualM08Producer`:
  indexed colon-generator expansions, converse membership, and affine
  certificates under actual right Noetherianity, with an integer oracle.
- `0c378aa028f969324c42acf53222a21df2bc3777` —
  `TwoCallDescentProducer`: two-call successor construction with explicit
  finite exceptional set, support/defect equality, and carried-test output,
  plus an endpoint recursion oracle.
- `a45291b49d6caef45265d863b48fd0a285a54346` — terminal and opposite package
  assembly: `terminal_sameDivisor`, `TerminalPackage` endpoints, symmetric
  opposite transport, and an independent terminal assembly oracle.

All worker reports preserve their producer hypotheses. In particular, no lane
proves the universal filtered symbol-set Ore theorem, the noncommutative
finite-length block decomposition, the characteristic-support union, strict
support removal, the universal base/successor, or the original-
`U` simultaneous source producer.

## Checks and interpretation

Each listed source and its independent `tests/*Oracle.lean` consumer was run
with `lake env lean --trust=0`. The reported axiom closure is restricted to
`propext`, `Classical.choice`, and `Quot.sound`; the only project `sorry` is
the statement-only placeholder in `Challenge.lean`. The root import now
includes the weighted-matrix module, and the aggregate
`lake build SymplecticStafford` completed successfully after that import.

The phase scripts and Palomar-compatible comparator remain checkpoint checks
for the semantic/ordered Challenge/Solution pair. They do not certify the
all-dimensional target. `release-gates.yaml` therefore remains fail-closed:
Phase I and Phase II are not verified, Palomar is not submitted, and public
visibility/Zenodo release are unchanged.

The controller replay was run at integration commit `0cb83aa` with the
resource guard first. `lake build SymplecticStafford` completed 8,787 jobs;
`./scripts/verify.sh --phase-i` and `./scripts/verify.sh --phase-ii` both
passed their documented semantic/ordered checkpoint; and
`./scripts/verify-palomar.sh` passed the compatibility build, import-closure
audits, comparator, NanoDa and Lean-kernel replay. The expected
`./scripts/check-release-readiness.sh` result is exit 1 because all three
release statuses remain unverified. The workspace and `/tmp` headroom stayed
above their configured minimums throughout the replay.

## Follow-up lanes

The same-day follow-up wave extends the checkpoint with these disjoint worker
commits:

- `f14670b7318dddc535c1aa74f9ad7e6eb20788a9` —
  `FullSymbolRightLocalization.common_right_clear`, clearing any finite family
  of right-localized terms after an actual common denominator is supplied.
- `461e0a0e2a4b69e98f9c31bb84e4fcfc44449863` —
  `WeightedDetectionComposition`, composing finite weighted detection with a
  nilpotent right correction.
- `3a9526c7e5f1f618de5f5281b24c7f6274ad9922` — `CentralField`, an explicit
  degree-zero central-field/filtered-algebra interface.
- `4431dc92b525b2c3300c473922aaf18a8b0d9db7` —
  `JacobsonScalarExtension`, connecting Jacobson-top generation reflection to a
  supplied commutative scalar-extension orbit basis.
- `8a17e8a1df2fbda20476468ff405ea07ac064513` — `FiniteScalarAvoidance`, finite
  bad-set union and scalar-avoidance arithmetic for the two-call interface.
- `426c26826e1f6637cd57ab336c7b564dbf56c3e6` —
  `CharacteristicSupportFiniteProducer`, consuming indexed finite-colon
  generator expansions to produce a Module.support union while retaining the
  original-ring pencil certificates.

At the controller integration commit `814dee5b47d6366eb218f9e72c72a41a7a977237`,
the follow-up source and its independent oracle were checked with
`lake env lean --trust=0`; the source and oracle closures use only
`propext`, `Classical.choice`, and `Quot.sound`, with no new `sorry`. These are
conditional consumers: they do not construct the full-symbol Ore set, the
noncommutative finite-length block decomposition, the characteristic-support
producer, strict support removal, the universal base/successor, or the
original-U simultaneous source. The integrated replay produced a successful
`lake build SymplecticStafford` (8,792 jobs), and both phase scripts plus
`verify-palomar.sh` passed their documented checkpoint checks after the
integration. `release-gates.yaml` remains fail-closed.
