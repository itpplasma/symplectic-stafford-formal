# Symplectic Stafford formalization plan

```yaml
phase: parallel-all-dimensional-formalization
phase_i_status: partial
phase_ii_status: not-started
terminal_theorem_claimed: false
public_release: false
palomar_registration: not-submitted
```

This file owns formal status. Semantic modules implement right ideals,
literal membership, quotient right action and opposite orientation. Ordered
modules implement affine identities and conditional constant-right-denominator
clearing. The finite-pencil module treats finitely many division-ring
coordinates; this does not yet establish the paper's arbitrary finite-length
module, activated-pencil or original-U simultaneous-source theorem.

The paper candidate is in the sibling `symplectic-stafford` repository at
commit `502b65a1dea53cac52220a08e321bfba525bc72e`. Its claims remain paper
claims until the corresponding Lean declarations and audits are complete.
Its terminal index, roadmap and ledger were refreshed at
`e3c7077d3d51772d97d8e72bb219a8fc36765682`. The paper is a complete
self-audited candidate in every finite dimension; independent mathematical
audit, human review and both formal phases remain separate obligations.

The final target is `∀ d ≠ 0, ∃ F R S, 1 = d * R + (F * d) * S`,
strengthened to `∀ d ≠ 0, ∀ B, ∀ a ≠ 0, ∃ H R S,
1 = d * R + ((B + H * a) * d) * S` in the original algebra.
The ambient algebra is simple, infinite-dimensional and unital over an
infinite characteristic-zero central field, with an exhaustive separated
nonnegative multiplicative locally finite filtration, degree-zero piece equal
to the field, and commutative affine-domain associated graded of finite
dimension. No DL/Bn lower support bound is a premise of this final core.

## Parallel implementation

Use [the phase instructions](docs/phase-instructions.md) and
`docs/proof-graph.yaml`. Mandatory final-paper obligations are M01–M11:
semantics; filtered/Rees foundations; full-symbol Ore localization; faithful
good-module detection; minimal-prime local length; original-U finite tests;
activated pencils; common-colon support union; strong finite-test P_h;
the two-call dimension induction; and original cofactors/opposite/package.
The controller integrates checked changes and owns phase promotion.
The existing `AdmissibleSymplecticClass` in `Contract.lean` is a historical
fourfold scaffold with dimension-four/B2 fields and proposition labels; it
does not encode the final all-dimensional algebra class. M01 must supply the
actual structural semantics before any terminal endpoint is certified.

`Challenge.lean` and `Solution.lean` currently compare the definitional
membership contract alone. The name `universalStatement` does not identify
the universal Stafford theorem. The dossier states their exact correspondence.

## Gates

Phase I must discharge every project-owned ledger item (including the
original-ring source-selection and assembly interfaces) and record a clean
independent replay. Phase II must then replace the remaining literature
assumptions. The only permitted terminal axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

The current executable checks are:

```sh
./scripts/verify.sh --phase-i
./scripts/verify.sh --phase-ii
./scripts/verify-palomar.sh
```

The first command covers the implemented checkpoint only; the latter two are
not release evidence until their complete endpoint sets exist. Publication is
fail-closed by `release-gates.yaml` and `scripts/check-release-readiness.sh`.
