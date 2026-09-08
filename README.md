# Symplectic Stafford formalization

Lean 4 scaffold for the formalization of the ordered same-divisor identity

```text
1 = d * R + F * d * S
```

for the project’s class of simple symplectic quantizations.  The identity is
noncommutative: the displayed factor order is part of the statement.

This repository is intentionally at the scaffold boundary.  It makes no
claim that the universal theorem has been proved.  Phase I will formalize
the project-owned algebraic and filtered interfaces over the actual carriers;
Phase II will prove or eliminate the remaining literature assumptions.  The
paper proof, its hypotheses, and its current open higher-dimensional scope
remain in the sibling `symplectic-stafford` research repository.

## Reproducible setup

The initial build uses the same pins as the verified `global-stafford-formal`
baseline:

| Dependency | Revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.0` |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| AlgebraicAnalysis | `faa64814d5a310dc925e330af58e000f129f1098` |
| Stafford38 formal | `784b59925beb9a480519142336bd6434f6eeef16` |

With Lean and Lake installed:

```sh
lake build
lake env lean tests/StatementOracle.lean
```

Lake’s generated dependency directory is ignored by Git.  Do not commit
`.lake` or generated `.olean` files.

## License and ownership

Source and documentation are released under Apache-2.0 when this repository
is published.  See `LICENSE` and `NOTICE`.  The research manuscript is not
part of this repository.  Publication, Palomar registration, and any public
release remain explicit maintainer decisions after both formalization phases
and the compatibility audit.
