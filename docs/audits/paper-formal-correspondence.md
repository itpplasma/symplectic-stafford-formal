# Paper and formal correspondence audit

Audit date: 8 September 2026.  Reader: a referee or release maintainer who
needs to distinguish the final paper candidate from the checked Lean
checkpoint.  The paper repository was inspected at `e3c7077d3d51772d97d8e72bb219a8fc36765682`; the formal checkout was inspected at its current
working tree.

## Executive finding

The formal checkpoint faithfully fixes the ordered right-certificate syntax
and proves elementary semantic consumers.  It does not yet formalize the
paper's all-dimensional producer, finite-test induction, localization, or
terminal extraction.  Phase I, Phase II, and public-release status must remain
pending.

## Exact correspondence

| Paper target or obligation | Formal declaration or file | Finding |
| --- | --- | --- |
| `1 = d * R + (F * d) * S` for every nonzero original `d` | `OriginalSameDivisor` in `SymplecticStafford/Semantics/Contract.lean`; `SameDivisorIdentity` in `Statement.lean` | The proposition's product order matches. No theorem derives it from the paper's filtered/symplectic hypotheses. |
| Strong affine target `1 = d*R + ((B + H*a)*d)*S` | `Ordered/Affine.lean` | Only ring identities are proved. There is no affine source-existence theorem, and centrality of the scalar parameter is not encoded. |
| M01 right ideals and right-module quotients | `RightIdeal`, `RingRightIdeal`, `RightQuotient` | The semiring right ideal and ring quotient structures are separate. No constructor connects `twoGeneratedRightIdeal d f` to a `RingRightIdeal`, so the quotient API is not instantiated at the target carrier. `quotientRightAction` is a relation-respecting operation; unit and associativity laws for a right action/module are not proved. |
| M02--M05 filtered/Rees localization, detection, and minimal-prime length | `docs/proof-graph.yaml` GAP nodes | No corresponding Lean declarations exist. The paper's actual algebraic Ore/localization and support obligations remain open. |
| M06--M07 finite tests and activated pencils | `FiniteLength/Pencil.lean` | `finite_pencil_exceptions` handles a finite product of division-ring coordinates with nonzero coordinate hypotheses. It does not prove the paper's division-coefficient LLD, composition-length lifting, `vL=0`, or `e=vB+uL` interfaces. |
| M08 common colon and support-union assembly | `Ordered/Affine.lean`, `Ordered/RightClear.lean` | Expansion and finite common right-power clearing are checked utilities. The actual `K`, `J`, polynomial containment, localization, and support-union theorem are absent. |
| M09--M10 strong `P_h` and successor induction | `docs/proof-graph.yaml` GAP nodes | No predicate, carried finite test lists, two lower-index recursive calls, old/new minimal-prime split, or termination theorem is formalized. |
| M11 original cofactors, opposite hypotheses, and Stafford package | `original_one_generation`, `LeftOppositeCertificate` | These are semantic equivalences and single-certificate transport only. There is no final finite-cofactor extraction, automatic opposite filtered-class theorem, or formalized package consumer. |
| Palomar challenge | `Challenge.lean`, `Solution.lean` | Correctly isolated. The challenge is the definitional membership contract; its one `sorry` is deliberate, and the solution proves the same proposition without importing the challenge. It is not the paper theorem. |

## Status and pin discrepancies

The paper's authoritative current commit is `e3c7077d3d51772d97d8e72bb219a8fc36765682`.
The formal `PLAN.md`, `formalization.yaml`, verification record, and dossier
still identify `502b65a1dea53cac52220a08e321bfba525bc72e`.  Either retain
`502b65a1...` as an explicitly frozen source snapshot or update every source
record together after the final paper commit is selected; a mixed source
boundary is not reproducible correspondence evidence.

The checked Stafford38 formal repository at `784b59925beb9a480519142336bd6434f6eeef16`
pins AlgebraicAnalysis at
`dfdd2da091a9d67e7a29cc7914f192d746a2400d`, whereas this formal checkout
now pins the latest public AlgebraicAnalysis commit
`44921f5914c5dbd40d2d532c2867adce0f519cb9` in both
`lakefile.toml` and `lake-manifest.json`.  The downstream semantic build has
been rerun at this latest pin in the isolated verification checkout; the
remaining Stafford38 working-tree pin difference is recorded rather than
silently rewritten.

The formal proof graph labels the implemented `ordered-algebra` and
`finite-length-pencil` modules as `GAP`, even though their declarations and
independent consumers compile.  Use an explicit checkpoint status (or a
`LEAN`/`LEAN-CHECKPOINT` kind) for those nodes while retaining the absent
localization/source-selection/assembly nodes as gaps.  Conversely, retain a
gap annotation for the quotient node until actual right-action laws and the
generated ring-right-ideal bridge are proved.

## Safe release wording

The following wording is supported: “This checkpoint proves the original-ring
ordered semantic contract, quotient relation-respecting operation, opposite
certificate transport, ordered identities, finite common right-denominator
clearing, and a coordinatewise finite pencil lemma under the pinned
environment.  It does not formalize or certify the all-dimensional paper
producer or the Stafford package.”  Do not call the checkpoint a proof of
the universal same-divisor theorem, a completed Phase I/II formalization, or
a public Zenodo release.
