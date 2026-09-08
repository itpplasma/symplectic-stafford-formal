# Phase I and Phase II instructions for the final paper

These instructions are for formalization workers and the integrating
controller. They follow paper commit
`502b65a1dea53cac52220a08e321bfba525bc72e` and the authoritative roadmap and
ledger at `e3c7077d3d51772d97d8e72bb219a8fc36765682` in
`itpplasma/symplectic-stafford`. Read that revision's terminal proof index,
main all-dimensional paper, parts I–III, and all-dimensional proof graph.

## The target and semantic audit

Keep `1 = d * R + ((B + H * a) * d) * S` in the original algebra, for every
nonzero original divisor d, arbitrary B and nonzero a. The same-divisor target
is B=0, a=1. Preserve the full simple connected locally finite filtered-domain
hypotheses in PLAN.md; do not add DL/Bn, tensor simplicity, finite-dimensional
modules or an assumed source producer to the statement. Prove degree-zero
equals the central field image. Any left-module encoding must prove its
right U/opposite transport.

Use integer or bottom-extended support dimension with delta(0)=-1. Natural
truncated subtraction at D-(D+1) cannot express the terminal argument.

## Project-owned obligations

| ID | Required proof and source | Completion boundary |
| --- | --- | --- |
| M01 | Original U, right ideals/quotients and support dimension; main 0,5 | Literal membership, quotient action, no hidden existence field |
| M02 | Filtered/Rees Noetherianity and good subquotients; I.1 | Bounded-shift independence of radical characteristic support |
| M03 | Full-symbol Ore/Rees/module localization; I.2–I.3 | Actual algebraic fractions and exact passage; no completion substitute |
| M04 | Weighted-top matrix inversion and detection; I.4 | Nonzero good modules detected even with negative degrees |
| M05 | Minimal-prime local composition length; I.5 | Arbitrary finite good module, only at minimal support primes |
| M06 | Division-coefficient LLD and finite affine tests; II.1–II.4 | One original-U multiplier with all offsets and nonzero tails |
| M07 | Activated and generating-vector pencils; II.5 | Fixed finite-length module, vL=0 and e=vB+uL |
| M08 | Common colon ideal and support union; main 1 | Actual finite generators, polynomial containment and constant right clearing |
| M09 | Strong P_h and admissible test lists; main 0,2,3 | All divisors, all B+Ua, every finite local test list |
| M10 | Successor and termination; main 3–5 | Two P_h calls for P_(h+1), old/new split, all tests retained |
| M11 | Original R,S, opposite hypotheses and package; main 5–6, III.1 | Exact terminal identity and separately checked banked consumers |

M08 fixes `K={s | G*d*s ∈ dU}` and `J=dU+F*d*K`. For every generator k
with `G*d*k=d*c`, preserve the certificate
`F*d*k=d*(-t*c)+(F+t*G)*d*k` for central t. A free-ring identity alone
does not prove the localization/support-union theorem.

M09 retains each test's actual localization, finite-length cyclic module,
canonical generator, nonzero right tail and offset. M10 first applies P_h to
d, obtains an actual relation `F*d*L0=d*C0`, and applies P_h to `d*L0` with
the old minimal-module tests. Both calls have lower index than P_(h+1).
Control the support of the common quotient by both recursive bounds; remove
all its minimal components with one central scalar while retaining the carried
tests. Terminate at P_(D+1), then extract finite right cofactors in U.

## Parallel lanes and returned evidence

The short-algebra lane owns M01 and ordered M08/M11. The finite-module lane
owns M06–M07. The filtered lane owns M02–M05. The assembly lane specifies
M09 and proves M10 after the APIs are fixed. Package and model workers
consume M11 only at proved scopes. Workers return exact declarations, their
hypotheses, builds, independent consumer evidence and remaining gaps.
The controller alone integrates and promotes authoritative status.

The current coordinatewise `finite_pencil_exceptions` theorem is a reusable
scalar utility. General semisimple tops may have repeated simple factors and
matrix endomorphism blocks; a product of division-ring coordinates does not
by itself model them. M06 and M07 require that bridge and finite-length lifting.

## Phase I

For each selected terminal target, discharge all M01–M11 obligations in its
transitive proof closure. Only individually audited literature leaves may
remain: register an exact statement, source/version/locator, semantic wrapper,
owner and axiom entry. A proved imported declaration and an admitted external
assumption are different evidence. Project-specific P_h, local length, source
selection, support union and induction may not be relabeled literature.

Audit dependent definitions, instances, wrapper fields and imports as well as
the final proof term. A conditional theorem assuming its missing construction
is development progress, not Phase I. Freeze the source commit and, for
uncommitted review inputs, the worktree patch digest.

## Phase II and release

Replace each registered external assumption with a kernel-checked proof.
Every terminal declaration's transitive axiom closure must lie in
`{propext, Classical.choice, Quot.sound}`. Reject sorryAx, compiler/native
shortcuts, shadowed theorem names and unchecked custom axioms. Compare the
actual endpoint type against an independent mathematical statement, not only
against another copy of a weakened contract.

Retain exact Lean 4.33.0, Mathlib v4.33.0 and public dependency commits from
the verified lock files. Replay from a clean checkout and record invocations,
theorem types, imports, axiom reports and independent kernel results.
A semantic Challenge/Solution success does not release SS-all. Publication
remains controlled by release-gates.yaml and the release runbook.

## Historical and concrete branches

C01–C03 map to M01/M11, P01–P02 to ordered M08, P03 to M07, P04 to M06,
and P05–P07 to M02–M05. The old R01/R02 slots now have written candidate
M08–M10; their formal proofs are required. SS4/P08, DL/Bn/Gabber lower bounds,
cusp/crossing catalogues and alternative Morita routes are optional for this
terminal proof unless a named consumer uses them. Concrete Weyl, Kleinian,
domain-Morita, applicable D(X), and higher-dimensional instances still need
actual class hypotheses. Retain the physical module/progenerator gate and
the exclusions of arbitrary-projective freeness, rank-one cancellation and
automatic simplicity of tensor products.
