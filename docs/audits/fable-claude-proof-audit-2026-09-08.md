# Fable/Claude paper proof audit — 2026-09-08

This is the requested independent one-shot audit of the paper candidate.  The
reviewer read `symplectic-stafford@e3c7077` (which indexes the mathematical
source frozen at `502b65a`) and the formal checkpoint through `dab16fc`, with
its uncommitted files.  It was read-only; it did not promote a phase, change
visibility, publish, or push.

## Verdict

The reviewer found no invalid bridge in the written all-dimensional proof.  In
particular, the right-sided Ore order, finite-test transport, minimal-prime
dimension decrease, two lower-index calls in the auxiliary-divisor induction,
original-algebra extraction, and opposite-ring argument survived an
independent dependency-order reconstruction.  The verdict is a paper-level
pass only: M02--M11 remain unformalized, and human review is still open.

Two presentation sentences were recommended for a future paper revision:

- state explicitly that centrality embeds (E(t)) into (E((t))) in the
  whole-chart source argument (or give the finite recursion); and
- spell out the common-denominator/central-root bound used when specializing
  (E(t))-invertibility to all but finitely many central parameters.

These are explanatory additions, not repairs to a detected invalid step.  The
paper checkout is upstream-owned under the project rules, so this checkpoint
records the recommendations without modifying the paper source.

## Formal and release findings

- `tests/FilteredSourceOracle.lean` was repaired and independently passes;
  its former Nat source-selection example was impossible for (d=2).
- `Source/Assembly.lean` now labels finite-candidate and uniform-source
  structures as scaffolds and exposes a divisor-indexed conditional shape.
- `Filtered/Localization.lean` remains a single-denominator clearing
  contract; it is not the paper's full symbol-set Ore localization.
- `StrongPh.lean` is a conditional M09--M10 plumbing contract; its witness
  fields do not prove the admissible-class producer.
- Only `check-release-readiness.sh` is a publication gate.  The checkpoint
  Phase-II and Palomar commands are not, by themselves, phase completion or
  release evidence.
- Public pins observed by the one-shot audit were Lean/Mathlib
  `v4.33.0`/`db584cd...`, AlgebraicAnalysis `44921f5...`, and Stafford38
  `784b599...`.  The public AlgebraicAnalysis main head subsequently advanced
  to `46f2c819deca0e9735a436bed94ebed03ae35090`; the controller checked that
  isolated clone and reran the downstream root and phase-I checkpoint replay.

## Controller addendum

The later formal slices (right-ideal bridge/action laws, algebraic bounded Rees,
finite-support and matrix-pencil detection, differential-Ore finite-cover
clearing, common-colon finite generation, concrete finite-index composition,
terminal boundary, and explicit opposite transport) compile under the newer
AlgebraicAnalysis head. They remain conditional utilities; this addendum does
not alter the paper-level verdict or promote any release gate.

Safe public wording is limited to: a self-audited written paper candidate,
the checked semantic/ordered/scalar Lean utilities, and a definitional
Challenge/Solution contract.  It is not safe to claim formal verification,
Phase I/II completion, a DOI, or a universal Lean theorem.
