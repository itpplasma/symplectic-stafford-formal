# Independent formal endpoint audit — 2026-09-08

This is an independent controller-side audit of the declarations present in
the semantic checkpoint. It does not promote either formalization phase or a
release gate.

## Source checks

The project source scan found exactly one proof hole, in `Challenge.lean`, and
no project `axiom`, `admit`, `native_decide`, or `Lean.ofReduceBool`
declarations. The occurrence in `Challenge.lean` is the deliberate challenge
placeholder; `Solution.lean` has no placeholder.

The following modules were checked directly with Lean 4.33.0 and
`--trust=0`:

```text
SymplecticStafford/Filtered/Localization.lean
SymplecticStafford/Source/Assembly.lean
```

The direct checks passed. The endpoint declarations reported only the normal
kernel foundations:

```text
Filtered.common_right_clear_from_certificate:
  propext, Classical.choice, Quot.sound
Source.SingleSourceAssembly.sameDivisor:
  propext, Classical.choice, Quot.sound
Ordered.affine_certificate_contract: propext
FiniteLength.finite_pencil_exceptions:
  propext, Classical.choice, Quot.sound
```

The temporary first check of `Filtered/Localization.lean` exposed a missing
RingHom notation import at `R →+* S`; the source now imports
`Mathlib.Algebra.Ring.Hom.Defs`, and the current file passes the direct check.

## Interpretation

`Source.SingleSourceAssembly.sameDivisor` is a conditional contract: its
`assemble` field supplies the original-ring witness. It is not a producer
theorem for the paper's admissible class. Likewise,
`FilteredLocalizationCertificate.right_clearable` supplies the clearing
hypothesis; it does not construct localization data. These declarations are
therefore safe checkpoint interfaces but cannot be used as Phase I or Phase II
completion evidence.

The release gate remains correctly fail-closed because `phase_i`, `phase_ii`,
and `palomar` are not marked `verified`.

## Superseding controller replay

After this initial audit, the AlgebraicAnalysis remote main head advanced to
46f2c819deca0e9735a436bed94ebed03ae35090. An isolated clean clone of that
head was installed, and the root build plus the phase-I checkpoint replay were
rerun successfully with Lean 4.33.0, Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d, and Stafford38
e77e176c381ca2d6b20c030f9227f1b031415d2e. The later raw-Rees,
support-boundary, activated-pencil-coordinate, common-colon, finite-index and
opposite-transport modules were also checked directly with trust disabled.
These results supersede only the pending-replay note below; they do not promote
the Phase I/II or publication gates.

## Pending replay

At the time of the initial audit the shared Challenge/Solution build process
was still compiling the pinned external Mathlib graph. That historical
observation does not negate the superseding phase-I replay above; Phase II and
the Palomar comparator remain pending as release evidence.

## Final independent replay

An independent endpoint lane then replayed the current worktree against the
same AlgebraicAnalysis `46f2c819deca0e9735a436bed94ebed03ae35090` lock. The
resource guard, source scan, `lake build SymplecticStafford` (3035 jobs),
`lake build Challenge` (2054 jobs), trust-disabled `Solution.lean`, endpoint
axiom audit, and all 21 `tests/*.lean` consumers passed. Only linter warnings
and the deliberate statement-only `Challenge.lean` placeholder remain. This
is independent checkpoint evidence, not Phase I/II completion or release
evidence.
