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

## Second parallel formalization wave

The subsequent disjoint lanes were committed and replayed in the controller's
worktree: `db9074e` (M01 right-ideal bridge), `857f945` (M02 algebraic Rees
subsemiring), `527e8c3` (finite associated-top detection), `4b50d51` (matrix
pencil avoidance), `3f6b776` (M08 finite-generation bridge), `f77a4cc`
(concrete M09--M10 successor contract), and `51a4632` (differential-Ore
finite-cover boundary). After importing these modules, `lake build
SymplecticStafford` completed 3046 jobs and the trust-disabled checkpoint
consumer replay passed. Every new declaration keeps its producer hypotheses
explicit; none promotes a universal source theorem or a release gate.

## Third parallel formalization wave

The next independent lanes added and checked commits 4d25d03 (finite filtered
module quotients and nonzero associated-layer extraction), 274869c
(conditional finite-generator characteristic-support cover and exact
common-colon pencil certificate), 41fa0fb (finite original-affine source
avoidance with explicit division-ring cofactors), 5b5df9a (activated
finite-length and repeated matrix-pencil bridges), 509aea2 (constructive
base/successor assembly with carried-test and original-cofactor fields),
0e63de3 (bounded Rees-module quotient and scalar-action laws), and 248fe65
(explicit original-ring power-Ore fraction boundary). The targeted
trust-disabled module/oracle checks passed for each lane. The aggregate import
and universal producer remain conditional; these commits do not promote
Phase I, Phase II, Palomar, or publication status.

## Fourth parallel formalization wave and Palomar compatibility

The controller integrated the finite bounded-generator filtration, finite
right-module composition filtration, Jacobson-top generation reflection,
finite power-Ore normal-form and associated-layer support lanes in
`3ab82b3`, then added the spectrum-support boundary (`4cbbe1b`), filtered
Noetherianity boundary (`a83f37e`), list-indexed division-LLD source selector
(`793d6e2`), full-symbol algebraic localization boundary (`e59a8da`), good
local finite-length bridge (`70bd608`) and activated finite-length pencil
consumer (`df95cb8`). Each lane supplied an independent concrete oracle and
trust-disabled checks; the aggregate `SymplecticStafford` build completed
3066 jobs. The phase-I and phase-II scripts pass their implemented
semantic/ordered checkpoint, while the ledger remains partial.

The Palomar tools were bootstrapped at their pinned revisions. The initial
comparator exposed a real module-name collision: Stafford38 also provides a
`Challenge` module, and Lake's dependency-first `LEAN_PATH` selected it. The
verifier now declares local Challenge/Solution library targets and prepends the
project artifact path for the direct comparator invocation. At this checkpoint
`scripts/verify-palomar.sh` passes the compatibility build, import closures,
lean4export comparison, NanoDa replay and Lean's default kernel replay. This
is evidence only for the elementary semantic Challenge/Solution pair; the
universal source producer and the Phase I/II/release gates remain open.

## Final controller replay at the recorded checkpoint

The exact controller commit is `d08fcfbfbc20a69486b725dfb0f586a977ab4436`.
At that clean commit, `lake build SymplecticStafford` completed 3066 jobs,
both `verify.sh --phase-i` and `verify.sh --phase-ii` passed their documented
semantic/ordered checkpoint, and `verify-palomar.sh` passed the pinned
compatibility build, import-closure audits, comparator, NanoDa and Lean
default-kernel checks. These are reproducible checkpoint results only: the
release manifest remains pending because the actual all-dimensional producer
and the M01--M11 Phase I/II endpoint proofs are not present.

## Fifth parallel formalization wave

The filtered lane then added `2e156d2` (`WeightedFaithfulBoundary`), making
finite nonempty coordinates, injective encoding and negative integer weights
explicit and recording the equal-weight off-diagonal failure boundary. The
induction lane added `b69a747` (`SuccessorObstruction`), a kernel-checked
flat-defect counterexample showing that the lower (P_h) contract alone cannot
force a one-step successor decrease. Both lanes passed trust-disabled source
and independent-oracle checks. These are boundary evidence, not producer
theorems; the universal faithful associated-graded construction and the actual
support-removal/scalar-avoidance successor remain open.

## Final controller replay at integrated boundary checkpoint

The integrated checkpoint is `0286e583d1a44ea3344d93c77ae16dd6e4b4c895`.
At this commit, the resource guard passed, `lake build SymplecticStafford`
completed 3069 jobs, both phase scripts passed their documented
semantic/ordered checkpoint, and `verify-palomar.sh` passed the pinned
compatibility build, import-closure audits, comparator, NanoDa and Lean
kernel replay. The release gate remains intentionally pending: the new
weighted, support-union and successor-obstruction files are boundary evidence,
and the universal producer plus the M01--M11 Phase I/II endpoints are still
absent.
