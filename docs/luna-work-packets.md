# Luna work packets for Symplectic Stafford

Frozen planning base: `2d02f41508515390f92880d191be7ef629f37180`.
This document is worker scaffolding, not a phase promotion. `PLAN.md`,
`docs/proof-graph.yaml`, the endpoint lists, and the release gates remain
authoritative.

## Submission order

1. **Finite-central division-pencil target (first new candidate).** Audit
   `FiniteLength/FiniteCentralDivisionLLD.lean` as the smallest mechanically
   complete theorem developed in this repository: finite-dimensionality over
   the center gives a finite bad-scalar spectrum without a determinant
   shortcut. It has a realistic path to a hole-free standalone artifact,
   although its editorial interest is uncertain and must be assessed before
   presenting it as a submission.
2. **Finite bounded filtered theorem.** Close the strongest honest bounded
   fragment of the Part I.5 bridge: finite genuine filtrations with
   finite-length associated layers. This supplies a bounded library lemma; its research interest is not
   established, and it does not cover the paper's unbounded localized
   filtration.
3. **Weyl transfer (accepted provenance, not a new result).** The repository
   proves `sameDivisor_of_weylAlg_algEquiv` by transporting the pinned
   Stafford38 theorem. It is useful regression and correspondence evidence,
   but the mathematical result belongs to the existing Stafford38
   formalization and should not be presented as a new standalone contribution.
4. **Actual ideal-quotient M08 support sequence.** Construct the standard
   short exact sequence for a concrete ideal inclusion and feed it to the
   checked support-union theorem. This removes a supplied map/exactness
   callback in the commutative ideal-quotient case. The identification with
   the paper's common-colon characteristic modules remains separate.
5. **Universal symplectic target.** Attempt only after the actual filtered
   algebra, homogeneous localization, local module, source map, and support
   objects exist. The first unresolved paper gap is still the passage from
   homogeneous-symbol localization `G_{Sigma_p}` to finite composition length
   of the noncommutative `T_p` module. Ordinary localization at `p` does not
   supply this, and an unbounded quotient filtration can have zero associated
   graded module while the quotient is nonzero.

## Worker protocol

Use Luna xhigh first. Give each worker exactly one source file and one oracle
file, with no overlapping ownership. A worker may inspect dependencies but
must not edit root imports, plans, graphs, gates, manifests, or endpoint lists.
The controller alone integrates and promotes evidence.

Each attempt has a 15-minute ceiling, a 64 MiB log ceiling, and may run only
targeted `lake env lean --trust=0 FILE` checks. Across the three formal
repositories, keep at most three targeted Lean processes active. Do not make
worktrees, copy dependencies, download packages, run a root build, or fill
temporary storage. Current resource floors are 20 GiB free in the checkout,
8 GiB free in temporary storage, and 100,000 free inodes.

Reject any result containing `sorry`, `admit`, a project `axiom`,
`native_decide`, `Lean.ofReduceBool`, a new hypothesis equivalent to the
conclusion, or a structure that merely stores the missing theorem. An oracle
must construct a nontrivial example and consume the theorem behavior; a
restatement of the source theorem under variables is not an independent
oracle. Record the exact base commit, changed paths, theorem types, commands,
outputs, and `#print axioms` results.

Escalate only on a concrete failure transcript:

1. Luna xhigh implements the smallest proof.
2. Sol low inspects and repairs a compiling or nearly compiling patch.
3. Sol medium handles a persistent API or proof-design failure.
4. Astra low audits a suspicious bridge or repairs a hard localized defect.
5. Astra medium is reserved for a genuinely unclear mathematical implication,
   especially the universal Part I.5 gap.

## Packet S1: finite filtration length

Ownership:

- `SymplecticStafford/Filtered/FiniteFiltrationLength.lean`
- `tests/FiniteFiltrationLengthOracle.lean`

Read `Filtered/ActualClassSupport.lean` and
`Filtered/StrictFiniteGradedChain.lean`. Prove a theorem for the existing
`FiniteFilteredModule`: if each actual associated quotient layer has finite
length, then the underlying module has finite length. Prefer an exact length
sum or explicit finite bound when Mathlib's exact-sequence length API supports
it without expanding scope. The proof should use the real filtration
submodules and quotient exact sequences, not a transfer callback.

The oracle must use a filtration of `Q^2` (or an equally nontrivial module)
with a proper intermediate submodule, establish the layer hypotheses, invoke
the producer, and inspect its axiom closure. This is a bounded strictness and
length result. It does not establish that the localized paper module admits
such a finite filtration or compare `G_{Sigma_p}` with `G_p`.

## Packet S2: ideal-quotient exact support

Ownership:

- `SymplecticStafford/Ordered/M08IdealQuotientExact.lean`
- `tests/M08IdealQuotientExactOracle.lean`

Read `Ordered/M08ExactSupportBridge.lean`. For commutative `A` and ideals
`I <= J`, construct the actual linear maps and exactness data for

```text
J / I  -->  A / I  -->  A / J
```

using Mathlib quotient modules or an equivalent canonical kernel quotient.
Then derive the exact support equality from the existing theorem. The source
must construct the maps and prove injectivity, exactness, and surjectivity;
it must not accept those facts as fields or hypotheses.

The oracle should use `A = Z`, `I = (6)`, and `J = (2)`, demonstrate that the
maps act as intended on explicit classes, consume the support equality, and
print axioms. This closes only the standard commutative ideal-chain case. A
later proof must identify the paper's associated common-colon modules with
these quotients.

## Packet S3: finite-central division-pencil submission audit

Ownership for a fresh worker after S1/S2 review:

- `docs/audits/finite-central-division-lld-submission.md`

Freeze and audit the exact declarations in
`FiniteLength/FiniteCentralDivisionLLD.lean`. Record their mathematical
statement, proof dependencies, axiom closure, independent oracle behavior,
and which part is genuinely new to this repository. Assess whether the result
is substantial enough for a standalone Palomar entry or should remain
supporting evidence inside a larger formalization.

Do not add another challenge file with a deliberate hole: the global source
audit permits `sorry` only in the existing `Challenge.lean`. Do not replace
the current checkpoint files, alter release metadata, or request publication
or licensing decisions during this audit. If the result merits a comparator
submission, the controller must first choose a layout compatible with the
single-hole verifier and prepare a concrete reviewable package.

## Deferred universal packets

These are not Luna-xhigh implementation tasks yet because their required
objects are absent, and adding more conditional records would not advance the
proof:

- M01--M03: construct the actual filtered quantum algebra, its commutative
  associated spectrum, and the genuine homogeneous Ore localization.
- M04--M05: prove strict survival for subquotients over `G_{Sigma_p}` and
  transfer a finite graded length bound to the actual noncommutative local
  module. This is the first global blocker.
- M06--M07: build the actual finite local tests and source maps, including
  repeated noncommutative division blocks, rather than assuming cyclic-top or
  orbit data.
- M08: identify the colon quotients with actual characteristic modules and
  derive the localized-zero/support union from those maps.
- M09--M10: prove source-dependent strict support removal and retention of all
  carried tests, then construct the universal base and two-call successor.
- M11: compose the existing actual support-to-cofactor extraction only after
  the preceding producers supply the real endpoint defect; opposite transport
  and literal cofactor order are already checked.

For these packets, Luna may search for existing library lemmas or build small
countermodels. Escalate to Astra only when the question is whether the needed
implication is mathematically valid under the paper's exact hypotheses.

## Implemented and reviewed in this wave

The finite-filtration length theorem and its rational-plane oracle are
implemented and passed independent Sol-low review. The selected
finite-central-pencil Challenge/Solution pair also passed independent
Sol-low review and the full local Palomar verification script. Full
checkpoint and behavioral-test results are frozen separately in
`luna-wave-20260909.json`. These are bounded results; all M01--M11 terminal
obligations and public release gates remain open.

## Active draft batch — checks deferred by user

Write the complete source batch before the consolidated build/repair pass.
`SymbolFractionReesMap.lean` is the Luna-xhigh source-map packet: actual
original Nat-indexed Rees ring into the integer Laurent Rees ring.
`SymbolFractionReesLocalization.lean` is the separate Luna-xhigh packet:
combine that map with support_right_clear to reconstruct an original Rees
numerator after one right homogeneous denominator. Coordinate the map API.
Neither packet may assume the desired representation or Noetherianity.
The filtration, Jacobson, Rees units and support-clearance sources have
independent reviews and targeted kernel evidence. Full-wave verification
remains deferred; do not infer universal M01–M11 or release closure.
