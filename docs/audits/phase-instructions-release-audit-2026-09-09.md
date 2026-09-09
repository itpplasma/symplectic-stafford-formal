# Phase instructions, dossier and release metadata audit

This audit is for a release maintainer deciding whether the formal evidence
matches the paper theorem. The reviewed formal commit is
`2676781b9b20c8744af1e619570fec9617e52c58`. The tracked worktree was clean;
its empty patch SHA-256 was
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
Concurrent untracked Lean files were excluded from this review.

The mathematical source remains frozen at
`502b65a1dea53cac52220a08e321bfba525bc72e`, with its instruction snapshot at
`e3c7077d3d51772d97d8e72bb219a8fc36765682`. These commits have distinct
documented roles; their coexistence is not a source-pin discrepancy.

## Verdict

The pending Phase I, Phase II and publication statuses are correct. The
checkpoint declarations and semantic comparator do not establish the
terminal theorem. The current release-readiness script is insufficient to
verify the release obligations in the runbook. Documentation corrections
record that distinction without promoting status or changing executable gates.

## Formal correspondence

The first missing terminal correspondence remains the actual filtered class
and characteristic module over `gr U`. `AdmissibleSymplecticClass` retains
historical B2 fields and proposition labels. Finite associated-layer support
and its cardinality do not supply support in `Spec(gr U)` or its Krull
dimension. `SpecCharacteristicSupport` instead consumes a supplied
commutative associated module and class map.

Several constructed substeps should no longer be described as absent:

- `ReesRing` constructs the bounded-polynomial subring from negation-closed
  filtration data. Its Noetherianity and the paper's graded/localized
  identifications remain open.
- `ActualM08Producer` constructs finite right generators from actual right
  Noetherianity. The filtered proof of that hypothesis and characteristic
  support union remain open.
- `JacobsonTop` proves actual radical-quotient generation reflection.
  The noncommutative block and activated-pencil arguments remain open.
- `FilteredMinimalPrimeBridge` proves finite length over an actual
  commutative prime localization from support dimension zero. It does not
  transfer length to the paper's noncommutative right module over `T_p`.
- `TwoCallAffineProducer` constructs the affine pencil coefficient from
  two lower witnesses, retaining explicit defect-removal and test-generation
  hypotheses.

The phase instructions and dossier now distinguish these constructions from
their remaining universal applications. This review inspected declaration
types and proof dependencies; it did not replay the full Lean checkpoint or
certify the complete written proof.

## Endpoint and release evidence

`docs/phase-i-endpoints.txt` contains two semantic declarations.
`docs/endpoints.txt` adds the definitional membership theorem
`SymplecticStaffordChallenge.universalStatement`. Neither list describes the
terminal M01–M11 closure. The current source audit rejects project axioms;
the prospective Phase I literature-leaf registration policy is not an
implemented assumption workflow in the checkpoint verifier.

The committed release manifest correctly fails the readiness script with
exit status 1 because all three phase statuses are pending. An independent
synthetic manifest produced exit status 0 despite all of the following:

- `publication.enabled` was false;
- the target was `missing-terminal-theorem`;
- every required-check list named an absent check;
- each evidence file contained only its matching `phase` and `result: pass`.

The synthetic manifest marked all three phases `verified` and supplied the
three minimal evidence files. The script printed
`release gate: Phase I, Phase II, and Palomar evidence verified`.
This confirms that it validates labels and file presence, without validating
the required-check results, proof closure, source identity, comparator scope,
or publication authorization. The fixture was isolated under
`/tmp/symplectic-stafford-release-audit.2yfyx9`; no project release state changed.

The runbook now requires a terminal Challenge/Solution pair before terminal
submission and describes the current semantic pair as checkpoint evidence.
The release manifest records the required evidence checks, and the readiness
script now fail-closes on `publication.enabled`, the target, and every listed
check result in addition to the phase/result labels. Human review of terminal
correspondence, source identity, proof closure and comparator scope remains
required; no release approval follows from the metadata gate.

## Documentation validation

The prose checker passed on the changed Markdown, TeX and YAML files.
`docs/dossier/build.sh` regenerated the map and claim register without a
tracked change to either generated file, and built the 12-page dossier.
The final TeX log contained no warning, undefined-reference or overfull-box
messages. `git diff --check` passed. Concurrent implementation commits
advanced main during this documentation pass. The PDF build manifest records
the build-time commit `a362849ff42b6e4fa2e428b7316baf30c7448656`, input hashes
and dirty documentation worktree; it is a development artifact rather than
clean-release evidence. The declaration-scope audit remains frozen at the
earlier commit stated above.
