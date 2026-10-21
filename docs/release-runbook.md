# Target A release runbook

The author authorized release preparation and Palomar submission on 21 October
2026. This runbook records the exact source, checks and receipts needed to
carry out that request. Independent human mathematical review remains pending;
it must be reported honestly and is not supplied by an agent audit. A final
human-readable manuscript is a separate later deliverable.

## Select and verify the source snapshot

The submission is the complete affine same-divisor theorem, Target A, not an
earlier finite-pencil checkpoint. The Challenge must import Mathlib only;
the Solution must not import the Challenge. Preserve the pinned Lean and
Mathlib revisions and the three permitted axioms. The active package has
exactly one direct dependency, Mathlib. Replay retired scaffolds only from
the [frozen historical checkout](history/legacy-build-environment.md), not
by restoring their dependencies to the submission package. Their former
Stafford38 dependency shadowed the root Challenge in official preflight.
Any earlier local or CI pass applies only to its named snapshot; dependency
removal requires a fresh native build, CI and complete official preflight.

Use a clean immutable source commit. Run the required checks from a fresh
checkout with fixed dependencies:

```sh
bash scripts/verify.sh
bash scripts/bootstrap-palomar-tools.sh
bash scripts/verify-palomar.sh
```

The full repository source audit must also meet Palomar's source-format
requirements, including every tracked Lean file. Retain command exit statuses,
logs and their hashes, endpoint axiom reports, import audits, and the
Comparator log with NanoDa, con-ron and Lean-kernel acceptance. Record the exact
source commit and tool revisions in `docs/verification-results.json` and the
evidence files named in `release-gates.yaml`.

The historical evidence phase names are retained for compatibility:

| Phase | Current meaning |
| --- | --- |
| `phase_i` | Target A statement correspondence, closure of M01–M11, literature-leaf audit, build and independent consumers |
| `phase_ii` | Independent replay of the complete Target A proof, including allowed axioms and independent kernel checking |
| `palomar` | Exact Challenge/Solution comparison and compatibility replay |

No check may be marked pass merely because the theorem is declared. Each
required check in the manifest needs concrete evidence for the submitted
source. The readiness script fails unless publication is enabled, every
required phase is verified and its matching evidence records all required
checks as pass. This metadata gate supplements the replay; it does not replace
it or certify human review. The controller enables publication only after
checking the concrete snapshot and evidence.

The release commit may add documentation, citation metadata and verification
evidence after the checked source snapshot. Its Lean sources, dependency pins,
Comparator configuration and verifier scripts must still match that snapshot;
otherwise replay is required. Retain the exact tree inventory so this relation
can be checked without interpreting a claim about unchanged sources.

## Keep paper and Lean synchronized

Use the [paper/Lean correspondence](paper-lean-correspondence.md), its
[machine-readable map](paper-lean-map.json), and the
[submission scope](target-a-submission-scope.md). The research source is
[symplectic-stafford](https://github.com/itpplasma/symplectic-stafford); the
map records the immutable source revision and file hashes. Public replay uses
the formal-only map check because the research snapshot is private. Full
correspondence replay must also set `PAPER_REPO` to that research checkout; it
checks the immutable Git blobs as well as the Lean declaration map. Retain
these two verification scopes separately. Check for drift before submission
and when either side changes. Keep corrections discovered during formalization in that research
repository's `docs/formal-proof-route-2026-09-30.md`.

The final manuscript must be derived from the mapped exposition plus its
recorded corrections, preserving hypotheses, factor order and the exact scope
of each consequence. The old dossier is historical and is not a prerequisite
for submitting the complete Lean theorem. A later final manuscript or dossier
must pass its own correspondence and rendering checks before being attached
to a release.

## Palomar submission and receipt

`comparator.json` compares
`SymplecticStaffordChallenge.universalStatement`, the full affine same-divisor
statement. After the selected snapshot is public and the replay is complete,
submit the full 40-character commit from
[symplectic-stafford-formal](https://github.com/itpplasma/symplectic-stafford-formal),
project directory `.` (or blank), using `comparator.json` and
`formalization.yaml`.

Run the complete reusable `palomar-preflight.yml` workflow in `mode: full`
against that exact public commit, using the pinned pipeline revision and
`palomar-standard-v1` profile. Retain its actual `mechanical-report.json`
with `status: pass`; a local build or comparator pass does not replace this
preflight. Project CI must also pass the trust-disabled consumers and map
checks on a clean runner.

Follow [Palomar's agent protocol](https://submit.palomar-registry.org/llms.txt).
Before intake, present the exact repository, full commit, Comparator path
and responsible-author/maintainer relationship to the author for agreement.
After mechanical verification and automated review, show the actual private
review and explain what registration will permanently publish. Register
only after the author's decision on that review. These are service protocol
requirements, separate from independent human mathematical peer review.
Local acceptance or a preflight report is not a registration receipt.

Retain the submitted commit, submission timestamp, returned status URL and
registry identifier. Update repository metadata only from that actual
receipt. Keep any pending automated registry review distinguishable from an
accepted registration. Never borrow a Stafford38 identifier or infer
registration from a successful Comparator run.

## Optional signed GitHub and Zenodo release

A GitHub/Zenodo publication is separate from Palomar registration. Select an
unused version tag and record the exact archive and checksums:

```sh
formal_commit=$(git rev-parse HEAD)
test -z "$(git status --porcelain)"
release_dir=$(mktemp -d /tmp/symplectic-stafford-release.XXXXXX)
git archive --format=tar.gz --prefix=symplectic-stafford-formal/ \
  --output="$release_dir/symplectic-stafford-formal.tar.gz" "$formal_commit"
shasum -a 256 "$release_dir/symplectic-stafford-formal.tar.gz" \
  > "$release_dir/SHA256SUMS"
tar -tzf "$release_dir/symplectic-stafford-formal.tar.gz" >/dev/null
release_tag='v0.1.0'
git tag -s "$release_tag" "$formal_commit" \
  -m "Symplectic Stafford formalization $release_tag"
git verify-tag "$release_tag"
git push origin "refs/tags/$release_tag"
gh release create "$release_tag" --verify-tag \
  --title "Symplectic Stafford formalization $release_tag" \
  --notes-file docs/release-notes.md \
  "$release_dir/symplectic-stafford-formal.tar.gz" \
  "$release_dir/SHA256SUMS"
```

Do not replace an existing tag or bypass signing if the signing key is
unavailable. Attach only artifacts verified for that source; the final paper
can be released later.

For Zenodo, an authorized maintainer enables the public repository in its
GitHub integration. Read the version and concept DOI from the resulting
record, download its source archive and compare it with the tagged tree.
Record the issued DOI in a later citation commit without moving the release
tag. Retain the source archive, checksums and receipt together. No existing
Zenodo integration or issued DOI is assumed here.

Formal code and documentation are Apache-2.0 with `LICENSE` and `NOTICE`. A
future manuscript remains a separate research artifact and does not acquire
its license from this formal package.
