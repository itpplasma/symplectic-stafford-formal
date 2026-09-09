# Human release runbook

This runbook records the Stafford38-style release procedure. It is a checklist,
not authorization to change repository visibility, sign tags, submit to
Palomar, or publish a Zenodo deposit. The current `release-gates.yaml` is
intentionally pending.

The readiness script fail-closes unless `publication.enabled` is true, the
target is `SS-all-original-affine`, every required phase is `verified`, and
each evidence file has matching `phase`/`result: pass` labels plus a `checks`
mapping with every declared check marked `pass`. It still does not replace
human review of source commits, proof closure, terminal correspondence, or
comparator scope. A release maintainer must review the evidence below and
obtain the publication decision; changing status labels cannot satisfy those
requirements.

## Select an evidence-bearing commit

Release only a clean immutable commit for which a fresh, credential-free clone
has replayed all project checks. The selected commit must have:

1. Phase I evidence, followed by Phase II evidence, with no hidden source or
   completion assumption;
2. an independently stated terminal Challenge/Solution pair expressing the
   full filtered-class hypotheses and original affine cofactor conclusion,
   followed by a successful `scripts/verify-palomar.sh` run using the exact
   comparator, lean4export, NanoDa, Landrun, and Lean revisions;
3. the corresponding `docs/verification-results.json`, `formalization.yaml`,
   and `release-gates.yaml` committed; and
4. human review of the paper/Lean correspondence and the proof architecture.

Before tagging, verify the full commit, ancestry, clean worktree, and exact
source archive. Do not put generated `.lake` files or credentials in the
archive:

```sh
formal_commit=$(git rev-parse HEAD)
git fetch origin
git merge-base --is-ancestor "$formal_commit" origin/main
test -z "$(git status --porcelain)"
release_dir=$(mktemp -d /tmp/symplectic-stafford-release.XXXXXX)
git archive --format=tar.gz --prefix=symplectic-stafford-formal/ \
  --output="$release_dir/symplectic-stafford-formal.tar.gz" "$formal_commit"
sha256sum "$release_dir/symplectic-stafford-formal.tar.gz" \
  > "$release_dir/SHA256SUMS"
tar -tzf "$release_dir/symplectic-stafford-formal.tar.gz" >/dev/null
```

Build and inspect the companion document separately. The source `.tex` is
part of the archive; the generated PDF may be attached as a release artifact.

```sh
docs/dossier/build.sh
cp docs/dossier/symplectic-stafford-description.pdf "$release_dir/"
cp docs/dossier/symplectic-stafford-description.build-manifest.json "$release_dir/"
(cd "$release_dir" && sha256sum symplectic-stafford-description.pdf \
  symplectic-stafford-description.build-manifest.json >> SHA256SUMS)
```

## Palomar

The current `comparator.json` compares
`SymplecticStaffordChallenge.universalStatement`, which is only definitional
membership in a two-generated right set. Its local replay is checkpoint
evidence and cannot serve as the terminal submission configuration.

Before terminal submission, supply and independently audit the actual
filtered-algebra statement and its proof, then configure the comparator for
that exact declaration. Record the declaration, import closure, pinned tools
and compared source commit in the evidence file. After the repository is
public and submission is explicitly authorized, submit that selected commit
under `itpplasma/symplectic-stafford-formal`, project directory `.` (or blank),
with its audited `comparator.json` and `formalization.yaml`. Retain the returned
status page. The terminal configuration and submission remain pending.

## Signed GitHub release

Only after the evidence gate and human release decision:

```sh
release_tag='v0.1.0'
git tag -s "$release_tag" "$formal_commit" \
  -m "Symplectic Stafford formalization $release_tag"
git verify-tag "$release_tag"
git push origin "refs/tags/$release_tag"
gh release create "$release_tag" --verify-tag \
  --title "Symplectic Stafford formalization $release_tag" \
  --notes-file docs/release-notes.md \
  "$release_dir/symplectic-stafford-formal.tar.gz" \
  "$release_dir/symplectic-stafford-description.pdf" \
  "$release_dir/SHA256SUMS"
```

Do not replace an existing tag and do not bypass signing if the signing key is
unavailable. The tag identifies the exact source tree and its attached PDF.

## Zenodo

Zenodo archives GitHub releases through its GitHub integration. Once, an
authorized maintainer should sign in to Zenodo, open account settings → GitHub,
and enable `itpplasma/symplectic-stafford-formal`. The repository must be public
before it can be selected. Publishing the signed GitHub release then causes
Zenodo to archive the tagged source and issue a version DOI and a concept DOI.

Read both identifiers from the actual Zenodo record; never invent or copy a
DOI from Stafford38. In a follow-up commit, add only the issued DOI to
`CITATION.cff` and the README citation text. Keep the source archive, PDF, and
checksums together as the release receipt.

## Apache-2.0 and scope

The formal source is Apache-2.0 with `LICENSE` and `NOTICE`. The companion
paper remains a separate research artifact and is not silently bundled into
the formal package. A Zenodo deposit does not turn the current semantic
checkpoint into a proof of the unresolved higher-dimensional theorem.
