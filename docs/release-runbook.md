# Human release runbook

This runbook records the Stafford38-style release procedure. It is a checklist,
not authorization to change repository visibility, sign tags, submit to
Palomar, or publish a Zenodo deposit. The current `release-gates.yaml` is
intentionally pending.

## Select an evidence-bearing commit

Release only a clean immutable commit for which a fresh, credential-free clone
has replayed all project checks. The selected commit must have:

1. Phase I evidence, followed by Phase II evidence, with no hidden source or
   completion assumption;
2. a successful `scripts/verify-palomar.sh` run using the exact comparator,
   lean4export, NanoDa, Landrun, and Lean revisions recorded by the verifier;
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

After the repository is public and submission is explicitly authorized, submit
the exact selected commit through the Palomar form. Use repository
`itpplasma/symplectic-stafford-formal`, project directory `.` (or blank),
`comparator.json`, `formalization.yaml`, and the compared declaration
`SymplecticStaffordChallenge.universalStatement`. Retain the returned status
page and record it in the evidence file. A passing semantic challenge is not a
passing universal theorem gate.

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
