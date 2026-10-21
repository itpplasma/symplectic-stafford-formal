# Symplectic Stafford research provenance

The [Symplectic Stafford research repository](https://github.com/itpplasma/symplectic-stafford)
and this [formal repository](https://github.com/itpplasma/symplectic-stafford-formal)
record the same internal proof development. The research repository's Markdown
exposition is not a separately published prior source being formalized. Its
dated chronology is retained for correspondence checking and mathematical
review. Target theorem A is proved in the formal repository; the earlier
conditional scaffolds are historical.

## Canonical ownership

| Artifact | Authority |
| --- | --- |
| Target A Lean proof, Challenge/Solution pair and verification tools | [symplectic-stafford-formal](https://github.com/itpplasma/symplectic-stafford-formal) |
| Research exposition, proof history and corrections discovered during formalization | [symplectic-stafford](https://github.com/itpplasma/symplectic-stafford), especially `docs/formal-proof-route-2026-09-30.md` |
| Final human-readable manuscript | Separate later deliverable; no separate paper repository is claimed here |

The research repository and a future manuscript repository are not Lean build
inputs. The formal proof in `SymplecticStafford/Paper/` imports Mathlib only.
AlgebraicAnalysis and [Stafford38](https://github.com/itpplasma/stafford38-formal)
are pinned dependencies of the historical scaffolds, not mathematical inputs
to Target A.

## Source and statement correspondence

The recorded research snapshot is c495a2c4c702c25cdb236034273c71cf94e86476.
The [paper/Lean correspondence](paper-lean-correspondence.md) and its
[machine-readable map](paper-lean-map.json) pin the source files and formal
declarations. The [submission scope](target-a-submission-scope.md) records the standing
hypotheses, exact noncommutative conclusion and proof-route differences.
Machine-checkable verification certifies the source snapshot named in each
report, not arbitrary later edits. Release documentation and metadata may be
added after a verified source snapshot only when the Lean sources, dependency
pins, comparator configuration and verifier scripts still match it; otherwise
replay is required.

References to “paper”, “paper proof” or “final paper” in older audit records,
proof maps, module comments and the old TeX dossier refer to the internal
exposition unless they explicitly identify an external publication. Historical
records retain their original status; the current scope and map govern the
release. The final manuscript must adopt the corrections and preserve the
mapped hypotheses and factor order before claiming exact correspondence.

## Attribution and assistance

The original proof is recorded as `type: original-proof`, `relationship:
other` in [formalization metadata](../formalization.yaml). Stafford's 1978
paper supplies historical background for the same-divisor target; it is not
the source of the new filtered-algebra proof. Stafford38 supplies useful
release and correspondence practices without supplying this proof.

Christopher Albert is the recorded human author and maintainer. AI systems
assisted mathematical research, Lean development and scoped audits under
human direction. The metadata retains model identifiers supported by the
project record. Assistance does not assign authorship of an idea.

The author authorized release preparation and Palomar submission on 21 October
2026. Independent human mathematical review remains pending. Kernel replay,
agent audits, Palomar review, journal review and publication are distinct
records; none is inferred from another. No novelty or priority claim is made.

Formal code and documentation are Apache-2.0; dependency attributions retain
their own licenses. No license for a future separate manuscript is assigned
by the formal package.
