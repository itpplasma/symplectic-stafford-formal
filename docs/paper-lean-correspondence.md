# Paper and Lean correspondence

The affine same-divisor theorem (Target A) and the numbered §7 consequences
have Lean proofs in `SymplecticStafford/Paper/`. The compared Challenge states
the original paper theorem. The formal route uses explicit replacements for
some written proofs; it does not certify every unused intermediate assertion.

The maintained declaration map is [paper-lean-map.json](paper-lean-map.json).
It contains 34 cards in proof order, with separate statement and proof-route
relations, exact source hashes, dependencies and omitted claims. This follows
the distinction used by the [Stafford38 correspondence
map](https://github.com/itpplasma/stafford38-formal/blob/746952ede40ac5dd22ac57201883da7ef7a42dfb/tools/paper_lean_audit/paper-lean-map.json).
The dependencies describe the mathematical route; compiler imports and kernel
axiom closure remain separate executable evidence.

## Selected mathematical source

The paper source is the [Symplectic Stafford research
repository](https://github.com/itpplasma/symplectic-stafford), frozen at
c495a2c4c702c25cdb236034273c71cf94e86476. The map fingerprints its existing
Markdown candidate, Parts I–III, banked consequences, the Zariskian closure
note, formal-route corrections and manuscript-revision instructions. Paper
anchors are literal Markdown headings at that immutable revision.

The consolidated manuscript's TeX source is absent from that repository.
Consequently this is correspondence to the available mathematical candidate
and its corrections, without PDF page or excerpt claims. The final
human-readable paper is deferred. When its source exists, use it as the
single authoritative manuscript, add its revision and hashes, and map its
numbered statements and actual passages to these declarations. Do not create
a competing independently edited paper snapshot.

## Hypotheses and conclusion

The Challenge uses a characteristic-zero field, a simple infinite-dimensional
algebra `U`, and an exhaustive nonnegative multiplicative filtration by
finite-dimensional pieces with `F₀U = k`. Its associated graded algebra `G`
is a commutative affine domain of finite Krull dimension. Surjective linear
symbol maps with exactly the lower-piece kernels and multiplicativity encode
the associated graded identification. A nonnegative filtration extends by
zero at negative indices, giving separatedness.

The conclusion is literally

```text
∀ d a ≠ 0, ∀ B, ∃ H R S, 1 = d R + (B + H a) d S.
```

Every factor belongs to the original `U`; the products retain the paper's
right-module order. Right ideals appear in Lean as submodules over `Uᵐᵒᵖ`.
There is no localization, source-selection or support hypothesis in the
Challenge. Its definitions are repeated independently in Solution; their
statement comparison belongs to the Palomar replay.

The internal theorem `FilteredAlgebraData.targetA` is stronger: it needs an
infinite field and Noetherian `G`, and does not use infinite-dimensionality
of `U`. Solution derives infinitude from characteristic zero and
Noetherianity from affine finite generation. These are reductions of the
paper assumptions, with no new premise.

## Proof route and corrections

| Paper step | Formal declarations | Relation |
| --- | --- | --- |
| Filtered data, symbols, Artin–Rees (Lemma 2.1) | `FilteredAlgebraData`, `artinRees` | Same lifting architecture |
| Full-symbol Ore localization (Z1) | `ore_condition`, `isRightFractions` | Direct Artin–Rees/commutator argument |
| Local unit and finite-length package | `unit_of_neg`, `survival`, `finiteLength` | Direct cyclic-quotient route replaces local Rees/good-filtration machinery |
| Cyclic support detection (Z7(b)) | `one_mem_extend_iff_not_le` | Exact cyclic statement needed by induction |
| No finite-rank trap (Lemma 4.2) | `density`, `not_finite_end`, `no_finite_rank_trap` | Repaired density step |
| Independent original source (Corollary 4.4) | `exists_injective_rmul`, `exists_linearIndependent_rmul` | Maximal rank replaces sketched Lemma 4.3 |
| Finite pencils (4.7–4.8) | `activated_pencil_finite`, `generator_pencil_finite` | Artinian-chain proof |
| Finite source selection (4.6) | `Test.exists_source` | Minimal-submodule proof |
| Common colon and support union (§5) | `colonJ`, `colonJ_le_Id`, `support_union` | Literal ordered certificates; union proof works at all primes |
| Two-call induction (§6) | `Ph_zero`, `Ph_succ`, `Ph_all` | Starts at index zero; both recursive calls use the smaller index |
| Original-algebra extraction | `targetA` | Empty test list at dimension plus one; lifts `1 ∈ gr I` to `1 ∈ I` |
| Opposite and §7 | `op`, `targetA_left`, generation/rank/consequence files | Automatic opposite data and the proved general Ore-domain package |

The two required written-proof repairs are already supplied in the research
repository's `paper/manuscript-revision-2026-09-30.md` §§8.1–8.2 and
`docs/formal-proof-route-2026-09-30.md`: replace the incomplete Lemma 4.3
route to Corollary 4.4 by maximal rank, and replace the insufficient matrix
algebra step in Lemma 4.2 by explicit density. Lemma 4.3 itself should be
removed from the required proof, or remain clearly unused until separately
proved. Proving its consumer by another route does not certify its sketch.

The map explicitly excludes unused general statements: Lemma 2.2, the full
associated graded identification for localized modules, Z4–Z7(a), and the
top/isotypic-block reduction of Lemma 4.1. The formal proof proves the local
facts its induction uses. It does not claim every manuscript generalization.

## Dimension convention

The paper uses `δ(0) = −1` and states its induction for `1 ≤ h ≤ D + 1`.
Lean uses `WithBot ℕ∞`, sets the zero quotient's dimension to `⊥`, and has
`⊥ + h = ⊥`. For a nonzero quotient and finite `D`, the finite dimensions
have their usual natural-number meaning. For the zero quotient, the paper's
bound `−1 ≤ D − h` and Lean's bound both hold throughout the paper's range.
Thus they give the same needed induction conclusion and extraction at
`D + 1`. Lean also proves `Ph_all h` for every natural `h`; that extension
must not be read as the unbounded integer inequality using `−1`.

Supports are computed over all primes of `G`; the induction only needs the
finite set of minimal primes. This avoids proving a separate homogeneous
minimal-prime reduction and leaves the theorem unchanged.

## Section 7 scope

The map includes individual cards for torsion cyclicity (7.1), two-generation
(7.2), prescribed tails (7.3), Ore-rank generation (7.4–7.5), stable range
(7.6), stably free freeness (7.7), two-source identities (7.8), integral
functionals (7.9), splitting (7.10–7.11), correction (7.12) and cancellation
(7.13). `ConsequencesForU.lean` derives the original algebra's Ore and
same-divisor hypotheses and exposes representative endpoints.

Ore rank is the dimension of the actual Ore localization of a right module,
represented as a left module over the opposite ring. The general theorems
sometimes need weaker assumptions than the manuscript: no right
Noetherianity beyond explicit finite-generation requirements; 7.9 only
requires the two Ore conditions; 7.12–7.13 need S38 for the opposite ring.
Right Noetherianity is retained for two-generation of unrestricted right
ideals. The banked consequence note also states broader abstract variants:
rank generation from S3 alone, and stable range from right Ore alone. The
mapped Lean generation theorem uses S38, and its stable-range/stably-free
route assumes both Ore conditions. Those broader abstractions are marked
partial; every needed hypothesis holds for the original filtered `U`.
Freeness of every projective and rank-one cancellation are outside the claim.
The single Palomar comparison is Target A; it does not automatically register
all auxiliary §7 declarations.

## Maintaining correspondence

Run `python3 scripts/check-paper-lean-map.py` locally with the private
research checkout available to the checker for the full pinned paper
fingerprint and heading-anchor check. Public CI uses the checker's
`--formal-only` mode: it validates the formal fingerprints, declaration
references and required endpoints without fetching private research sources.
The public Lean/Palomar replay needs no private paper checkout. No raw
private research bundle is part of this release. Run the ordinary project
verification and complete Palomar preflight against the frozen formal
snapshot.

These checks detect drift within their stated source boundary; semantic
correspondence still requires reading the statements, hypotheses and route
differences. An automated pass is not independent human mathematical approval
or a full PDF-to-Lean comparison.

For a source change, review affected cards and dependent conclusions before
refreshing hashes. A hash refresh alone does not approve a changed statement.
Freeze the final formal commit and retain replay evidence against that exact
revision. For a paper change, select an immutable research/manuscript commit,
review affected anchors and cards, then update the source pin and hashes.

The old [proof graph](proof-graph.yaml), [dossier](dossier/README.md) and
[8 September correspondence audit](audits/paper-formal-correspondence.md)
are historical scaffold records. They are outside the maintained Target A
map and must not be used to infer current proof gaps or a current submission
scope. Human review and actual registry status belong to the release records.
