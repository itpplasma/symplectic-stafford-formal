# Target A submission scope

This note describes the Palomar Challenge/Solution pair for the affine
same-divisor theorem (paper Target theorem A). It replaces the earlier
bounded finite-central division-pencil comparison described in
`pencil-submission-scope.md`.

## The compared statement

`Challenge.lean` imports Mathlib only and states
`SymplecticStaffordChallenge.AffineSameDivisorStatement`:

> Let `k` be a field of characteristic zero and `U` a simple `k`-algebra
> that is not finite-dimensional over `k`. Suppose `G` is a commutative
> domain, finitely generated as a `k`-algebra and of finite Krull dimension,
> with a grading `G = ⨁ₙ 𝒜 n`. Suppose `U` carries data
> `FilteredAlgebraData k U G 𝒜`. Then for all nonzero `d, a ∈ U` and every
> `B ∈ U` there are `H, R, S ∈ U` with `1 = d R + (B + H a) d S`.

`FilteredAlgebraData` contains:

- an exhaustive, monotone filtration `F : ℕ → Submodule k U` with
  `F 0 = k·1`, finite-dimensional pieces, and `F i · F j ⊆ F (i + j)`;
- `k`-linear maps `gr n : F n → 𝒜 n`, each surjective, with kernel `F (n-1)`
  (kernel `0` for `n = 0`), satisfying
  `gr (i+j) (x y) = gr i x · gr j y`.

The maps `gr n` induce isomorphisms `F n / F (n-1) ≃ 𝒜 n`. Multiplicativity
makes their sum a graded ring isomorphism `gr U ≃ G`. The statement therefore
encodes paper §1.1 exactly:

- `U` is simple and infinite-dimensional over an infinite field of
  characteristic zero;
- the filtration is exhaustive, separated, nonnegative and multiplicative, by
  finite-dimensional pieces, with `F₀U = k`;
- `gr U` is a commutative affine domain with `D = dim G < ∞`.

The conclusion is (1.4) with the noncommutative factor order unchanged. The
statement contains no localization, support or source-selection hypothesis.

The theorem name `universalStatement` is kept for comparator compatibility.
`comparator.json` is unchanged and permits exactly `propext`, `Quot.sound` and
`Classical.choice`.

## The proof

`Solution.lean` repeats the definitions independently and does not import the
challenge. It passes the data to `SymplecticStafford.Paper.FilteredAlgebraData`
and applies `FilteredAlgebraData.targetA`. The development under
`SymplecticStafford/Paper/` imports Mathlib only:

| File | Paper content |
| --- | --- |
| `Setting.lean` | §1.1 data, degrees, symbols, `gr I`, Artin–Rees in `U` (Lemma 2.1 lifting) |
| `RightFraction.lean` | rings of right fractions, common denominators, clearing, simplicity/domain (Z9) |
| `Localization.lean` | Z1 Ore condition, the actual `T_𝔭`, Z3 units, Nakayama, survival (Z6), finite length at minimal primes (Z8), detection (Z7(b)), nondivision (Z9) |
| `Pencil.lean` | Corollary 4.8, Proposition 4.7 |
| `DivisionPencil.lean` | Lemma 4.5 |
| `NoFiniteRank.lean` | Jacobson density, Lemma 4.2, Corollary 4.4 |
| `SourceSelection.lean` | Proposition 4.6 |
| `Test.lean` | Definition 1.1 and carried-test retention (6.8) |
| `Dimension.lean` | dimension drop (6.10), support-union bound (6.4), base, endpoint |
| `Induction.lean` | (5.2)–(5.4), Lemma 5.1, Remark 5.2, `P_h`, the successor, Target A |
| `Opposite.lean` | §7.7: the opposite algebra and `1 = R d + S d F` |
| `ConsequencesGeneration.lean` | §7.1–7.8, 7.10 |

## Proof-route differences from the manuscript

The formal proof keeps every statement. It uses the following shorter routes,
each fully proved in Lean:

1. **Pencils (4.7, 4.8).** A single chain lemma for Artinian modules over a
   `k`-algebra. Distinct bad scalars give a strictly decreasing chain of
   intersections, separated by `p(c)x` for `p = ∏(1 + λᵢX)`. No
   isotypic-block reduction is needed.
2. **Corollary 4.4.** A maximal-rank argument applies Lemma 4.5 to an
   augmented family. It replaces the `E(t)`-elimination sketch of Lemma 4.3.
3. **Proposition 4.6.** Induction uses a minimal submodule `K` with some
   `eHt T + K = V`. `Hom(V, S)` is shown to be finite-dimensional over
   `End(S)` by induction on composition length.
4. **Z1.** Proved from Artin–Rees in `U` and the commutator estimate
   `rs − sr ∈ F_{deg r + deg s − 1}`. Lemma 2.2 is not used.
5. **Z4–Z7(a) are not needed.** Survival is proved directly: if `I₁ ⊆ I₂`
   are right ideals, `I₁` is `S_𝔭`-saturated, and `σ(s)·gr I₂ ⊆ gr I₁` for
   some `s ∈ S_𝔭`, then `I₁ = I₂`. The proof uses Artin–Rees in `U`, the
   Z3 unit property and Nakayama elimination in `T_𝔭`. Finite length then
   follows by pulling chains back to saturated right ideals and mapping them
   into the Artinian ring `(G/gr I)_𝔭`. This avoids graded associated
   primes.
6. Supports and dimensions are computed over all primes of `G`,
   `δ(U/I) = dim(G/gr I)`. Localizations are taken at every prime, so no
   homogeneity argument for minimal primes is required.
7. The induction starts at `P_0` (source selection and `δ ≤ D`) instead of
   `P_1`. Lemma 5.1 holds at every prime containing `gr J`.

## Non-vacuity

`SymplecticStafford/Examples/WeylInstance.lean` instantiates the hypotheses
with the Weyl algebra `Aₙ(k)`, `char k = 0`:

- `weylFilteredAlgebraData`: the Bernstein filtration (every generator of
  weight one), with `gr Aₙ(k) ≅ k[x₁,…,xₙ,ξ₁,…,ξₙ]` graded by total degree;
- `isSimpleRing`: commutators with the newest pair act on PBW normal forms
  as `−∂/∂ξ₀` and `∂/∂x₀`, which strips that pair from a nonzero element of a
  two-sided ideal; induction on `n` ends in `A₀ = k`;
- `stafford38_universalStatement`: Target A with `B = 0`, `a = 1` proves the
  pinned `Stafford38.UniversalStatement` for every `n`.

The example is outside the compared Challenge/Solution pair and is checked by
`tests/WeylNonVacuityOracle.lean`.

## Evidence

Local results are recorded in `docs/verification.md`. The local check
compiles the full development and compares the statement with the pinned
tools: Comparator `5756749`, lean4export `15f6055`, NanoDa `68d5ca9` and
Landrun `811cfff`.

- Lean 4.33.0 compiles and exports the project.
- The comparator tool itself is built with the `v4.34.0-rc1` toolchain
  pinned by its own repository.

These are local results. They do not constitute public clean replay,
independent human review or a registration decision. Those remain release
steps in `release-runbook.md`.

## Non-claims

The proof was produced within the private research development. Its
originality and priority are not asserted here. Independent mathematical
review of the paper and of the formal statement's correspondence remains a
human release step.
