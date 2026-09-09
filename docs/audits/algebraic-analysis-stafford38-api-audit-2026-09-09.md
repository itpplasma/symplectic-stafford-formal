# AlgebraicAnalysis / Stafford38-formal API audit

Date: 9 September 2026.  This audit was run against the exact dependency
revisions in `lakefile.toml` and `lake-manifest.json`:

| dependency | consumed revision | current upstream check |
| --- | --- | --- |
| Lean | `leanprover/lean4:v4.33.0` | toolchain present |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` | manifest pin |
| AlgebraicAnalysis | `add0a80d865c88fe9cbc6901bda08a636ce188f9` (`v0.3.1`) | `origin/main` and `v0.3.1` |
| Stafford38-formal | `213ae2073030c8a897087152a616b8f8c1292df2` (`v1.1.1`) | `origin/main` and `v1.1.1` |

`git ls-remote` was used for the upstream check; both consumed revisions are
the current `main` heads.  Stafford38's documentation still mentions the
historical AlgebraicAnalysis `v0.3.0` revision in its verification table, but
its current package source and downstream manifest are compatible with this
project's newer `v0.3.1` pin.

## Reusable declarations actually available

AlgebraicAnalysis supplies the following kernel-checked, application-neutral
pieces:

* `AlgebraicAnalysis.TwoGeneratorIdentity.of_rightUnitClearing` and
  `.of_rightOreLocalization` transport the ordered identity through an
  explicitly supplied ring homomorphism or right Ore localization.
* `AlgebraicAnalysis.OreRightLocalization.rightOre_clear` gives an actual
  right denominator for every element of an actual right Ore localization.
* `AlgebraicAnalysis.MinimalPrimeFiniteLengthLocalization`
  `.localizedModule_nontrivial_and_isFiniteLength` gives the nonzero,
  finite-length canonical localization at a minimal prime of the actual
  annihilator of a finite module.
* `AlgebraicAnalysis.FilteredStrictness` and the filtered two-term page
  modules provide strict filtered quotient/page maps, kernels, cokernels and
  finite composition consumers when strictness and finiteness are supplied.
* The Ore/PBW modules provide derivation-Ore normal forms and right Hilbert
  basis results for their explicitly presented Ore extension.

The local `Dependency.AlgebraicAnalysisStafford38Bridge` reexports the first,
third, and Stafford38 right-Ore transport endpoints, and
`tests/DependencyBridgeOracle.lean` checks them independently on a field and
the actual localized regular module.  Its axiom reports contain only the
normal Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound` where
needed); no project axiom or `sorryAx` is introduced.

Stafford38-formal supplies a complete `Stafford38.universalStatement` and
`universalFixedSourceStatement` only for its presented Weyl algebra.  Its
localized differential corollaries cover polynomial localizations under
explicit `IsLocalization` hypotheses.  Its filtered/Rees and characteristic
modules expose exact Weyl-specific quotient and finite-length consumers, with
their remaining algebraization inputs named in the types.

## M01--M06 comparison

| obligation | reusable imported part | missing producer or identification |
| --- | --- | --- |
| M01 | additive filtered layers and associated classes; Weyl filtered quotient APIs | identify the actual arbitrary `U` filtration with a commutative `Spec(gr U)` algebra and its right-module action; prove support/zero detection |
| M02 | bounded Rees construction, finite homogeneous-lifting criteria, polynomial/Weyl calibrations | prove the actual quantum Rees ring is Noetherian and identify it with the paper's associated object; finite lifting is not inferred from a formal completion |
| M03 | actual Ore localization, right denominator clearing, Ore/PBW extensions | prove the selected algebraic full-symbol denominator set is Ore in the original `U`; a principal-symbol open or formal slice is not such a proof |
| M04 | finite weighted detection, strict filtered consumers, nilpotent-correction lemmas | construct faithful finite coordinates for every arbitrary good filtered module, including negative-weight behavior |
| M05 | minimal-annihilator-prime localization is nonzero and finite-length once an actual finite commutative module and prime are given | produce the actual associated module, localization/action equivalence and strict filtered-to-graded transfer at the homogeneous localization used by the paper |
| M06 | finite division-ring/matrix pencil and original-cofactor consumers | prove the division-coefficient LLD and select one multiplier in original `U` for every finite test family, with all offsets and nonzero tails |

Thus no imported declaration closes M01--M06 at the paper's universal scope.
The strongest available Stafford38 theorem cannot be instantiated with an
arbitrary simple connected filtered quantization: its carrier is a presented
Weyl algebra, and the localization/differential corollaries require their
displayed coefficient and localization structures.  The local bridge keeps
that restriction explicit rather than coercing a general `U` into a Weyl
instance.

## Consequence for phase and release status

The audit is positive evidence for dependency compatibility and reusable
conditional endpoints only.  It does not promote `PLAN.md`: Phase I remains
`partial`, Phase II remains `checkpoint-only`, and publication remains
fail-closed until the universal original-`U` producer and the downstream
M01--M11 rewiring are actually proved and independently replayed.
