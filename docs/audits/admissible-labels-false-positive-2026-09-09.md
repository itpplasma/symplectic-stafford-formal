# Semantic-class false positive: exact M01 source boundary

## Result

The proposition-valued `AdmissibleSymplecticClass` contract does not imply the
original-ring same-divisor certificate, even when the carrier is the
nontrivial integral domain `ℤ`.  The checked witness
`integerLabeledAdmissibleClass` assigns `True` to every historical structural
label, uses constant characteristic-dimension data equal to `2` for both
handednesses, and satisfies both B2 fields.  Nevertheless
`integer_not_originalSameDivisor` proves that the divisor `2` has no ordered
certificate

```text
1 = 2 * r + (F * 2) * s
```

for any `F r s : ℤ`: the right-hand side is even.  The theorem
`labels_do_not_imply_originalSameDivisor` packages the resulting failure of
any producer of the form
`AdmissibleSymplecticClass ℤ → OriginalSameDivisor ℤ`.

## Exact scope and repair requirement

This is a false positive of the formal semantic contract, not a
counterexample to the intended paper class.  It does not claim that `ℤ`
satisfies the intended meanings of simplicity, local finiteness, or affine
associated graded domain.  It does show that those meanings are currently
uninterpreted propositions in Lean.  Therefore M01--M04 cannot be derived
from the current class by proof search alone.  A sound universal producer
must add and prove a bridge from the labels to actual original-ring data,
including at least:

1. an exhaustive separated locally finite filtration with actual layers;
2. the degree-zero scalar/central structure and the commutative affine
   associated graded domain;
3. the Noetherian/Rees and Ore/localization certificates used by M02--M03;
4. the finite faithful weighted or equivalent source-selection certificate
   used by M04; and
5. exact recombination of every source and cofactor in the original `U`.

The existing structural and localization interfaces are consumers of these
data; this result does not fill any of them.  No phase or release gate is
promoted.

## Reproduction

```text
lake build SymplecticStafford.Filtered.AdmissibleLabelsFalsePositive
lake env lean --trust=0 tests/AdmissibleLabelsFalsePositiveOracle.lean
```

The source and independent oracle contain no `sorry`, `admit`, or custom
axiom.  Their printed kernel axiom dependencies are the repository's ordinary
`propext`, `Quot.sound`, and (for the implication using a proposition-valued
choice) `Classical.choice`.
