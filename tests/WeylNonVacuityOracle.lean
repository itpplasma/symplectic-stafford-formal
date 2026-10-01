import SymplecticStafford.Examples.WeylInstance

/-!
# Non-vacuity of the Target A hypotheses

The `n`th Weyl algebra in characteristic zero, with its Bernstein filtration,
satisfies every standing hypothesis of `FilteredAlgebraData.targetA`.  Target A
therefore reproduces Stafford's Theorem 3.8 in the exact form of the pinned
`Stafford38.UniversalStatement`.
-/

open SymplecticStafford.Examples.WeylInstance

example : Stafford38.UniversalStatement := stafford38_universalStatement

/-- The general Target A identity in `A₂(ℚ)`. -/
example (d a B : Stafford38.WeylAlg ℚ 2) (hd : d ≠ 0) (ha : a ≠ 0) :
    ∃ H R S : Stafford38.WeylAlg ℚ 2, 1 = d * R + (B + H * a) * d * S :=
  weyl_targetA ℚ 2 d a hd ha B

#print axioms weylFilteredAlgebraData
#print axioms isSimpleRing
#print axioms stafford38_universalStatement
