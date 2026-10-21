module

public import SymplecticStafford.Induction.FiniteScalarAvoidance

@[expose] public section

/-!
Independent behavioral oracle for finite scalar avoidance.

The finite bad sets below are concrete singleton sets over `Nat`.  The oracle
checks that the returned parameter simultaneously avoids a base obstruction,
two component obstructions, and two carried-test obstructions.  It does not
inspect implementation details or repository state.
-/

open SymplecticStafford.Induction

theorem finite_scalar_avoidance_oracle :
    ∃ z : Nat,
      z ∉ ({5} : Set Nat) ∧
        (∀ a, a ∈ ({0, 1} : Finset Nat) → ¬ z = 100 + a) ∧
        (∀ b, b ∈ ([10, 11] : List Nat) → ¬ z = b + 200) := by
  let componentBad : Nat → Nat → Prop := fun a z => z = 100 + a
  let testBad : Nat → Nat → Prop := fun b z => z = b + 200
  have component_finite :
      ∀ a, a ∈ ({0, 1} : Finset Nat) →
        Set.Finite {z : Nat | componentBad a z} := by
    intro a ha
    exact Set.finite_singleton _
  have test_finite :
      ∀ b, b ∈ ([10, 11] : List Nat) →
        Set.Finite {z : Nat | testBad b z} := by
    intro b hb
    exact Set.finite_singleton _
  have h := exists_scalar_avoiding_finset_list
    ({0, 1} : Finset Nat) ([10, 11] : List Nat)
    componentBad testBad ({5} : Set Nat)
    component_finite test_finite (Set.finite_singleton 5)
  rcases h with ⟨z, hz, hcomponents, htests⟩
  refine ⟨z, hz, ?_, ?_⟩
  · intro a ha
    simpa [componentBad] using hcomponents a ha
  · intro b hb
    simpa [testBad] using htests b hb

#print axioms finite_scalar_avoidance_oracle
