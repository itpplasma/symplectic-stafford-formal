module

public import SymplecticStafford.Induction.TwoCallDescentProducer

@[expose] public section

/-!
# One scalar for all finite successor obstructions

The two-call successor has several independent sources of exceptional
parameters: support components, carried local tests, and an already known
exceptional set.  This file proves the finite-set arithmetic needed to choose
one central scalar outside all of them at once.

The theorem is deliberately agnostic about why each bad set is finite.  In
particular, it does not prove support geometry, a local pencil theorem, or a
universal `P_h` producer.  It only turns explicit finite exceptional-set
certificates into one parameter, preserving the original source operation in
`TwoCallDescentData`.
-/

namespace SymplecticStafford.Induction

universe u v w x y

section Generic

variable {Λ : Type u} {α : Type v} {β : Type w}

/-! A finite union of arbitrary finite exceptional sets remains finite. -/

theorem finite_exists_bad_finset
    [DecidableEq α]
    (S : Finset α) (bad : α → Λ → Prop)
    (hbad : ∀ a, a ∈ S → Set.Finite {z : Λ | bad a z}) :
    Set.Finite {z : Λ | ∃ a, a ∈ S ∧ bad a z} := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert a S ha ih =>
      have ha_finite : Set.Finite {z : Λ | bad a z} :=
        hbad a (by simp)
      have hS_finite :
          Set.Finite {z : Λ | ∃ b, b ∈ S ∧ bad b z} := by
        apply ih
        intro b hb
        exact hbad b (by simp [hb])
      have hEq :
          {z : Λ | ∃ b, b ∈ insert a S ∧ bad b z} =
            {z : Λ | bad a z} ∪ {z : Λ | ∃ b, b ∈ S ∧ bad b z} := by
        ext z
        simp [and_or_left]
      rw [hEq]
      exact ha_finite.union hS_finite

theorem finite_exists_bad_list
    (xs : List β) (bad : β → Λ → Prop)
    (hbad : ∀ b, b ∈ xs → Set.Finite {z : Λ | bad b z}) :
    Set.Finite {z : Λ | ∃ b, b ∈ xs ∧ bad b z} := by
  induction xs with
  | nil =>
      simp
  | cons a xs ih =>
      have ha_finite : Set.Finite {z : Λ | bad a z} :=
        hbad a (by simp)
      have hxs_finite :
          Set.Finite {z : Λ | ∃ b, b ∈ xs ∧ bad b z} := by
        apply ih
        intro b hb
        exact hbad b (by simp [hb])
      have hEq :
          {z : Λ | ∃ b, b ∈ a :: xs ∧ bad b z} =
            {z : Λ | bad a z} ∪ {z : Λ | ∃ b, b ∈ xs ∧ bad b z} := by
        ext z
        simp [or_and_left]
      rw [hEq]
      exact ha_finite.union hxs_finite

/-!
Choose a scalar outside a finite support-indexed family, a finite list of
test-indexed families, and one additional finite exceptional set.
-/
theorem exists_scalar_avoiding_finset_list
    [Infinite Λ] [DecidableEq α]
    (S : Finset α) (xs : List β)
    (componentBad : α → Λ → Prop)
    (testBad : β → Λ → Prop)
    (baseBad : Set Λ)
    (component_finite : ∀ a, a ∈ S → Set.Finite {z : Λ | componentBad a z})
    (test_finite : ∀ b, b ∈ xs → Set.Finite {z : Λ | testBad b z})
    (base_finite : baseBad.Finite) :
    ∃ z : Λ,
      z ∉ baseBad ∧
        (∀ a, a ∈ S → ¬ componentBad a z) ∧
        (∀ b, b ∈ xs → ¬ testBad b z) := by
  let componentSet : Set Λ :=
    {z | ∃ a, a ∈ S ∧ componentBad a z}
  let testSet : Set Λ :=
    {z | ∃ b, b ∈ xs ∧ testBad b z}
  have hcomponent : componentSet.Finite := by
    exact finite_exists_bad_finset S componentBad component_finite
  have htest : testSet.Finite := by
    exact finite_exists_bad_list xs testBad test_finite
  have hall : (componentSet ∪ testSet ∪ baseBad).Finite :=
    hcomponent.union htest |>.union base_finite
  let z : Λ := Classical.choose hall.exists_notMem
  have hz : z ∉ componentSet ∪ testSet ∪ baseBad :=
    Classical.choose_spec hall.exists_notMem
  refine ⟨z, ?_, ?_, ?_⟩
  · intro h
    exact hz (Or.inr h)
  · intro a ha hbad
    apply hz
    exact Or.inl (Or.inl ⟨a, ha, hbad⟩)
  · intro b hb hbad
    apply hz
    exact Or.inl (Or.inr ⟨b, hb, hbad⟩)

end Generic

section Descent

variable {U : Type u} [Semiring U]
variable {Λ : Type v} {κ : Type w} [Infinite Λ] [DecidableEq κ]

/-!
The direct descent specialization.  The support is the actual finite support
proxy stored by `TwoCallDescentData`; the theorem merely supplies the one
scalar required by its strict-support and retention fields.
-/
theorem TwoCallDescentData.exists_scalar_avoiding
    {P : CentralParameters U Λ} {D h : Nat}
    {defect : U → U → List (LocalTest U x y) → Int}
    {lower : StrongPh D h defect}
    {d : U} {hd : d ≠ 0} {A : AffineSource U}
    {Ω : List (LocalTest U x y)}
    {hΩ : AdmissibleTestList d Ω}
    (data : TwoCallDescentData (κ := κ) P D h defect lower d hd A Ω hΩ)
    (componentBad : κ → Λ → Prop)
    (testBad : LocalTest U x y → Λ → Prop)
    (component_finite :
      ∀ a, a ∈ data.support d (lower d hd A Ω hΩ).source Ω →
        Set.Finite {z : Λ | componentBad a z})
    (test_finite : ∀ t, t ∈ Ω → Set.Finite {z : Λ | testBad t z}) :
    ∃ z : Λ,
      z ∉ data.exceptional ∧
        (∀ a, a ∈ data.support d (lower d hd A Ω hΩ).source Ω →
          ¬ componentBad a z) ∧
        (∀ t, t ∈ Ω → ¬ testBad t z) := by
  exact exists_scalar_avoiding_finset_list
    (data.support d (lower d hd A Ω hΩ).source Ω) Ω
    componentBad testBad data.exceptional component_finite test_finite
    data.exceptional_finite

end Descent

end SymplecticStafford.Induction

#print axioms SymplecticStafford.Induction.finite_exists_bad_finset
#print axioms SymplecticStafford.Induction.finite_exists_bad_list
#print axioms SymplecticStafford.Induction.exists_scalar_avoiding_finset_list
#print axioms SymplecticStafford.Induction.TwoCallDescentData.exists_scalar_avoiding
