import SymplecticStafford.Filtered.ReesModuleActionBridge
import SymplecticStafford.Filtered.ReesModuleShift
import SymplecticStafford.Semantics.S1Consequences

/-!
# Finite algebraic Rees specialization

The value of a bounded Rees term is evaluation of its central variable at
`1`.  This file makes the finite version of that observation explicit.  A
finite family of bounded homogeneous terms is lifted to the actual bounded
Rees ring and then evaluated at `1`; shifted module terms are evaluated after
the supplied filtered map.  All conclusions are coefficientwise and use no
completion, localization, or associated-graded identification.

The last structure records the extra data needed to turn a bounded Rees
identity into an original-ring right cofactor certificate.  Its fields are
inputs: bounded coefficient witnesses and the identity at the value level.
The specialization theorem only transports those inputs to `R`; it does not
produce them from formal or completed data.
-/

namespace SymplecticStafford.Filtered

universe u v w

noncomputable section

variable {R : Type u} [Ring R]

open scoped BigOperators

namespace ReesAlgebraicSpecialization

/-! ## Finite bounded-term evaluation -/

variable (F : NegFiltrationData R)

/- The bounded Rees lift of a finite family of homogeneous terms. -/
def finiteLift {ι : Type v} (s : Finset ι)
    (x : ι → ReesTerm F.toFiltrationData) : ReesRing F :=
  ∑ i ∈ s, ReesRing.monomial F (x i).degree (x i).value (x i).bounded

@[simp] theorem finiteLift_eval {ι : Type v} (s : Finset ι)
    (x : ι → ReesTerm F.toFiltrationData) :
    ReesRing.evaluationAtOne F (finiteLift F s x) =
      ∑ i ∈ s, (x i).value := by
  unfold finiteLift
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact ReesRing.evaluationAtOne_monomial F
    (x i).degree (x i).value (x i).bounded

theorem finiteLift_mem {ι : Type v} (s : Finset ι)
    (x : ι → ReesTerm F.toFiltrationData) (i : ι) (_hi : i ∈ s) :
    (x i).value ∈ F.carrier (x i).degree :=
  (x i).bounded

/- Evaluation of a finite family of bounded terms, as an actual `R` value. -/
def finiteEvaluate {ι : Type v} (s : Finset ι)
    (x : ι → ReesTerm F.toFiltrationData) : R :=
  ReesRing.evaluationAtOne F (finiteLift F s x)

@[simp] theorem finiteEvaluate_eq_sum {ι : Type v} (s : Finset ι)
    (x : ι → ReesTerm F.toFiltrationData) :
    finiteEvaluate F s x = ∑ i ∈ s, (x i).value :=
  finiteLift_eval F s x

theorem finiteEvaluate_add {ι : Type v} (s : Finset ι)
    (x y : ι → ReesTerm F.toFiltrationData) :
    finiteEvaluate F s x + finiteEvaluate F s y =
      ∑ i ∈ s, ((x i).value + (y i).value) := by
  simp only [finiteEvaluate_eq_sum]
  exact Finset.sum_add_distrib.symm

theorem finiteEvaluate_mul_scalar {ι : Type v} (s : Finset ι)
    (a : ReesTerm F.toFiltrationData)
    (x : ι → ReesTerm F.toFiltrationData) :
    a.value * finiteEvaluate F s x =
      ∑ i ∈ s, (a.value * (x i).value) := by
  simp only [finiteEvaluate_eq_sum]
  exact Finset.mul_sum s (fun i => (x i).value) a.value

/- The induced action of a finite bounded lift on an `R`-module. -/
theorem finiteLift_smul {M : Type v} [AddCommMonoid M] [Module R M]
    {ι : Type w} (s : Finset ι)
    (x : ι → ReesTerm F.toFiltrationData) (m : M) :
    (ReesRing.evaluationAtOne F (finiteLift F s x)) • m =
      ∑ i ∈ s, (x i).value • m := by
  rw [finiteLift_eval]
  exact Finset.sum_smul

/-! ## Shifted module terms -/

variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]
variable {G : ModuleFiltrationData F.toFiltrationData M}
variable {H : ModuleFiltrationData F.toFiltrationData N}

/- Finite evaluation after a supplied degree-shifted filtered map. -/
def finiteShiftedEvaluate
    {d : ℕ} {ι : Type u}
    (φ : ShiftedFilteredLinearMap F.toFiltrationData G H d)
    (s : Finset ι) (x : ι → ReesModuleTerm G) : N :=
  ∑ i ∈ s, (φ.mapTerm (x i)).value

theorem finiteShiftedEvaluate_eq_sum
    {d : ℕ} {ι : Type u}
    (φ : ShiftedFilteredLinearMap F.toFiltrationData G H d)
    (s : Finset ι) (x : ι → ReesModuleTerm G) :
    finiteShiftedEvaluate F φ s x =
      ∑ i ∈ s, φ.toFun (x i).value := by
  unfold finiteShiftedEvaluate
  apply Finset.sum_congr rfl
  intro i hi
  exact φ.mapTerm_value (x i)

theorem finiteShiftedEvaluate_add
    {d : ℕ} {ι : Type u}
    (φ : ShiftedFilteredLinearMap F.toFiltrationData G H d)
    (s : Finset ι) (x y : ι → ReesModuleTerm G) :
    finiteShiftedEvaluate F φ s (fun i => ReesModuleTerm.add (x i) (y i)) =
      finiteShiftedEvaluate F φ s x + finiteShiftedEvaluate F φ s y := by
  rw [finiteShiftedEvaluate_eq_sum, finiteShiftedEvaluate_eq_sum,
    finiteShiftedEvaluate_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact φ.map_add' _ _

theorem finiteShiftedEvaluate_smul
    {d : ℕ} {ι : Type u}
    (φ : ShiftedFilteredLinearMap F.toFiltrationData G H d)
    (a : ReesTerm F.toFiltrationData) (s : Finset ι)
    (x : ι → ReesModuleTerm G) :
    finiteShiftedEvaluate F φ s
        (fun i => ReesModuleTerm.smul a (x i)) =
      a.value • finiteShiftedEvaluate F φ s x := by
  rw [finiteShiftedEvaluate_eq_sum, finiteShiftedEvaluate_eq_sum]
  calc
    (∑ i ∈ s, φ.toFun (ReesModuleTerm.smul a (x i)).value) =
        ∑ i ∈ s, a.value • φ.toFun (x i).value := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [ReesModuleTerm.smul] using
        φ.map_smul' a.value (x i).value
    _ = a.value • ∑ i ∈ s, φ.toFun (x i).value := by
      exact Finset.smul_sum.symm

/- The same scalar/action compatibility at the actual bounded Rees-ring
   level.  The scalar acts through the explicitly supplied evaluation ring
   homomorphism; no filtered Rees-module instance is inferred. -/
theorem shiftedMap_preserves_evaluation_action
    {d : ℕ}
    (φ : ShiftedFilteredLinearMap F.toFiltrationData G H d)
    (c : ReesRing F) (x : M) :
    φ.toFun (ReesRing.evaluationAtOne F c • x) =
      ReesRing.evaluationAtOne F c • φ.toFun x := by
  exact φ.map_smul' (ReesRing.evaluationAtOne F c) x

theorem finiteShiftedEvaluate_reindex_invariant
    {d : ℕ} {ι : Type u}
    (φ : ShiftedFilteredLinearMap F.toFiltrationData G H d)
    (s : Finset ι) (x : ι → ReesModuleTerm G)
    (n : ι → ℕ) (hn : ∀ i, (x i).degree ≤ n i) :
    finiteShiftedEvaluate F φ s
        (fun i => ReesModuleTerm.reindex (x i) (hn i)) =
      finiteShiftedEvaluate F φ s x := by
  unfold finiteShiftedEvaluate
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-! ## Original-ring membership and cofactor transport -/

/-
Bounded coefficient data for one ordered right-ideal identity.  Every
cofactor is an actual bounded term, and `identity` is supplied in the value
ring.  Keeping this as a structure makes the algebraization boundary
explicit: completion or formal specialization cannot fill these fields.
-/
structure BoundedCofactorData (d f : ReesTerm F.toFiltrationData) where
  right₁ : ReesTerm F.toFiltrationData
  right₂ : ReesTerm F.toFiltrationData
  identity : (1 : R) =
    d.value * right₁.value + (f.value * d.value) * right₂.value

theorem BoundedCofactorData.original_membership
    {d f : ReesTerm F.toFiltrationData}
    (c : BoundedCofactorData F d f) :
    (1 : R) ∈ SymplecticStafford.twoGeneratedRightIdeal d.value f.value := by
  exact ⟨c.right₁.value, c.right₂.value, c.identity⟩

def BoundedCofactorData.toCertificate
    {d f : ReesTerm F.toFiltrationData}
    (c : BoundedCofactorData F d f) :
    SymplecticStafford.RightCertificate (R := R) d.value f.value 1 :=
  ⟨c.right₁.value, c.right₂.value, c.identity⟩

theorem BoundedCofactorData.cofactors_are_original
    {d f : ReesTerm F.toFiltrationData}
    (c : BoundedCofactorData F d f) :
    c.toCertificate.right₁ = c.right₁.value ∧
      c.toCertificate.right₂ = c.right₂.value :=
  ⟨rfl, rfl⟩

theorem BoundedCofactorData.certificate_identity
    {d f : ReesTerm F.toFiltrationData}
    (c : BoundedCofactorData F d f) :
    (1 : R) = d.value * c.toCertificate.right₁ +
      (f.value * d.value) * c.toCertificate.right₂ :=
  c.identity

end ReesAlgebraicSpecialization

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.ReesAlgebraicSpecialization.finiteLift_eval
#print axioms
  SymplecticStafford.Filtered.ReesAlgebraicSpecialization.finiteShiftedEvaluate_smul
#print axioms
  SymplecticStafford.Filtered.ReesAlgebraicSpecialization.BoundedCofactorData.original_membership
