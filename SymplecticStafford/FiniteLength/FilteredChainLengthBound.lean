import SymplecticStafford.FiniteLength.FilteredLocalizedGradedBridge
import SymplecticStafford.FiniteLength.GradedFilteredLength
import SymplecticStafford.FiniteLength.BoundedBelowStrictnessContract
import SymplecticStafford.Filtered.StrictFiniteGradedChain

/-!
# Quantitative conditional filtered-chain bound

This is the strongest finite-length statement available from the current
Part I.5 interfaces.  Every bridge used by the conclusion is a field of
`FilteredChainLengthCertificate`: bounded-below filtered strictness, exact
associated-graded layers, nonzero adjacent factors, and transfer to an actual
localized graded chain.  The supplied `GradedFilteredExtension` records the
one-step exact length split.  The theorem therefore gives an explicit bound
`n ≤ Module.length`, with equality when the transferred chain is a full
composition chain.  No Ore, slice, or universal filtered-localization
construction is inferred.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable {L : Type w} [AddCommGroup L] [Module Rᵐᵒᵖ L]

def chainQuotient
    {F : RightModuleFiltrationData (R := R) (M := M)}
    {n : ℕ} (C : StrictFilteredChain F n) (i : Fin n) :=
  C.level i.succ ⧸ ((C.level i.castSucc).comap (C.level i.succ).subtype)

/-- All hypotheses needed to quantify a strict filtered chain after
localization.  `exactGr` and `nonzeroFactor` are retained in the certificate,
even though the length equality itself is supplied by the transferred
composition chain; this prevents those obligations being silently dropped
when a future producer constructs the certificate. -/
structure FilteredChainLengthCertificate
    (F : RightModuleFiltrationData (R := R) (M := M)) (n : ℕ) where
  transfer : FilteredChainTransfer (R := R) (M := M) (L := L) F n
  boundedBelow : NatFiltration (R := Rᵐᵒᵖ) (M := M)
  exactGr : ∀ i : Fin n,
    ExactAssociatedGraded F (transfer.source.level i.castSucc)
  nonzeroFactor : ∀ i : Fin n, Nontrivial (chainQuotient transfer.source i)

theorem strict_layer_exists
    (Q : FilteredChainLengthCertificate (R := R) (M := M) (L := L) F n)
    (i : Fin n) :
    ∃ k : ℕ, ¬ (∀ x ∈ Q.transfer.source.level i.succ,
      x ∈ Q.boundedBelow.carrier k →
        ∃ y, y ∈ Q.transfer.source.level i.castSucc ∧
          y ∈ Q.boundedBelow.carrier k ∧
          x - y ∈ previousLayer Q.boundedBelow k) := by
  classical
  have hlt : Q.transfer.source.level i.castSucc <
      Q.transfer.source.level i.succ := Q.transfer.source.strict i
  have hnot := strict_inclusion_has_strict_layer Q.boundedBelow
    (le_of_lt hlt) (ne_of_lt hlt)
  by_contra h
  push_neg at h
  exact hnot h

theorem localized_extension_isFiniteLength
    {G : Type v} [AddCommGroup G] [Module Rᵐᵒᵖ G]
    (E : GradedFilteredExtension (R := Rᵐᵒᵖ) (M := L) (G := G)) :
    IsFiniteLength Rᵐᵒᵖ L :=
  E.isFiniteLength

theorem localized_extension_length_split
    {G : Type v} [AddCommGroup G] [Module Rᵐᵒᵖ G]
    (E : GradedFilteredExtension (R := Rᵐᵒᵖ) (M := L) (G := G)) :
    Module.length Rᵐᵒᵖ L =
      Module.length Rᵐᵒᵖ E.submodule + Module.length Rᵐᵒᵖ G :=
  E.length_eq_add

/- The finite descending filtration API gives the independent local
   visibility witness used by a producer for each proper filtered submodule. -/
theorem finite_filtered_layer_exists
  (F : SymplecticStafford.Filtered.FiniteFilteredModule
      (R := Rᵐᵒᵖ) (M := M))
    (A : Submodule Rᵐᵒᵖ M) (hA : A < (⊤ : Submodule Rᵐᵒᵖ M)) :
    ∃ k : Fin F.height,
      ¬ Function.Surjective
        (SymplecticStafford.Filtered.StrictFiniteGradedChain.layerMap F A k) :=
  SymplecticStafford.Filtered.StrictFiniteGradedChain.exists_layerMap_not_surjective_of_lt_top
    F A hA

/-- Quantitative M05 endpoint.  The first conjunct is the explicit upper
bound for the strict filtered-chain length; equality follows because the
localized target is supplied as a full composition chain.  The remaining
conjuncts expose the exactness, nonzero-factor, bounded-below layer witness,
and graded extension length split consumed in this certificate. -/
theorem quantitative_length_bound
    {G : Type v} [AddCommGroup G] [Module Rᵐᵒᵖ G]
    (Q : FilteredChainLengthCertificate
      (R := R) (M := M) (L := L) F n)
    (E : GradedFilteredExtension (R := Rᵐᵒᵖ) (M := L) (G := G)) :
    (n : ℕ∞) ≤ Module.length Rᵐᵒᵖ L ∧
      Module.length Rᵐᵒᵖ L = n ∧
      IsFiniteLength Rᵐᵒᵖ L ∧
      (∀ i : Fin n, ∀ d : ℕ, Function.Exact
        ((Q.exactGr i).inclusion d) ((Q.exactGr i).projection d)) ∧
      (∀ i : Fin n, Nontrivial (chainQuotient Q.transfer.source i)) ∧
      (∀ i : Fin n, ∃ k : ℕ, ¬ (∀ x ∈ Q.transfer.source.level i.succ,
        x ∈ Q.boundedBelow.carrier k →
          ∃ y, y ∈ Q.transfer.source.level i.castSucc ∧
            y ∈ Q.boundedBelow.carrier k ∧
            x - y ∈ previousLayer Q.boundedBelow k)) ∧
      Module.length Rᵐᵒᵖ L =
        Module.length Rᵐᵒᵖ E.submodule + Module.length Rᵐᵒᵖ G := by
  have htransfer := transfer_finite_length_bound Q.transfer
  have hstrict : ∀ i : Fin n, ∃ k : ℕ, ¬ (∀ x ∈ Q.transfer.source.level i.succ,
      x ∈ Q.boundedBelow.carrier k →
        ∃ y, y ∈ Q.transfer.source.level i.castSucc ∧
          y ∈ Q.boundedBelow.carrier k ∧
          x - y ∈ previousLayer Q.boundedBelow k) :=
    fun i => strict_layer_exists Q i
  have hle : (n : ℕ∞) ≤ Module.length Rᵐᵒᵖ L := by
    rw [htransfer.2]
  refine ⟨hle, htransfer.2, htransfer.1, ?_, Q.nonzeroFactor, hstrict, ?_⟩
  · intro i d
    exact (Q.exactGr i).exact d
  · exact localized_extension_length_split E

end

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.strict_layer_exists
#print axioms SymplecticStafford.FiniteLength.localized_extension_isFiniteLength
#print axioms SymplecticStafford.FiniteLength.localized_extension_length_split
#print axioms SymplecticStafford.FiniteLength.finite_filtered_layer_exists
#print axioms SymplecticStafford.FiniteLength.quantitative_length_bound
