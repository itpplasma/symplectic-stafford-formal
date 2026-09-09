import Mathlib.RingTheory.Noetherian.Defs
import SymplecticStafford.Filtered.ReesNoetherianCriterion
import SymplecticStafford.Filtered.ReesRing

/-!
# Boundary for the filtered module Noetherian consumer

An exhaustive constant filtration, even when it is negation-closed and hence
gives an actual algebraic Rees ring, does not by itself produce a strict
reduction certificate.  The pointwise sequence ring has a strict chain of
prefix ideals.  This rules out a module certificate for its regular module,
and therefore isolates the missing finite-generation/leading-term input.
-/

namespace SymplecticStafford.Filtered

universe u

abbrev SequenceRing := ℕ → ℤ

def constantNegFiltration : NegFiltrationData SequenceRing where
  carrier _ := Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij; simp
  exhaustive := by intro x; exact ⟨0, by simp⟩
  neg_mem := by simp

@[simp] theorem constantNegFiltration_carrier (n : ℕ) :
    (constantNegFiltration.carrier n : Set SequenceRing) = Set.univ := rfl

def sequencePrefixIdeal (n : ℕ) : Ideal SequenceRing where
  carrier := {f | ∀ i, n ≤ i → f i = 0}
  zero_mem' := by
    intro i hi
    simp
  add_mem' := by
    intro f g hf hg i hi
    simp [hf i hi, hg i hi]
  smul_mem' := by
    intro r f hf i hi
    simp [hf i hi]

theorem sequencePrefixIdeal_mono {m n : ℕ} (hmn : m ≤ n) :
    (sequencePrefixIdeal m : Submodule SequenceRing SequenceRing) ≤
      (sequencePrefixIdeal n : Submodule SequenceRing SequenceRing) := by
  intro f hf i hi
  exact hf i (hmn.trans hi)

def sequenceCoordinate (n : ℕ) : SequenceRing :=
  fun i => if i = n then 1 else 0

theorem sequenceCoordinate_mem_succ (n : ℕ) :
    sequenceCoordinate n ∈ sequencePrefixIdeal (n + 1) := by
  intro i hi
  simp only [sequenceCoordinate]
  split_ifs with h
  · omega
  · rfl

theorem sequenceCoordinate_not_mem (n : ℕ) :
    sequenceCoordinate n ∉ sequencePrefixIdeal n := by
  intro h
  have hz := h n (le_refl n)
  simp [sequenceCoordinate] at hz

theorem sequencePrefixIdeal_strict (n : ℕ) :
    (sequencePrefixIdeal n : Submodule SequenceRing SequenceRing) ≠
      (sequencePrefixIdeal (n + 1) : Submodule SequenceRing SequenceRing) := by
  intro h
  have hm : sequenceCoordinate n ∈
      (sequencePrefixIdeal n : Submodule SequenceRing SequenceRing) := by
    rw [h]
    exact sequenceCoordinate_mem_succ n
  exact sequenceCoordinate_not_mem n hm

theorem sequenceRing_not_noetherian :
    ¬ IsNoetherianRing SequenceRing := by
  intro hN
  let chain : ℕ →o Submodule SequenceRing SequenceRing :=
    { toFun := fun n =>
        (sequencePrefixIdeal n : Submodule SequenceRing SequenceRing)
      monotone' := fun m n hmn => sequencePrefixIdeal_mono hmn }
  obtain ⟨n, hn⟩ :=
    (monotone_stabilizes_iff_noetherian (R := SequenceRing)
      (M := SequenceRing)).mpr hN chain
  have heq := hn (n + 1) (Nat.le_succ n)
  change (sequencePrefixIdeal n : Submodule SequenceRing SequenceRing) =
    sequencePrefixIdeal (n + 1) at heq
  exact sequencePrefixIdeal_strict n heq

/-- The regular module over this filtered ring cannot satisfy the strict
reduction certificate: such a certificate would make the ring Noetherian. -/
theorem no_sequence_module_noetherian_certificate :
    ¬ Nonempty (ReesModuleNoetherianCertificate SequenceRing SequenceRing) := by
  intro hC
  rcases hC with ⟨C⟩
  exact sequenceRing_not_noetherian
    ((isNoetherianRing_iff).2 C.isNoetherianModule)

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.sequencePrefixIdeal_strict
#print axioms SymplecticStafford.Filtered.sequenceRing_not_noetherian
#print axioms SymplecticStafford.Filtered.no_sequence_module_noetherian_certificate
