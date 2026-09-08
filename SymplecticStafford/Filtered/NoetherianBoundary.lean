import Mathlib.RingTheory.Noetherian.Defs
import SymplecticStafford.Filtered.Localization

/-!
# The exact M02 boundary exposed by the raw filtration contract

`FiltrationData` records exhaustive multiplicative degree bounds, but it does
not record Noetherianity of the underlying ring.  This file gives a concrete
kernel-checked witness: the pointwise semiring of sequences `ℕ → ℕ` admits the
constant exhaustive filtration while its prefix ideals form a strict
ascending chain.  Therefore no theorem deriving Rees Noetherianity from
`FiltrationData` alone can be sound.

This is a boundary result, not a counterexample to the paper's filtered
domain class: the sequence semiring is neither a domain nor simple.  A full
M02 theorem must add (and prove for the intended class) a Noetherian Rees
input, rather than silently treating the raw bounded Rees subsemiring as
Noetherian.
-/

namespace SymplecticStafford.Filtered

universe u

section FunctionSemiring

abbrev SequenceSemiring := ℕ → ℕ

/-- The constant filtration satisfies every field of the raw filtration API. -/
def constantFiltration : FiltrationData SequenceSemiring where
  carrier _ := Set.univ
  zero_mem := by simp
  one_mem := by simp
  add_mem := by simp
  mul_mem := by simp
  monotone := by intro i j hij x hx; trivial
  exhaustive := by intro x; exact ⟨0, trivial⟩

@[simp] theorem constantFiltration_carrier (n : ℕ) :
    (constantFiltration.carrier n : Set SequenceSemiring) = Set.univ := rfl

theorem constantFiltration_degreeAtMost (n : ℕ) (x : SequenceSemiring) :
    HasDegreeAtMost constantFiltration n x := by
  trivial

/-- Functions supported in the first `n` coordinates. -/
def prefixIdeal (n : ℕ) : Ideal SequenceSemiring where
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

theorem prefixIdeal_mono {m n : ℕ} (hmn : m ≤ n) :
    (prefixIdeal m : Submodule SequenceSemiring SequenceSemiring) ≤
      (prefixIdeal n : Submodule SequenceSemiring SequenceSemiring) := by
  intro f hf i hi
  exact hf i (hmn.trans hi)

def coordinate (n : ℕ) : SequenceSemiring := fun i => if i = n then 1 else 0

theorem coordinate_mem_succ (n : ℕ) : coordinate n ∈ prefixIdeal (n + 1) := by
  intro i hi
  simp only [coordinate]
  split_ifs with h
  · omega
  · rfl

theorem coordinate_not_mem (n : ℕ) : coordinate n ∉ prefixIdeal n := by
  intro h
  have hz := h n (le_refl n)
  simp [coordinate] at hz

theorem prefixIdeal_strict (n : ℕ) :
    (prefixIdeal n : Submodule SequenceSemiring SequenceSemiring) ≠
      (prefixIdeal (n + 1) : Submodule SequenceSemiring SequenceSemiring) := by
  intro h
  have hm : coordinate n ∈
      (prefixIdeal n : Submodule SequenceSemiring SequenceSemiring) := by
    rw [h]
    exact coordinate_mem_succ n
  exact coordinate_not_mem n hm

theorem prefixChain_not_noetherian :
    ¬ IsNoetherianRing SequenceSemiring := by
  intro hN
  let chain : ℕ →o Submodule SequenceSemiring SequenceSemiring :=
    { toFun := fun n => (prefixIdeal n : Submodule SequenceSemiring SequenceSemiring)
      monotone' := fun m n hmn => prefixIdeal_mono hmn }
  obtain ⟨n, hn⟩ :=
    (monotone_stabilizes_iff_noetherian (R := SequenceSemiring)
      (M := SequenceSemiring)).mpr hN chain
  have heq := hn (n + 1) (Nat.le_succ n)
  change (prefixIdeal n : Submodule SequenceSemiring SequenceSemiring) =
    prefixIdeal (n + 1) at heq
  exact prefixIdeal_strict n heq

end FunctionSemiring

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.constantFiltration_degreeAtMost
#print axioms SymplecticStafford.Filtered.prefixIdeal_strict
#print axioms SymplecticStafford.Filtered.prefixChain_not_noetherian
