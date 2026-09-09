import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Length
import SymplecticStafford.Filtered.RingFiltrationBridge
import SymplecticStafford.FiniteLength.FilteredMinimalPrimeBridge

/-!
# Conditional filtered/localized associated-graded bridge

This file is a deliberately disjoint Part I.5 interface.  It records the
data which a filtered quantum chart has to provide before a graded
minimal-support argument can be transferred back to the actual right module.
The associated layers and the induced filtrations below are algebraic
objects; localization equivalences, exactness, strictness, and survival at a
prime are explicit hypotheses.  In particular this file does not construct a
quantum slice, an Ore localization, or a universal source.
-/

namespace SymplecticStafford.FiniteLength

universe u v w

section RightFilteredModules

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- A bounded-below-indexed filtration of a right `R`-module. -/
structure RightModuleFiltrationData where
  carrier : ℕ → Submodule Rᵐᵒᵖ M
  mono : Monotone carrier
  exhaustive : ∀ x : M, ∃ n, x ∈ carrier n
  bottom : carrier 0 = ⊥

namespace RightModuleFiltrationData

variable (F : RightModuleFiltrationData (R := R) (M := M))

def predecessor (n : ℕ) : Submodule Rᵐᵒᵖ M :=
  if n = 0 then ⊥ else F.carrier (n - 1)

theorem predecessor_le (n : ℕ) : F.predecessor n ≤ F.carrier n := by
  by_cases hn : n = 0
  · simp [predecessor, hn]
  · rw [predecessor, if_neg hn]
    exact F.mono (Nat.sub_le n 1)

def layerSubmodule (n : ℕ) : Submodule Rᵐᵒᵖ (F.carrier n) :=
  F.predecessor n |>.comap (F.carrier n).subtype

abbrev associatedLayer (n : ℕ) := F.carrier n ⧸ F.layerSubmodule n

def associatedClass (n : ℕ) (x : M) (hx : x ∈ F.carrier n) :
    F.associatedLayer n :=
  Submodule.Quotient.mk ⟨x, hx⟩

theorem associatedClass_eq_zero_iff (n : ℕ) (x : M)
    (hx : x ∈ F.carrier n) :
    F.associatedClass n x hx = 0 ↔ x ∈ F.predecessor n := by
  rw [associatedClass, Submodule.Quotient.mk_eq_zero]
  rfl

theorem exists_associatedClass_ne_zero_of_ne_zero {x : M} (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ hnx : x ∈ F.carrier n,
      F.associatedClass n x hnx ≠ 0 := by
  classical
  let hex : ∃ k : ℕ, x ∈ F.carrier k := F.exhaustive x
  let n : ℕ := Nat.find hex
  have hxn : x ∈ F.carrier n := Nat.find_spec hex
  have hmin : ∀ k < n, x ∉ F.carrier k := by
    intro k hkn hk
    exact (not_lt_of_ge (Nat.find_min' hex hk)) hkn
  refine ⟨n, hxn, ?_⟩
  intro hzero
  have hpred : x ∈ F.predecessor n :=
    (F.associatedClass_eq_zero_iff n x hxn).mp hzero
  by_cases hn0 : n = 0
  · have hpred0 : x ∈ (⊥ : Submodule Rᵐᵒᵖ M) := by
      rw [hn0] at hpred
      simpa [predecessor] using hpred
    exact hx (by simpa using hpred0)
  · have hlt : n - 1 < n := Nat.sub_lt (Nat.zero_lt_of_ne_zero hn0) zero_lt_one
    exact hmin (n - 1) hlt (by simpa [predecessor, hn0] using hpred)

/- The induced filtration on a submodule, with the actual subtype carrier. -/
def inducedSubmodule (N : Submodule Rᵐᵒᵖ M) :
    RightModuleFiltrationData (R := R) (M := N) where
  carrier n := (F.carrier n).comap N.subtype
  mono := by
    intro i j hij x hx
    exact F.mono hij hx
  exhaustive := by
    intro x
    obtain ⟨n, hn⟩ := F.exhaustive (x : M)
    exact ⟨n, hn⟩
  bottom := by
    ext x
    simp [F.bottom]

/- The induced filtration on an actual submodule quotient. -/
def inducedQuotient (N : Submodule Rᵐᵒᵖ M) :
    RightModuleFiltrationData (R := R) (M := M ⧸ N) where
  carrier n := (F.carrier n).map N.mkQ
  mono := by
    intro i j hij
    exact Submodule.map_mono (F.mono hij)
  exhaustive := by
    intro x
    obtain ⟨y, rfl⟩ := N.mkQ_surjective x
    obtain ⟨n, hn⟩ := F.exhaustive y
    exact ⟨n, (Submodule.mem_map.mpr ⟨y, hn, rfl⟩)⟩
  bottom := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      have hy0 : y = 0 := by simpa [F.bottom] using hy
      simp [hy0]
    · intro hx
      have : x = 0 := by simpa using hx
      subst x
      exact Submodule.zero_mem _

theorem nonzero_quotient_has_nonzero_associatedClass
    (N : Submodule Rᵐᵒᵖ M) {x : M ⧸ N} (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ hnx : x ∈ (inducedQuotient F N).carrier n,
      (inducedQuotient F N).associatedClass n x hnx ≠ 0 := by
  exact (inducedQuotient F N).exists_associatedClass_ne_zero_of_ne_zero hx

end RightModuleFiltrationData

end RightFilteredModules

section AssociatedGradedEquivalences

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable {N : Type w} [AddCommGroup N] [Module Rᵐᵒᵖ N]

/-- Degreewise additive equivalences of the ring associated layers before and
after a supplied filtered localization.  The coefficient/localization map
and multiplication compatibility are intentionally external obligations. -/
structure RingAssociatedGradedLocalization
    (F₀ F₁ : SymplecticStafford.Filtered.RingFiltrationData (R := R)) where
  layerEquiv : ∀ n : ℕ,
    SymplecticStafford.Filtered.RingFiltrationData.associatedLayer F₀ n ≃+
      SymplecticStafford.Filtered.RingFiltrationData.associatedLayer F₁ n
  map_compatible : Prop
  multiplication_compatible : Prop

/-- Degreewise linear equivalences of right-module associated layers. -/
structure ModuleAssociatedGradedLocalization
    (F₀ : RightModuleFiltrationData (R := R) (M := M))
    (F₁ : RightModuleFiltrationData (R := R) (M := N)) where
  layerEquiv : ∀ n : ℕ,
    F₀.associatedLayer n ≃ₗ[Rᵐᵒᵖ] F₁.associatedLayer n
  scalar_action_compatible : Prop

/-- The complete filtered/localized graded identification contract. -/
structure FilteredLocalizedGradedEquivalence
    (F₀ F₁ : SymplecticStafford.Filtered.RingFiltrationData (R := R))
    (G₀ : RightModuleFiltrationData (R := R) (M := M))
    (G₁ : RightModuleFiltrationData (R := R) (M := N)) where
  ring : RingAssociatedGradedLocalization F₀ F₁
  module : ModuleAssociatedGradedLocalization G₀ G₁
  ring_module_action_compatible : Prop

end AssociatedGradedEquivalences

section ExactAssociatedGraded

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- Exactness of the associated-graded short sequence for an induced
submodule and quotient.  The maps are supplied because proving that they are
well-defined is part of the actual strict filtered/Rees theorem. -/
structure ExactAssociatedGraded
    (F : RightModuleFiltrationData (R := R) (M := M))
    (N : Submodule Rᵐᵒᵖ M) where
  inclusion : ∀ n : ℕ,
    (F.inducedSubmodule N).associatedLayer n →ₗ[Rᵐᵒᵖ] F.associatedLayer n
  projection : ∀ n : ℕ,
    F.associatedLayer n →ₗ[Rᵐᵒᵖ]
      (F.inducedQuotient N).associatedLayer n
  exact : ∀ n : ℕ,
    Function.Exact (inclusion n) (projection n)

theorem exact_at
    {F : RightModuleFiltrationData (R := R) (M := M)}
    {N : Submodule Rᵐᵒᵖ M}
    (E : ExactAssociatedGraded F N) (n : ℕ) :
    Function.Exact (E.inclusion n) (E.projection n) := E.exact n

end ExactAssociatedGraded

section AtPrimeWitness

variable {A : Type u} [CommRing A]
variable {G : Type v} [AddCommGroup G] [Module A G]

/-- A homogeneous associated-graded class which is known to survive in the
actual `LocalizedModule` at `AtPrime`.  `degree` is the homogeneous degree;
the survival assertion is the nonvanishing input needed by the support lane.
-/
structure HomogeneousAtPrimeWitness (p : Ideal A) [p.IsPrime]
    (gradedLayer : ℕ → Set G) where
  degree : ℕ
  value : G
  homogeneous : value ∈ gradedLayer degree
  nonzero : value ≠ 0
  survives : (LocalizedModule.mkLinearMap p.primeCompl G) value ≠ 0

theorem HomogeneousAtPrimeWitness.survives_atPrime
    {p : Ideal A} [p.IsPrime]
    {gradedLayer : ℕ → Set G}
    (w : HomogeneousAtPrimeWitness (A := A) (G := G) p gradedLayer) :
    (LocalizedModule.mkLinearMap p.primeCompl G) w.value ≠ 0 := w.survives

end AtPrimeWitness

section ChainTransfer

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable {L : Type w} [AddCommGroup L] [Module Rᵐᵒᵖ L]

/-- A strict chain in the filtered module. -/
structure StrictFilteredChain
    (F : RightModuleFiltrationData (R := R) (M := M)) (n : ℕ) where
  level : Fin (n + 1) → Submodule Rᵐᵒᵖ M
  head : level 0 = ⊥
  last : level (Fin.last n) = ⊤
  contained : ∀ i : Fin (n + 1), level i ≤ F.carrier (n + 1)
  strict : ∀ i : Fin n, level i.castSucc < level i.succ

/-- The target chain after filtered-to-localized-graded transfer.  `CovBy`
is retained so Mathlib's exact composition-length theorem applies. -/
structure StrictLocalizedGradedChain (n : ℕ) where
  level : Fin (n + 1) → Submodule Rᵐᵒᵖ L
  head : level 0 = ⊥
  last : level (Fin.last n) = ⊤
  step : ∀ i : Fin n, CovBy (level i.castSucc) (level i.succ)

namespace StrictLocalizedGradedChain

variable (C : StrictLocalizedGradedChain (R := R) (L := L) n)

def compositionSeries : CompositionSeries (Submodule Rᵐᵒᵖ L) :=
  { length := n
    toFun := C.level
    step := C.step }

theorem finiteLength (C : StrictLocalizedGradedChain (R := R) (L := L) n) :
    IsFiniteLength Rᵐᵒᵖ L := by
  apply isFiniteLength_of_exists_compositionSeries
  exact ⟨C.compositionSeries, C.head, C.last⟩

theorem length_eq (C : StrictLocalizedGradedChain (R := R) (L := L) n) :
    Module.length Rᵐᵒᵖ L = n := by
  symm
  exact Module.length_compositionSeries C.compositionSeries C.head C.last

end StrictLocalizedGradedChain

/-- A supplied transfer sends a strict filtered chain to a strict localized
graded chain.  Its `strict_survival` field is the exact missing strictness
theorem; it cannot be inferred from an additive layer equivalence alone. -/
structure FilteredChainTransfer
    (F : RightModuleFiltrationData (R := R) (M := M)) (n : ℕ) where
  source : StrictFilteredChain F n
  target : StrictLocalizedGradedChain (R := R) (L := L) n
  strict_survival : ∀ i : Fin n,
    source.level i.castSucc < source.level i.succ →
      target.level i.castSucc < target.level i.succ

theorem transfer_strict_chain
    (T : FilteredChainTransfer (R := R) (M := M) (L := L) F n) :
    ∀ i : Fin n, T.target.level i.castSucc < T.target.level i.succ := by
  intro i
  exact T.strict_survival i (T.source.strict i)

theorem transfer_finite_length_bound
    (T : FilteredChainTransfer (R := R) (M := M) (L := L) F n) :
    IsFiniteLength Rᵐᵒᵖ L ∧ Module.length Rᵐᵒᵖ L = n := by
  exact ⟨T.target.finiteLength, T.target.length_eq⟩

end ChainTransfer

end SymplecticStafford.FiniteLength

#print axioms SymplecticStafford.FiniteLength.RightModuleFiltrationData.exists_associatedClass_ne_zero_of_ne_zero
#print axioms SymplecticStafford.FiniteLength.exact_at
#print axioms SymplecticStafford.FiniteLength.HomogeneousAtPrimeWitness.survives_atPrime
#print axioms SymplecticStafford.FiniteLength.transfer_strict_chain
#print axioms SymplecticStafford.FiniteLength.transfer_finite_length_bound
