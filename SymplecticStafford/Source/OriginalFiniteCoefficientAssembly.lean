module

public import SymplecticStafford.Source.FiniteTestFamilyAssembly
public import SymplecticStafford.Source.OriginalFiniteCoefficientSource

@[expose] public section

/-!
# Divisor-indexed assembly of finite original-coefficient sources

`OriginalFiniteCoefficientSource` is the one-divisor package.  This file
performs only the next composition: a common explicit coefficient algebra and
divisor-indexed finite test families are paired with one supplied source
package for each nonzero divisor.  The resulting object exposes a literal
`DivisorIndexedAssembly`, while retaining the selected multiplier, source,
all test assertions, coefficient membership, and both original-ring
cofactors.

No source package is manufactured here.  The field `selected` is the
conditional producer input, so finite local tests, source selection, and exact
recombination remain visible.  In particular this module does not assert a
universal M06 producer.
-/

namespace SymplecticStafford.Source

universe u v w x

variable {U : Type u} [DivisionRing U]
variable {K : Type v} [Field K] [Infinite K]

structure OriginalFiniteCoefficientAssembly
    {LocalizationData : Type w} {CyclicModuleData : Type x}
    (A : FiniteCoefficientAlgebra U K)
    (background affineTail : U → U)
    (tests : U → List (OriginalLocalTest U LocalizationData CyclicModuleData))
    (directions : U → List U) where
  background_nonzero : ∀ ⦃d : U⦄, d ≠ 0 → background d ≠ 0
  affineTail_nonzero : ∀ ⦃d : U⦄, d ≠ 0 → affineTail d ≠ 0
  background_mem : ∀ d, background d ∈ A.carrier
  affineTail_mem : ∀ d, affineTail d ∈ A.carrier
  directions_mem : ∀ d h, h ∈ directions d → h ∈ A.carrier
  selected : ∀ ⦃d : U⦄, d ≠ 0 →
    Nonempty (OriginalFiniteCoefficientSource A d (background d)
      (affineTail d) (tests d) (directions d))

namespace OriginalFiniteCoefficientAssembly

variable {LocalizationData : Type w} {CyclicModuleData : Type x}
variable {A : FiniteCoefficientAlgebra U K}
variable {background affineTail : U → U}
variable {tests : U → List (OriginalLocalTest U LocalizationData CyclicModuleData)}
variable {directions : U → List U}

noncomputable def selectedSource
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) :
    OriginalFiniteCoefficientSource A d (background d) (affineTail d)
      (tests d) (directions d) :=
  Classical.choice (P.selected hd)

theorem selected_source_eq
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) :
    (P.selectedSource hd).source = background d +
      (P.selectedSource hd).multiplier * affineTail d :=
  (P.selectedSource hd).source_eq

theorem selected_source_nonzero
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) :
    (P.selectedSource hd).source ≠ 0 :=
  (P.selectedSource hd).source_nonzero

theorem selected_source_mem
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) :
    (P.selectedSource hd).source ∈ A.carrier :=
  (P.selectedSource hd).source_mem

theorem selected_multiplier_mem
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) :
    (P.selectedSource hd).multiplier ∈ A.carrier :=
  (P.selectedSource hd).multiplier_mem

theorem selected_test_pass
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) {t : OriginalLocalTest U LocalizationData CyclicModuleData}
    (ht : t ∈ tests d) :
    t.Passes (P.selectedSource hd).source :=
  (P.selectedSource hd).passes t ht

theorem selected_test_admissible
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) {t : OriginalLocalTest U LocalizationData CyclicModuleData}
    (ht : t ∈ tests d) :
    t.Admissible d :=
  (P.selectedSource hd).admissible t ht

theorem selected_test_rightTail_nonzero
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) {t : OriginalLocalTest U LocalizationData CyclicModuleData}
    (ht : t ∈ tests d) :
    t.rightTail ≠ 0 :=
  (P.selectedSource hd).rightTail_nonzero t ht

theorem selected_coefficients_length
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) :
    (P.selectedSource hd).coefficients.length = (directions d).length :=
  (P.selectedSource hd).coefficients_length

theorem selected_coefficient_mem
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) {z : K}
    (hz : z ∈ (P.selectedSource hd).coefficients) :
    A.embedding z ∈ A.carrier :=
  (P.selectedSource hd).coefficient_mem z hz

theorem selected_direction_mem
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) {h : U}
    (hh : h ∈ directions d) :
    h ∈ A.carrier :=
  (P.selectedSource hd).directions_mem h hh

theorem selected_cofactor₁_mem
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) :
    (P.selectedSource hd).assembly.right₁ ∈ A.carrier :=
  (P.selectedSource hd).cofactor₁_mem

theorem selected_cofactor₂_mem
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) :
    (P.selectedSource hd).assembly.right₂ ∈ A.carrier :=
  (P.selectedSource hd).cofactor₂_mem

noncomputable def toDivisorIndexedAssembly
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions) :
    DivisorIndexedAssembly U where
  source := fun {d} hd => (P.selectedSource hd).source
  assemble := fun {d} hd => (P.selectedSource hd).assembly

theorem same_divisor
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions) :
    SymplecticStafford.SameDivisorS1 (R := U) :=
  DivisorIndexedAssembly.sameDivisor (P.toDivisorIndexedAssembly)

theorem selected_exact_recombination
    (P : OriginalFiniteCoefficientAssembly A background affineTail tests directions)
    {d : U} (hd : d ≠ 0) :
    (1 : U) = d * (P.selectedSource hd).assembly.right₁ +
      ((P.selectedSource hd).source * d) *
        (P.selectedSource hd).assembly.right₂ :=
  (P.selectedSource hd).assembly.identity

end OriginalFiniteCoefficientAssembly

/- A small constructor keeps the source-selection theorem and this assembly
   wrapper separate.  It is useful when a caller has already proved the
   actual finite-direction source theorem for every divisor. -/
noncomputable def OriginalFiniteCoefficientAssembly.of_selected
    {LocalizationData : Type w} {CyclicModuleData : Type x}
    (A : FiniteCoefficientAlgebra U K)
    (background affineTail : U → U)
    (tests : U → List (OriginalLocalTest U LocalizationData CyclicModuleData))
    (directions : U → List U)
    (background_nonzero : ∀ ⦃d : U⦄, d ≠ 0 → background d ≠ 0)
    (affineTail_nonzero : ∀ ⦃d : U⦄, d ≠ 0 → affineTail d ≠ 0)
    (background_mem : ∀ d, background d ∈ A.carrier)
    (affineTail_mem : ∀ d, affineTail d ∈ A.carrier)
    (directions_mem : ∀ d h, h ∈ directions d → h ∈ A.carrier)
    (selected : ∀ ⦃d : U⦄, d ≠ 0 →
      Nonempty (OriginalFiniteCoefficientSource A d (background d)
        (affineTail d) (tests d) (directions d))) :
    OriginalFiniteCoefficientAssembly A background affineTail tests directions :=
  { background_nonzero := background_nonzero
    affineTail_nonzero := affineTail_nonzero
    background_mem := background_mem
    affineTail_mem := affineTail_mem
    directions_mem := directions_mem
    selected := selected }

end SymplecticStafford.Source

#print axioms
  SymplecticStafford.Source.OriginalFiniteCoefficientAssembly.toDivisorIndexedAssembly
#print axioms
  SymplecticStafford.Source.OriginalFiniteCoefficientAssembly.same_divisor
#print axioms
  SymplecticStafford.Source.OriginalFiniteCoefficientAssembly.selected_exact_recombination
