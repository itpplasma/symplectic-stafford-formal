module

public import SymplecticStafford.Filtered.ReesModule

@[expose] public section

/-!
# Degree-shifted maps of bounded filtered modules

The value quotient in `ReesModule.lean` has a checked action by one raw
bounded scalar term.  It intentionally is not an associated-graded module and
does not carry an action of the polynomial `ReesRing`.  This file adds the
next safe interface: an explicitly supplied filtered linear map of degree
shift `d` induces a map on the value quotients.  The induced map respects the
single-term quotient action, while the proof keeps the degree shift visible
on representatives.

No polynomial/ReesRing action is inferred.  In particular, the resulting
compatibility theorem has scalar type `ReesQuotient F`, not `ReesRing F`.
-/

namespace SymplecticStafford.Filtered

universe u v w

noncomputable section

variable {R : Type u} [Semiring R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

structure ShiftedFilteredLinearMap
    (F : FiltrationData R)
    (G : ModuleFiltrationData F M)
    (H : ModuleFiltrationData F N)
    (d : ℕ) where
  toFun : M → N
  map_zero' : toFun 0 = 0
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (a : R) (x : M), toFun (a • x) = a • toFun x
  filtered' : ∀ (n : ℕ) (x : M), x ∈ G.carrier n →
    toFun x ∈ H.carrier (n + d)

namespace ShiftedFilteredLinearMap

variable {F : FiltrationData R}
variable {G : ModuleFiltrationData F M} {H : ModuleFiltrationData F N}
variable {d : ℕ}

def mapTerm (φ : ShiftedFilteredLinearMap F G H d)
    (x : ReesModuleTerm G) : ReesModuleTerm H where
  degree := x.degree + d
  value := φ.toFun x.value
  bounded := φ.filtered' x.degree x.value x.bounded

@[simp] theorem mapTerm_degree (φ : ShiftedFilteredLinearMap F G H d)
    (x : ReesModuleTerm G) : (φ.mapTerm x).degree = x.degree + d := rfl

@[simp] theorem mapTerm_value (φ : ShiftedFilteredLinearMap F G H d)
    (x : ReesModuleTerm G) : (φ.mapTerm x).value = φ.toFun x.value := rfl

theorem mapTerm_valueRel (φ : ShiftedFilteredLinearMap F G H d)
    {x y : ReesModuleTerm G} (h : ReesModuleQuotient.valueRel x y) :
    ReesModuleQuotient.valueRel (φ.mapTerm x) (φ.mapTerm y) := by
  change φ.toFun x.value = φ.toFun y.value
  change x.value = y.value at h
  rw [h]

/- The quotient lift uses only equality of underlying module values. -/
def mapQuotient (φ : ShiftedFilteredLinearMap F G H d) :
    ReesModuleQuotient G → ReesModuleQuotient H :=
  Quotient.lift (fun x => ReesModuleQuotient.mk (φ.mapTerm x)) (by
    intro x y h
    exact @Quotient.sound (ReesModuleTerm H)
      (ReesModuleQuotient.valueSetoid H) (φ.mapTerm x) (φ.mapTerm y)
      (φ.mapTerm_valueRel h))

@[simp] theorem value_mapQuotient (φ : ShiftedFilteredLinearMap F G H d)
    (x : ReesModuleQuotient G) :
    ReesModuleQuotient.value (φ.mapQuotient x) =
      φ.toFun (ReesModuleQuotient.value x) := by
  refine Quotient.inductionOn x ?_
  intro x
  change ReesModuleQuotient.value (ReesModuleQuotient.mk (φ.mapTerm x)) =
    φ.toFun (ReesModuleQuotient.value (ReesModuleQuotient.mk x))
  rw [ReesModuleQuotient.value_mk, ReesModuleQuotient.value_mk]
  rfl

theorem mapQuotient_zero (φ : ShiftedFilteredLinearMap F G H d) :
    φ.mapQuotient (ReesModuleQuotient.zero (G := G)) =
      ReesModuleQuotient.zero (G := H) := by
  apply ReesModuleQuotient.eq_of_value_eq
  rw [value_mapQuotient]
  simp only [ReesModuleQuotient.zero, ReesModuleQuotient.value_mk]
  exact φ.map_zero'

theorem mapQuotient_add (φ : ShiftedFilteredLinearMap F G H d)
    (x y : ReesModuleQuotient G) :
    φ.mapQuotient (ReesModuleQuotient.add x y) =
      ReesModuleQuotient.add (φ.mapQuotient x) (φ.mapQuotient y) := by
  apply ReesModuleQuotient.eq_of_value_eq
  simp only [value_mapQuotient, ReesModuleQuotient.value_add]
  exact φ.map_add' _ _

/- The action-compatible statement is intentionally only for a raw bounded
   scalar quotient.  It does not manufacture a `ReesRing` module instance. -/
theorem mapQuotient_smul (φ : ShiftedFilteredLinearMap F G H d)
    (a : ReesQuotient F) (x : ReesModuleQuotient G) :
    φ.mapQuotient (ReesModuleQuotient.smul a x) =
      ReesModuleQuotient.smul a (φ.mapQuotient x) := by
  apply ReesModuleQuotient.eq_of_value_eq
  simp only [value_mapQuotient, ReesModuleQuotient.value_smul]
  exact φ.map_smul' (ReesQuotient.value a)
    (ReesModuleQuotient.value x)

end ShiftedFilteredLinearMap

end

end SymplecticStafford.Filtered

#print axioms
  SymplecticStafford.Filtered.ShiftedFilteredLinearMap.mapQuotient_smul
#print axioms
  SymplecticStafford.Filtered.ShiftedFilteredLinearMap.value_mapQuotient
