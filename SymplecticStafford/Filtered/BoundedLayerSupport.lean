import SymplecticStafford.Filtered.ActualClassSupport
import SymplecticStafford.Filtered.CharacteristicSupport

/-!
# Bounded layer reindexing and support independence

The finite characteristic-support proxy records actual nonzero classes in
successive subquotients.  A bounded change of filtration presentation should
therefore preserve its cardinality when it explicitly reindexes the finite
layers and identifies membership in both the selected and next layers.

`BoundedLayerReindex` is that exact certificate.  It is intentionally a
finite, concrete interface: it does not assert that an arbitrary shift has
such a reindexing, and it does not identify this proxy with the full
homogeneous spectrum.
-/

namespace SymplecticStafford.Filtered

universe u v

variable {R : Type u} {M : Type v}
variable [Ring R] [AddCommGroup M] [Module R M]

structure BoundedLayerReindex
    (F G : FiniteFilteredModule (R := R) (M := M)) where
  index : Fin F.height ≃ Fin G.height
  layer_mem_iff : ∀ (k : Fin F.height) (x : M),
    x ∈ F.carrier k.1 ↔ x ∈ G.carrier (index k).1
  next_mem_iff : ∀ (k : Fin F.height) (x : M),
    x ∈ F.carrier (k.1 + 1) ↔ x ∈ G.carrier ((index k).1 + 1)

namespace BoundedLayerReindex

variable {F G : FiniteFilteredModule (R := R) (M := M)}
variable (T : BoundedLayerReindex F G)

theorem mem_quotientSupport_iff (k : Fin F.height) :
    k ∈ F.QuotientSupport ↔ T.index k ∈ G.QuotientSupport := by
  constructor
  · rintro ⟨x, hx, hq⟩
    refine ⟨x, (T.layer_mem_iff k x).mp hx, ?_⟩
    rw [G.quotient_ne_zero_iff_not_mem]
    intro hnext
    apply (F.quotient_ne_zero_iff_not_mem x k.1).mp hq
    exact (T.next_mem_iff k x).mpr hnext
  · rintro ⟨x, hx, hq⟩
    refine ⟨x, (T.layer_mem_iff k x).mpr hx, ?_⟩
    rw [F.quotient_ne_zero_iff_not_mem]
    intro hnext
    apply (G.quotient_ne_zero_iff_not_mem x (T.index k).1).mp hq
    exact (T.next_mem_iff k x).mp hnext

theorem quotientSupport_eq_image :
    G.QuotientSupport = T.index '' F.QuotientSupport := by
  ext k
  constructor
  · intro hk
    let k' : Fin F.height := T.index.symm k
    have hk' : k' ∈ F.QuotientSupport :=
      (T.mem_quotientSupport_iff k').mpr (by simpa [k'])
    exact ⟨k', hk', by simp [k']⟩
  · rintro ⟨j, hj, rfl⟩
    exact (T.mem_quotientSupport_iff j).mp hj

def supportSubtypeEquiv (T : BoundedLayerReindex F G) :
    {k : Fin F.height // k ∈ F.QuotientSupport} ≃
      {k : Fin G.height // k ∈ G.QuotientSupport} where
  toFun k := ⟨T.index k.1, (T.mem_quotientSupport_iff k.1).mp k.2⟩
  invFun k := ⟨T.index.symm k.1, (T.mem_quotientSupport_iff
    (T.index.symm k.1)).mpr (by simpa using k.2)⟩
  left_inv k := by simp
  right_inv k := by simp

theorem quotientSupportCard_eq (T : BoundedLayerReindex F G) :
    F.QuotientSupportCard = G.QuotientSupportCard := by
  classical
  unfold FiniteFilteredModule.QuotientSupportCard
  letI := F.finite_quotientSupport.fintype
  letI := G.finite_quotientSupport.fintype
  exact Fintype.card_congr (supportSubtypeEquiv T)

theorem quotientSupport_nonempty_iff (T : BoundedLayerReindex F G) :
    F.QuotientSupport.Nonempty ↔ G.QuotientSupport.Nonempty := by
  rw [Set.nonempty_iff_ne_empty, Set.nonempty_iff_ne_empty]
  constructor
  · intro hne hG
    apply hne
    apply Set.image_eq_empty.mp
    rw [← quotientSupport_eq_image T, hG]
  · intro hne hF
    apply hne
    rw [quotientSupport_eq_image T, hF]
    simp

theorem quotientSupportDimension_eq (T : BoundedLayerReindex F G) :
    F.QuotientSupportDimension = G.QuotientSupportDimension := by
  classical
  by_cases hF : F.QuotientSupport.Nonempty
  · have hG : G.QuotientSupport.Nonempty :=
      (quotientSupport_nonempty_iff T).mp hF
    rw [F.quotientSupportDimension_eq_card hF,
      G.quotientSupportDimension_eq_card hG, quotientSupportCard_eq T]
  · have hG : ¬ G.QuotientSupport.Nonempty := by
      intro hG
      exact hF ((quotientSupport_nonempty_iff T).mpr hG)
    simp [FiniteFilteredModule.QuotientSupportDimension, hF, hG]

theorem quotientSupportDefect_eq (T : BoundedLayerReindex F G) :
    supportDimensionDefect F.QuotientSupportDimension =
      supportDimensionDefect G.QuotientSupportDimension := by
  rw [quotientSupportDimension_eq T]

end BoundedLayerReindex

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.BoundedLayerReindex.mem_quotientSupport_iff
#print axioms SymplecticStafford.Filtered.BoundedLayerReindex.quotientSupportDimension_eq
#print axioms SymplecticStafford.Filtered.BoundedLayerReindex.quotientSupportDefect_eq
