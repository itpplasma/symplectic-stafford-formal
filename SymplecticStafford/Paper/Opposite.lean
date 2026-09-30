import SymplecticStafford.Paper.Induction
import Mathlib.Algebra.Module.Equiv.Opposite

/-!
# Opposite transport (paper §7.7)

The opposite algebra `Uᵐᵒᵖ` with the same filtration satisfies the standing
hypotheses, with associated graded ring `Gᵒᵖ = G` (commutative).  Hence the
affine same-divisor theorem also holds in `Uᵐᵒᵖ`, which reads in `U` as the
left-handed identity `1 = R d + S d F`.
-/

namespace SymplecticStafford.Paper

open MulOpposite

namespace FilteredAlgebraData

variable {k U G : Type*} [Field k] [Ring U] [Algebra k U] [CommRing G] [Algebra k G]
variable {𝒜 : ℕ → Submodule k G} [GradedAlgebra 𝒜]
variable (D : FilteredAlgebraData k U G 𝒜)

/-- The filtration of `Uᵐᵒᵖ`. -/
def opF (n : ℕ) : Submodule k Uᵐᵒᵖ :=
  (D.F n).comap (opLinearEquiv k : U ≃ₗ[k] Uᵐᵒᵖ).symm.toLinearMap

lemma mem_opF {n : ℕ} {x : Uᵐᵒᵖ} : x ∈ D.opF n ↔ unop x ∈ D.F n := Iff.rfl

/-- The unop map on filtration pieces. -/
def opPiece (n : ℕ) : D.opF n →ₗ[k] D.F n :=
  (opLinearEquiv k : U ≃ₗ[k] Uᵐᵒᵖ).symm.toLinearMap.restrict fun _ hx => hx

lemma opPiece_apply {n : ℕ} (x : D.opF n) : (D.opPiece n x : U) = unop (x : Uᵐᵒᵖ) := rfl

/-- **The opposite filtered algebra** (paper §7.7). -/
def op : FilteredAlgebraData k Uᵐᵒᵖ G 𝒜 where
  F := D.opF
  mono := fun _ _ h _ hx => D.mono h hx
  exhaustive := fun u => D.exhaustive (unop u)
  zero_piece := by
    ext x
    rw [mem_opF, D.mem_F_zero_iff, LinearMap.mem_range]
    constructor
    · rintro ⟨c, hc⟩; exact ⟨c, by rw [Algebra.linearMap_apply, MulOpposite.algebraMap_apply, hc, op_unop]⟩
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← hc, Algebra.linearMap_apply, MulOpposite.algebraMap_apply, unop_op]
  finiteDimensional := fun n =>
    LinearEquiv.finiteDimensional
      (LinearEquiv.ofBijective (D.opPiece n)
        ⟨fun x y h => Subtype.ext (MulOpposite.unop_injective (congrArg Subtype.val h)),
          fun y => ⟨⟨MulOpposite.op (y : U), by simp [mem_opF]⟩, rfl⟩⟩).symm
  mul_mem := fun {i j} _ _ hu hv => by
    rw [mem_opF, unop_mul, add_comm]
    exact D.mul_mem hv hu
  gr := fun n => (D.gr n).comp (D.opPiece n)
  gr_surjective := fun n y => by
    obtain ⟨x, hx⟩ := D.gr_surjective n y
    exact ⟨⟨MulOpposite.op (x : U), by simp [mem_opF]⟩, by simpa using hx⟩
  gr_zero_eq_zero_iff := fun x => by
    rw [LinearMap.comp_apply, D.gr_zero_eq_zero_iff]
    constructor
    · intro h; exact Subtype.ext (MulOpposite.unop_injective (by simpa [opPiece_apply] using
        congrArg Subtype.val h))
    · rintro rfl; simp
  gr_succ_eq_zero_iff := fun n x => by
    rw [LinearMap.comp_apply, D.gr_succ_eq_zero_iff]; rfl
  gr_mul := fun {i j} x y => by
    simp only [LinearMap.comp_apply]
    have hx : (x : Uᵐᵒᵖ).unop ∈ D.F i := x.2
    have hy : (y : Uᵐᵒᵖ).unop ∈ D.F j := y.2
    have h1 := D.grAt_of_mem hx
    have h2 := D.grAt_of_mem hy
    have h3 := D.grAt_of_mem (D.mul_mem hy hx)
    have h4 := D.grAt_mul' (add_comm j i) hy hx
    rw [D.grAt_of_mem (show unop ((x : Uᵐᵒᵖ) * y) ∈ D.F (i + j) by
      rw [unop_mul, add_comm]; exact D.mul_mem hy hx)] at h4
    change ((D.gr (i + j) ⟨unop ((x : Uᵐᵒᵖ) * y), _⟩ : 𝒜 (i + j)) : G) =
      (D.gr i ⟨unop (x : Uᵐᵒᵖ), hx⟩ : G) * (D.gr j ⟨unop (y : Uᵐᵒᵖ), hy⟩ : G)
    rw [h4, D.grAt_of_mem hy, D.grAt_of_mem hx, mul_comm]

variable [IsDomain G] [IsNoetherianRing G] [IsSimpleRing U] [Infinite k]

/-- **The left-handed same-divisor identity** `1 = R d + S d F` in `U`,
from the affine theorem in the opposite algebra. -/
theorem targetA_left (hdim : ringKrullDim G < ⊤) (d : U) (hd : d ≠ 0) :
    ∃ F R S : U, 1 = R * d + S * d * F := by
  obtain ⟨H, R, S, h⟩ := D.op.targetA hdim (MulOpposite.op d) 1
    (by simpa using hd) one_ne_zero 0
  refine ⟨unop H, unop R, unop S, ?_⟩
  have := congrArg unop h
  simpa [unop_mul, mul_assoc] using this

end FilteredAlgebraData

end SymplecticStafford.Paper
