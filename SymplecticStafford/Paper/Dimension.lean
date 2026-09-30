import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Dimension bookkeeping for the codimension induction (paper §6)

Supports `Z(U/I) = V(gr I)` are compared through `ringKrullDim (G ⧸ J)`, which
Mathlib identifies with the Krull dimension of the zero locus of `J`.

* `ringKrullDim_quotient_add_one_le`: a larger ideal that lies in none of the
  minimal primes of `J` cuts the dimension by at least one.  This is the strict
  drop (6.10): the new support misses the generic point of every component.
* `ringKrullDim_quotient_le_max`: if every minimal prime of `J` contains `J₁`
  or `J₂`, then `dim V(J) ≤ max (dim V(J₁)) (dim V(J₂))` (the support-union
  bound (6.4) from Lemma 5.1).
* `ringKrullDim_quotient_add_one_le_of_ne_zero`: in a domain, a nonzero element
  cuts the dimension (the base case of the induction).
* `eq_top_of_ringKrullDim_quotient_eq_bot`: empty support means the unit ideal.
-/

namespace SymplecticStafford.Paper

open Order

variable {R : Type*} [CommRing R]

/-- A prime containing `J` lies in its zero locus. -/
private def toZeroLocus (J : Ideal R) (P : PrimeSpectrum R) (hP : J ≤ P.asIdeal) :
    PrimeSpectrum.zeroLocus (R := R) J :=
  ⟨P, hP⟩

/-- **Dimension drop.**  If `J ≤ J'` and `J'` is contained in no minimal prime of
`J`, then `dim (R ⧸ J') + 1 ≤ dim (R ⧸ J)`. -/
theorem ringKrullDim_quotient_add_one_le {J J' : Ideal R} (hJJ' : J ≤ J')
    (hmin : ∀ q ∈ J.minimalPrimes, ¬ J' ≤ q) :
    ringKrullDim (R ⧸ J') + 1 ≤ ringKrullDim (R ⧸ J) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  by_cases hne : Nonempty (PrimeSpectrum.zeroLocus (R := R) J')
  swap
  · rw [not_nonempty_iff] at hne
    rw [krullDim_eq_bot]
    simp
  obtain ⟨⟨P, hP⟩⟩ := hne
  haveI : Nonempty (PrimeSpectrum.zeroLocus (R := R) J) :=
    ⟨⟨P, fun x hx => hP (hJJ' hx)⟩⟩
  haveI : Nonempty (PrimeSpectrum.zeroLocus (R := R) J') := ⟨⟨P, hP⟩⟩
  rw [krullDim_eq_iSup_length, krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  have hhead : J ≤ l.head.1.asIdeal := fun x hx => l.head.2 (hJJ' hx)
  obtain ⟨q, hq, hqle⟩ := Ideal.exists_minimalPrimes_le hhead
  let q' : PrimeSpectrum.zeroLocus (R := R) J := ⟨⟨q, hq.1.1⟩, hq.1.2⟩
  let f : PrimeSpectrum.zeroLocus (R := R) J' → PrimeSpectrum.zeroLocus (R := R) J :=
    fun x => ⟨x.1, fun y hy => x.2 (hJJ' hy)⟩
  have hf : StrictMono f := fun _ _ h => h
  have hlt : q' < f l.head := by
    refine lt_of_le_of_ne hqle fun h => hmin q hq ?_
    have : q = l.head.1.asIdeal := congrArg (fun x : PrimeSpectrum R => x.asIdeal) (congrArg Subtype.val h)
    rw [this]
    exact l.head.2
  have hlt' : q' < (l.map f hf).head := hlt
  let l' := (l.map f hf).cons q' hlt'
  have hlen : l'.length = l.length + 1 := by
    simp only [l', RelSeries.cons_length]; rfl
  refine le_trans ?_ (le_iSup _ l')
  rw [hlen]; push_cast; rfl

/-- **Support-union bound.**  If each minimal prime of `J` contains `J₁` or `J₂`,
then `dim (R ⧸ J) ≤ max (dim (R ⧸ J₁)) (dim (R ⧸ J₂))`. -/
theorem ringKrullDim_quotient_le_max {J J₁ J₂ : Ideal R}
    (h : ∀ q ∈ J.minimalPrimes, J₁ ≤ q ∨ J₂ ≤ q) :
    ringKrullDim (R ⧸ J) ≤ max (ringKrullDim (R ⧸ J₁)) (ringKrullDim (R ⧸ J₂)) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, ringKrullDim_quotient]
  unfold krullDim
  refine iSup_le fun l => ?_
  have hhead : J ≤ l.head.1.asIdeal := fun x hx => l.head.2 hx
  obtain ⟨q, hq, hqle⟩ := Ideal.exists_minimalPrimes_le hhead
  have hall : ∀ i, q ≤ (l i).1.asIdeal := fun i =>
    le_trans hqle (l.strictMono.monotone (Fin.zero_le i))
  rcases h q hq with h1 | h2
  · let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) J₁) :=
      { length := l.length
        toFun := fun i => ⟨(l i).1, fun y hy => hall i (h1 hy)⟩
        step := fun i => l.step i }
    exact le_trans l'.length_le_krullDim (le_max_left _ _)
  · let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) J₂) :=
      { length := l.length
        toFun := fun i => ⟨(l i).1, fun y hy => hall i (h2 hy)⟩
        step := fun i => l.step i }
    exact le_trans l'.length_le_krullDim (le_max_right _ _)

/-- In a domain, a nonzero element of `J` cuts the dimension of `R ⧸ J`. -/
theorem ringKrullDim_quotient_add_one_le_of_ne_zero [IsDomain R] {J : Ideal R} {g : R}
    (hg : g ∈ J) (hg0 : g ≠ 0) : ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim R := by
  have hle : Ideal.span {g} ≤ J := (Ideal.span_singleton_le_iff_mem J).mpr hg
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_of_ne_zero hg0))
  gcongr
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle)

/-- Empty support: `dim (R ⧸ J) = ⊥` forces `J = ⊤`. -/
theorem eq_top_of_ringKrullDim_quotient_eq_bot {J : Ideal R}
    (h : ringKrullDim (R ⧸ J) = ⊥) : J = ⊤ := by
  by_contra hJ
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have := ringKrullDim_nonneg_of_nontrivial (R := R ⧸ J)
  rw [h] at this
  exact absurd this (by simp)

end SymplecticStafford.Paper
