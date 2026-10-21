module

public import SymplecticStafford.Filtered.PowerOre
public import SymplecticStafford.Filtered.ReesAlgebra

@[expose] public section

/-!
# Finite algebraic symbol/fraction normal forms

This file composes the finite Rees API with the algebraic power-Ore
certificate.  The resulting statements are deliberately finite: a finite
chart family has one common denominator power, and a finite family of raw
Rees symbols has one common filtration degree.  The numerator order is the
original-ring order throughout.

The iff theorem below needs injectivity of the chart map.  Without that
hypothesis an equality of evaluated fractions need not descend to an
equality in the original ring.  No completed or principal-symbol
localization is used.
-/

namespace SymplecticStafford.Filtered

universe u v

variable {R : Type u} [Semiring R]
variable {S : Type v} [Semiring S]

namespace PowerOreLocalizationCertificate

variable (C : PowerOreLocalizationCertificate R S)

private theorem inverse_pow_mul_denominator_pow_eq
    (n m : Nat) :
    C.inverse ^ n * (C.map C.denominator) ^ (n + m) =
      (C.map C.denominator) ^ m := by
  have hcomm : Commute C.inverse (C.map C.denominator) := by
    exact C.inverse_mul_denominator.trans C.denominator_mul_inverse.symm
  have hone : C.inverse ^ n * (C.map C.denominator) ^ n = 1 := by
    have h := hcomm.mul_pow n
    rw [C.inverse_mul_denominator] at h
    simpa using h.symm
  rw [pow_add]
  calc
    C.inverse ^ n * ((C.map C.denominator) ^ n *
        (C.map C.denominator) ^ m) =
        (C.inverse ^ n * (C.map C.denominator) ^ n) *
          (C.map C.denominator) ^ m := by
            simp only [mul_assoc]
    _ = (C.map C.denominator) ^ m := by
      rw [hone]
      simp

private theorem denominator_pow_mul_inverse_pow_eq
    (n : Nat) :
    (C.map C.denominator) ^ n * C.inverse ^ n = 1 := by
  have hcomm : Commute (C.map C.denominator) C.inverse := by
    exact C.denominator_mul_inverse.trans C.inverse_mul_denominator.symm
  have h := hcomm.mul_pow n
  rw [C.denominator_mul_inverse] at h
  simpa using h.symm

private theorem inverse_pow_mul_denominator_pow_eq'
    (n m : Nat) :
    C.inverse ^ n * (C.map C.denominator) ^ (m + n) =
      (C.map C.denominator) ^ m := by
  rw [Nat.add_comm m n]
  exact inverse_pow_mul_denominator_pow_eq C n m

/-- Raising a fraction to a larger common power preserves its value.

The new numerator is obtained by multiplying on the right in `R`; no factor
is commuted past the numerator.
-/
theorem fractionEval_raise
    (a : R) {n N : Nat} (h : n ≤ N) :
    C.map a * C.inverse ^ n =
      C.map (a * C.denominator ^ (N - n)) * C.inverse ^ N := by
  have hN : N - n + n = N := Nat.sub_add_cancel h
  have hInv : C.inverse ^ N =
      C.inverse ^ (N - n) * C.inverse ^ n := by
    rw [← pow_add, hN]
  symm
  rw [map_mul, map_pow, hInv]
  calc
    C.map a * (C.map C.denominator) ^ (N - n) *
        (C.inverse ^ (N - n) * C.inverse ^ n) =
        C.map a * ((C.map C.denominator) ^ (N - n) *
          C.inverse ^ (N - n)) * C.inverse ^ n := by
            simp only [mul_assoc]
    _ = C.map a * C.inverse ^ n := by
      rw [denominator_pow_mul_inverse_pow_eq C (N - n)]
      simp

/-- A finite family of chart elements admits one original-U denominator
power and one original-U numerator for each member.

This is stronger than applying `right_clearable` independently: the exponent
is shared by the entire finite family, which is the finite coefficient
control needed before any exact recombination in the original algebra.
-/
theorem finite_fraction_normal_form (xs : List S) :
    ∃ n : Nat, ∀ x ∈ xs, ∃ a : R,
      x = C.map a * C.inverse ^ n := by
  rcases common_right_clear_from_certificate
      C.toFilteredLocalizationCertificate xs with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro x hx
  rcases hn x hx with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  calc
    x = x * 1 := by simp
    _ = x * ((C.map C.denominator) ^ n * C.inverse ^ n) := by
      rw [denominator_pow_mul_inverse_pow_eq C n]
    _ = (x * (C.map C.denominator) ^ n) * C.inverse ^ n := by
      simp only [mul_assoc]
    _ = C.map a * C.inverse ^ n := by rw [ha]

/-- Every finite list of right-power fractions has a common denominator
exponent.  Each numerator is normalized by right multiplication in `R`.
-/
theorem finite_fraction_pair_common_exponent
    (xs : List (R × Nat)) :
    ∃ N : Nat, ∀ p ∈ xs, ∃ a : R,
      p.2 ≤ N ∧
        C.map p.1 * C.inverse ^ p.2 = C.map a * C.inverse ^ N := by
  induction xs with
  | nil =>
      refine ⟨0, ?_⟩
      simp
  | cons p ps ih =>
      rcases ih with ⟨N, hN⟩
      refine ⟨max p.2 N, ?_⟩
      intro q hq
      by_cases hqp : q = p
      · subst q
        refine ⟨p.1 * C.denominator ^ (max p.2 N - p.2), ?_, ?_⟩
        · exact Nat.le_max_left p.2 N
        · exact C.fractionEval_raise p.1 (Nat.le_max_left p.2 N)
      · have hqps : q ∈ ps := by simpa [hqp] using hq
        rcases hN q hqps with ⟨a, ha, hval⟩
        have hqN' : q.2 ≤ max p.2 N := le_trans ha (Nat.le_max_right p.2 N)
        refine ⟨a * C.denominator ^ (max p.2 N - N), hqN', ?_⟩
        calc
          C.map q.1 * C.inverse ^ q.2 = C.map a * C.inverse ^ N := hval
          _ = C.map (a * C.denominator ^ (max p.2 N - N)) *
              C.inverse ^ (max p.2 N) :=
            (C.fractionEval_raise a (Nat.le_max_right p.2 N))

/-- The ordered product of a finite list of right-power fractions is again a
right-power fraction.  The induction step uses the original-ring right-Ore
witness for the accumulated numerator; in particular, the new numerator is
`p.1 * c` in that order. -/
def fractionProduct (C : PowerOreLocalizationCertificate R S)
    (xs : List (R × Nat)) : S :=
  match xs with
  | [] => 1
  | p :: ps =>
      (C.map p.1 * C.inverse ^ p.2) * fractionProduct C ps

@[simp] theorem fractionProduct_nil : C.fractionProduct [] = 1 := rfl

@[simp] theorem fractionProduct_cons (p : R × Nat) (ps : List (R × Nat)) :
    C.fractionProduct (p :: ps) =
      (C.map p.1 * C.inverse ^ p.2) * C.fractionProduct ps := rfl

theorem finite_fraction_product_normal_form
    (xs : List (R × Nat)) :
    ∃ a : R, ∃ n : Nat,
      C.fractionProduct xs = C.map a * C.inverse ^ n := by
  induction xs with
  | nil =>
      exact ⟨1, 0, by simp⟩
  | cons p ps ih =>
      rcases ih with ⟨b, m, hproduct⟩
      rcases C.fractionEval_mul_of_ore_witness p.1 b p.2 m with
        ⟨k, c, hore, hmul⟩
      exact ⟨p.1 * c, k + m, by rw [fractionProduct_cons, hproduct, hmul]⟩

/- The reverse implication in the following equivalence is already encoded
   by the quotient relation of `fractionMk`; exposing it here gives clients a
   usable canonical-representative theorem without opening that quotient. -/
theorem fractionEval_eq_iff_fractionRel
    (hmap : Function.Injective C.map)
    {p q : R × Nat} :
    C.map p.1 * C.inverse ^ p.2 = C.map q.1 * C.inverse ^ q.2 ↔
      C.fractionRel p q := by
  constructor
  · intro h
    have hmul := congrArg
      (fun z : S => z * (C.map C.denominator) ^ (p.2 + q.2)) h
    have hmap' :
        C.map p.1 * (C.map C.denominator) ^ q.2 =
          C.map q.1 * (C.map C.denominator) ^ p.2 := by
      calc
        C.map p.1 * (C.map C.denominator) ^ q.2 =
            C.map p.1 * (C.inverse ^ p.2 *
              (C.map C.denominator) ^ (p.2 + q.2)) := by
          rw [inverse_pow_mul_denominator_pow_eq C p.2 q.2]
        _ = (C.map p.1 * C.inverse ^ p.2) *
              (C.map C.denominator) ^ (p.2 + q.2) := by
          simp only [mul_assoc]
        _ = (C.map q.1 * C.inverse ^ q.2) *
              (C.map C.denominator) ^ (p.2 + q.2) := by rw [h]
        _ = C.map q.1 * (C.map C.denominator) ^ p.2 := by
          simp only [mul_assoc]
          rw [inverse_pow_mul_denominator_pow_eq' C q.2 p.2]
    have hring :
        p.1 * C.denominator ^ q.2 = q.1 * C.denominator ^ p.2 := by
      apply hmap
      simpa only [map_mul, map_pow] using hmap'
    exact ⟨0, by simpa using hring⟩
  · intro h
    have hquot : C.fractionMk p.1 p.2 = C.fractionMk q.1 q.2 := by
      exact Quotient.sound h
    exact congrArg C.fractionEval hquot

end PowerOreLocalizationCertificate

/-! A finite Rees-symbol bound, used by the combined chart theorem below. -/

theorem finite_rees_symbol_common_bound
    (F : FiltrationData R) (xs : List (ReesTerm F)) :
    ∃ N : Nat, ∀ x ∈ xs,
      x.degree ≤ N ∧ x.value ∈ F.carrier N := by
  induction xs with
  | nil =>
      refine ⟨0, ?_⟩
      simp
  | cons x xs ih =>
      rcases ih with ⟨N, hN⟩
      refine ⟨max x.degree N, ?_⟩
      intro y hy
      by_cases hxy : y = x
      · subst y
        exact ⟨Nat.le_max_left _ _, F.monotone (Nat.le_max_left _ _) x.bounded⟩
      · have hyxs : y ∈ xs := by simpa [hxy] using hy
        rcases hN y hyxs with ⟨hydeg, hyval⟩
        exact ⟨le_trans hydeg (Nat.le_max_right _ _),
          F.monotone (Nat.le_max_right _ _) hyval⟩

/-- Finite filtered symbols can be placed at one Rees degree and their chart
images can simultaneously be written with one original-U fraction power. -/
theorem finite_rees_symbol_chart_normal_form
    (C : PowerOreLocalizationCertificate R S)
    (xs : List (ReesTerm C.sourceFiltration)) :
    ∃ (degree denominator : Nat),
      (∀ x ∈ xs, x.degree ≤ degree ∧
        ∃ p : ReesAlgebra C.sourceFiltration,
          (p : ReesPolynomial R) =
            SkewPolynomial.monomial degree x.value) ∧
      (∀ x ∈ xs, ∃ a : R,
        C.map x.value = C.map a * C.inverse ^ denominator) := by
  rcases finite_rees_symbol_common_bound C.sourceFiltration xs with
    ⟨degree, hdegree⟩
  rcases C.finite_fraction_normal_form (xs.map (fun x => C.map x.value)) with
    ⟨denominator, hdenominator⟩
  refine ⟨degree, denominator, ?_, ?_⟩
  · intro x hx
    rcases hdegree x hx with ⟨hxdeg, hxval⟩
    refine ⟨hxdeg, ?_⟩
    refine ⟨ReesAlgebra.monomial C.sourceFiltration degree x.value
      (C.sourceFiltration.monotone hxdeg x.bounded), ?_⟩
    exact ReesAlgebra.coe_monomial C.sourceFiltration degree x.value
      (C.sourceFiltration.monotone hxdeg x.bounded)
  · intro x hx
    have hmem : C.map x.value ∈ xs.map (fun y => C.map y.value) := by
      exact List.mem_map.2 ⟨x, hx, rfl⟩
    exact hdenominator (C.map x.value) hmem

end SymplecticStafford.Filtered

#print axioms SymplecticStafford.Filtered.PowerOreLocalizationCertificate.finite_fraction_normal_form
#print axioms SymplecticStafford.Filtered.PowerOreLocalizationCertificate.finite_fraction_pair_common_exponent
#print axioms SymplecticStafford.Filtered.PowerOreLocalizationCertificate.finite_fraction_product_normal_form
#print axioms SymplecticStafford.Filtered.PowerOreLocalizationCertificate.fractionEval_eq_iff_fractionRel
#print axioms SymplecticStafford.Filtered.finite_rees_symbol_chart_normal_form
