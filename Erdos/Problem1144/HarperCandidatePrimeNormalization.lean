import Erdos.Problem1144.HarperCandidatePrimeBins
import Erdos.Problem1144.HarperCandidateTranslationPrimeCoefficients

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-- Relative bin-mass control gives a squared error for coupling the two
normal increments with the same standard normal. -/
theorem candidate_sqrt_mass_difference_sq_le {m d r : ℝ}
    (hm : 0 ≤ m) (hd : 0 < d) (hr : |m / d - 1| ≤ r) :
    (Real.sqrt m - Real.sqrt d) ^ 2 ≤ d * r ^ 2 := by
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hr
  have hm2 := Real.sq_sqrt hm
  have hd2 := Real.sq_sqrt hd.le
  have hden : 0 < Real.sqrt m + Real.sqrt d :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr hd)
  have hprod : (Real.sqrt m - Real.sqrt d) * (Real.sqrt m + Real.sqrt d) = m - d := by
    nlinarith
  have he : m - d = d * (m / d - 1) := by field_simp
  have hab : |m - d| ≤ d * r := by
    rw [he, abs_mul, abs_of_pos hd]
    exact mul_le_mul_of_nonneg_left hr hd.le
  have hs : |Real.sqrt m - Real.sqrt d| ≤ Real.sqrt d * r := by
    apply (mul_le_mul_iff_left₀ hden).mp
    rw [← abs_of_pos hden, ← abs_mul, hprod]
    calc
      _ ≤ d * r := hab
      _ ≤ (Real.sqrt d * r) * |Real.sqrt m + Real.sqrt d| := by
        rw [abs_of_pos hden]
        nlinarith [mul_nonneg (Real.sqrt_nonneg m) (mul_nonneg (Real.sqrt_nonneg d) hr0)]
  have hs2 := pow_le_pow_left₀ (abs_nonneg _) hs 2
  simpa only [sq_abs, mul_pow, hd2] using hs2

/-- The literal endpoint coefficient has the uniform second-moment bound
needed for rescaling the Gaussian bin increments. -/
theorem candidate_integral_logCoefficient_sq_le {T y u L : ℝ}
    (hT : 0 < T) (hTy : T ≤ y) (hL : 0 ≤ L) (hu : u ≤ L) :
    (∫ ω, (harperCandidateLogProcess ω u / Real.sqrt y) ^ 2 ∂mu) ≤ (1 + L) / T := by
  have hy : 0 < y := hT.trans_le hTy
  simp_rw [div_pow, integral_div, Real.sq_sqrt hy.le]
  have h := candidateLogSecondMoment_le_of_le hL hu
  exact div_le_div₀ (by positivity) h hT hTy

/-- An almost-unit relative prime mass is strictly positive, so its
normalization produces exactly the desired nondegenerate bin increment. -/
theorem candidate_prime_bin_mass_pos_of_relative_error {m d r : ℝ}
    (hd : 0 < d) (hr : r < 1) (hm : |m / d - 1| ≤ r) : 0 < m := by
  have hl := (abs_le.mp hm).1
  have hp : 0 < m / d := by linarith
  exact (div_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2]) |>.1

/-- Total variance loss from normalizing prime-bin masses. The complete
process, real bin endpoints, and inverse-square-root factors are literal;
only the quantitative mass error is supplied by the PNT theorem. -/
theorem candidate_sum_prime_bin_normalization_variance_le
    {T d r t L : ℝ} {n : ℕ} (mass : ℕ → ℝ)
    (hT : 0 < T) (hd : 0 < d) (hr : r < 1) (hL : 0 ≤ L) (ht : t - T ≤ L)
    (hmass : ∀ j ∈ Finset.range n, |mass j / d - 1| ≤ r) :
    (∑ j ∈ Finset.range n, (Real.sqrt (mass j) - Real.sqrt d) ^ 2 *
      (∫ ω, (harperCandidateLogProcess ω (t - (T + ((j : ℝ) + 1) * d)) /
        Real.sqrt (T + ((j : ℝ) + 1) * d)) ^ 2 ∂mu)) ≤
      ((n : ℝ) * d) * r ^ 2 * ((1 + L) / T) := by
  have hpoint (j : ℕ) (hj : j ∈ Finset.range n) :
      (Real.sqrt (mass j) - Real.sqrt d) ^ 2 *
        (∫ ω, (harperCandidateLogProcess ω (t - (T + ((j : ℝ) + 1) * d)) /
          Real.sqrt (T + ((j : ℝ) + 1) * d)) ^ 2 ∂mu) ≤
        d * r ^ 2 * ((1 + L) / T) := by
    have hm := candidate_sqrt_mass_difference_sq_le
      (candidate_prime_bin_mass_pos_of_relative_error hd hr (hmass j hj)).le hd (hmass j hj)
    have hjd : 0 ≤ ((j : ℝ) + 1) * d := by positivity
    have hc := candidate_integral_logCoefficient_sq_le hT
      (show T ≤ T + ((j : ℝ) + 1) * d by linarith) hL
      (show t - (T + ((j : ℝ) + 1) * d) ≤ L by linarith)
    exact mul_le_mul hm hc (integral_nonneg fun _ => sq_nonneg _) (by positivity)
  calc
    _ ≤ ∑ _j ∈ Finset.range n, d * r ^ 2 * ((1 + L) / T) := Finset.sum_le_sum hpoint
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end Erdos.Problem1144
