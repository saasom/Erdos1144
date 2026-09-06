import Erdos.Problem1144.HarperCandidateCovariancePerronAngular
import Erdos.Problem1144.HarperCandidateFiniteSpectralEnergy

open MeasureTheory Set
open scoped Topology

namespace Erdos.Problem1144

/-- The critical finite Euler angular transform has its literal squared Euler
density divided by the Cauchy denominator. -/
theorem candidate_criticalEuler_norm_sq_eq_density (Y : ℕ) (ω : Omega) (τ : ℝ) :
    ‖candidateEulerAngularApprox Y 0 ω τ‖ ^ 2 =
      harperRankinEulerDensity Y 0 ω (-τ) / ((1 / 2 : ℝ) ^ 2 + τ ^ 2) := by
  rw [candidateEulerAngularApprox, norm_div, div_pow,
    harperRankinEulerDensity_eq_normSq_dirichletPolynomial _ _ _ _ (by norm_num)]
  simp only [mul_zero, zero_add, Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_I_re, Complex.mul_I_im, neg_zero, add_zero, zero_add]
  ring

/-- Exact critical finite Euler second moment, uniformly in frequency. -/
theorem candidate_integral_criticalEuler_norm_sq (Y : ℕ) (τ : ℝ) :
    (∫ ω, ‖candidateEulerAngularApprox Y 0 ω τ‖ ^ 2 ∂mu) =
      harperRankinPrimeEnergyNormalizer Y 0 / ((1 / 2 : ℝ) ^ 2 + τ ^ 2) := by
  simp_rw [candidate_criticalEuler_norm_sq_eq_density]
  rw [integral_div]
  exact congrArg (fun z : ℝ => z / ((1 / 2 : ℝ) ^ 2 + τ ^ 2))
    (candidate_integral_shifted_euler_density Y 0 (-τ))

private theorem critical_second_moment_tail_le (Y : ℕ) {H τ : ℝ}
    (hH : 0 < H) (hτ : H < |τ|) :
    (∫ ω, ‖candidateEulerAngularApprox Y 0 ω τ‖ ^ 2 ∂mu) ≤
      harperRankinPrimeEnergyNormalizer Y 0 * (1 / τ ^ 2) := by
  rw [candidate_integral_criticalEuler_norm_sq, mul_one_div]
  apply div_le_div_of_nonneg_left (harperRankinPrimeEnergyNormalizer_pos Y 0).le _
    (by nlinarith)
  exact sq_pos_of_ne_zero (by intro h; simp only [h, abs_zero] at hτ; linarith)

/-- The literal finite critical Euler spectral tail is jointly integrable. -/
theorem candidate_integrable_criticalEuler_tail_product (Y : ℕ) {H : ℝ} (hH : 0 < H) :
    Integrable (fun z : ℝ × Omega => ‖candidateEulerAngularApprox Y 0 z.2 z.1‖ ^ 2)
      ((volume.restrict {τ : ℝ | H < |τ|}).prod mu) := by
  have hf : Measurable (fun z : ℝ × Omega =>
      ‖candidateEulerAngularApprox Y 0 z.2 z.1‖ ^ 2) :=
    ((measurable_candidateEulerAngularApprox Y 0).comp measurable_swap).norm.pow_const 2
  apply (integrable_prod_iff hf.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun τ => candidate_integrable_eulerAngularApprox_sq Y 0 τ
  · apply ((candidate_inv_sq_absolute_tail hH).1.const_mul
      (harperRankinPrimeEnergyNormalizer Y 0)).mono'
      hf.norm.aestronglyMeasurable.integral_prod_right'
    filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const measurable_id.abs)] with τ hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [Real.norm_eq_abs, abs_pow, abs_norm]
    exact critical_second_moment_tail_le Y hH hτ

/-- The expected angular-frequency energy omitted above `H` is at most
`2 N_Y(0)/H`, with the exact finite Euler normalizer. -/
theorem candidate_integral_criticalEuler_tail_le (Y : ℕ) {H : ℝ} (hH : 0 < H) :
    (∫ ω, (∫ τ in {τ : ℝ | H < |τ|},
      ‖candidateEulerAngularApprox Y 0 ω τ‖ ^ 2) ∂mu) ≤
      2 * harperRankinPrimeEnergyNormalizer Y 0 / H := by
  have hi := candidate_integrable_criticalEuler_tail_product Y hH
  rw [← integral_integral_swap (f := fun τ ω =>
    ‖candidateEulerAngularApprox Y 0 ω τ‖ ^ 2) hi]
  have hb : ∀ᵐ τ ∂volume.restrict {τ : ℝ | H < |τ|},
      (∫ ω, ‖candidateEulerAngularApprox Y 0 ω τ‖ ^ 2 ∂mu) ≤
        harperRankinPrimeEnergyNormalizer Y 0 * (1 / τ ^ 2) := by
    filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const measurable_id.abs)] with τ hτ
    exact critical_second_moment_tail_le Y hH hτ
  have h := integral_mono_ae hi.integral_prod_left
    ((candidate_inv_sq_absolute_tail hH).1.const_mul (harperRankinPrimeEnergyNormalizer Y 0)) hb
  rw [integral_const_mul, (candidate_inv_sq_absolute_tail hH).2] at h
  convert h using 1 <;> ring

private theorem band_compl_eq (H : ℝ) :
    (Icc (-H) H)ᶜ = {τ : ℝ | H < |τ|} := by
  ext τ
  simp only [mem_compl_iff, mem_Icc, mem_setOf_eq, ← abs_le, not_le]

/-- Finite Euler time-truncation errors are integrable over the signs. -/
theorem candidate_integrable_mean_finiteEuler_cutoff_error (Y : ℕ) {H : ℝ} (hH : 0 < H) :
    Integrable (fun ω => ∫ x,
      ‖candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H x -
        candidateEulerLogProcess Y ω x‖ ^ 2) mu := by
  simp_rw [candidate_finiteEuler_angular_cutoff_error_eq, band_compl_eq]
  exact (candidate_integrable_criticalEuler_tail_product Y hH).integral_prod_right.const_mul _

/-- The literal finite Euler time error has expected `L²` energy at most
`N_Y(0)/(πH)`. No arithmetic or Fourier-tail estimate is assumed. -/
theorem candidate_integral_finiteEuler_cutoff_error_le (Y : ℕ) {H : ℝ} (hH : 0 < H) :
    (∫ ω, (∫ x,
      ‖candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H x -
        candidateEulerLogProcess Y ω x‖ ^ 2) ∂mu) ≤
      harperRankinPrimeEnergyNormalizer Y 0 / (Real.pi * H) := by
  simp_rw [candidate_finiteEuler_angular_cutoff_error_eq, band_compl_eq]
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (candidate_integral_criticalEuler_tail_le Y hH)
    (by positivity : 0 ≤ (2 * Real.pi)⁻¹)
  convert h using 1 <;> ring

/-- At zero shift the literal Rankin normalizer is the original critical
Euler normalizer, so its established Mertens bound applies. -/
theorem candidate_critical_rankinNormalizer_eq (Y : ℕ) :
    harperRankinPrimeEnergyNormalizer Y 0 = Problem520.primeEnergyNormalizer Y := by
  unfold harperRankinPrimeEnergyNormalizer Problem520.primeEnergyNormalizer
  apply Finset.prod_congr rfl
  intro p hp
  exact harperRankinEulerNormalizer_zero (Nat.prime_of_mem_primesBelow hp).pos

end Erdos.Problem1144
