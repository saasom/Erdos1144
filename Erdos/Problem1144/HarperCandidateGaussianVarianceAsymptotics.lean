import Erdos.Problem1144.HarperCandidateGaussianWhiteGeometry
import Erdos.Problem1144.HarperCandidateGaussianLowerTailAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Asymptotics ProbabilityTheory
open scoped Topology

namespace Erdos.Problem1144

/-- Every fixed power of the iterated logarithm is an admissible threshold
for a polynomially large family with the proved reciprocal-square-root-log
variance floor. This is the actual scalar Gaussian thinning criterion. -/
theorem candidate_tendsto_polynomialSize_gaussianPDF_loglog_threshold
    {v γ : ℝ} (hv : 0 < v) (hγ : 0 < γ) (A : ℝ) (k : ℕ) :
    Tendsto (fun T : ℝ => T ^ γ * gaussianPDFReal 0 1
      (Real.sqrt 2 * ((A * Real.log (1 + Real.log T) ^ k) /
        Real.sqrt (v * (1 + Real.log T) ^ (-(1 : ℝ) / 2))) + 1)) atTop atTop := by
  let x : ℝ → ℝ := fun T => 1 + Real.log T
  let K : ℝ → ℝ := fun T => (A * Real.log (x T) ^ k) /
    Real.sqrt (v * x T ^ (-(1 : ℝ) / 2))
  have hx : Tendsto x atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 Real.tendsto_log_atTop
  have hf : Tendsto (fun T : ℝ => Real.log (x T) ^ (2 * k) / Real.sqrt (x T))
      atTop (nhds 0) := by
    have h := ((isLittleO_log_rpow_rpow_atTop (2 * k : ℕ)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).comp hx
    simpa only [Real.rpow_natCast, Real.sqrt_eq_rpow] using h
  have hg : Tendsto (fun T : ℝ => x T / Real.log T) atTop (nhds 1) := by
    have h := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).add_const 1
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT
    dsimp only [x, Function.comp_def]
    field_simp
  have hratio : Tendsto (fun T : ℝ => K T ^ 2 / Real.log (T ^ γ))
      atTop (nhds 0) := by
    have h := (hf.mul hg).const_mul (A ^ 2 / (v * γ))
    simp only [zero_mul, mul_zero] at h
    apply h.congr'
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℝ)] with T hlog hT
    have hxpos : 0 < x T := by dsimp only [x]; linarith
    have hvar : 0 ≤ v * x T ^ (-(1 : ℝ) / 2) :=
      mul_nonneg hv.le (Real.rpow_nonneg hxpos.le _)
    have hroot : Real.sqrt (x T) ≠ 0 := (Real.sqrt_pos.mpr hxpos).ne'
    have hinv : x T ^ (-(1 : ℝ) / 2) = (Real.sqrt (x T))⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hxpos.le]
      congr 1
      ring
    dsimp only [K]
    rw [div_pow, Real.sq_sqrt hvar, Real.log_rpow hT γ, hinv]
    have hpower : (Real.log (x T) ^ k) ^ 2 = Real.log (x T) ^ (2 * k) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [mul_pow, hpower]
    field_simp
    rw [Real.sq_sqrt hxpos.le]
  have hzero : ∀ᶠ T : ℝ in atTop, Real.log (T ^ γ) = 0 → K T ^ 2 = 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT hzero
    rw [Real.log_rpow (by linarith : 0 < T) γ] at hzero
    exact False.elim ((mul_pos hγ (Real.log_pos hT)).ne' hzero)
  have hsmall : (fun T : ℝ => K T ^ 2) =o[atTop] (fun T => Real.log (T ^ γ)) :=
    (isLittleO_iff_tendsto' hzero).mpr hratio
  exact candidate_tendsto_mul_gaussianPDFReal_atTop (tendsto_rpow_atTop hγ) hsmall

end Erdos.Problem1144
