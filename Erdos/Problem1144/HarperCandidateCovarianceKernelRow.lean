import Erdos.Problem1144.HarperCandidateCovarianceKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set

namespace Erdos.Problem1144

noncomputable section

/-! Actual square-integrable rows of the angular white covariance kernel.
The estimate is uniform over arbitrary frequency subsets, so it applies to
random Euler-product screens after fixing the sign configuration. -/

/-- The literal kernel is measurable in angular frequency. -/
theorem candidate_measurable_whiteKernel (T B : ℝ) :
    Measurable (candidateCovarianceWhiteKernel T B) := by
  have hm : Measurable (fun z : ℝ × ℝ =>
      ((1 / z.2 : ℝ) : ℂ) * candidateCovariancePhase (-z.1 * z.2)) := by
    unfold candidateCovariancePhase
    fun_prop
  exact (StronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Icc T B)) hm.stronglyMeasurable).measurable

/-- A globally integrable pointwise majorant, obtained by combining the exact
nonoscillatory and inverse-gap bounds. -/
theorem candidate_whiteKernel_norm_sq_le_cauchy
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (h : ℝ) :
    ‖candidateCovarianceWhiteKernel T B h‖ ^ 2 ≤
      (Real.log (B / T) ^ 2 + 4) / (1 + (T * h) ^ 2) := by
  let k := ‖candidateCovarianceWhiteKernel T B h‖
  have hk : 0 ≤ k := norm_nonneg _
  have hlog := candidate_whiteKernel_norm_le_log hT hTB h
  have hlog0 : 0 ≤ Real.log (B / T) := hk.trans hlog
  have hsq : k ^ 2 ≤ Real.log (B / T) ^ 2 := by nlinarith
  have hosc : (T * h) ^ 2 * k ^ 2 ≤ 4 := by
    by_cases hh : h = 0
    · simp [hh]
    · have hb := candidate_whiteKernel_norm_le_inverse_gap hT hTB hh
      have hp := (le_div_iff₀ (mul_pos hT (abs_pos.mpr hh))).mp hb
      have hp0 : 0 ≤ k * (T * |h|) := mul_nonneg hk (by positivity)
      have hs : (k * (T * |h|)) ^ 2 ≤ 4 := by nlinarith
      simpa only [mul_pow, sq_abs, mul_comm (k ^ 2)] using hs
  apply (le_div_iff₀ (by positivity : 0 < 1 + (T * h) ^ 2)).mpr
  nlinarith

private theorem majorant_integrable {T : ℝ} (hT : 0 < T) (C : ℝ) :
    Integrable (fun h : ℝ => C / (1 + (T * h) ^ 2)) := by
  simpa only [div_eq_mul_inv] using
    (integrable_inv_one_add_sq.comp_mul_left' hT.ne').const_mul C

/-- Every actual kernel row has a finite square integral. -/
theorem candidate_integrable_whiteKernel_norm_sq
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) :
    Integrable (fun h => ‖candidateCovarianceWhiteKernel T B h‖ ^ 2) := by
  apply (majorant_integrable hT (Real.log (B / T) ^ 2 + 4)).mono'
    (((candidate_measurable_whiteKernel T B).norm.pow_const 2).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun h => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact candidate_whiteKernel_norm_sq_le_cauchy hT hTB h

/-- The full angular row has the required reciprocal-`T` square-mass scale. -/
theorem candidate_integral_whiteKernel_norm_sq_le
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) :
    (∫ h, ‖candidateCovarianceWhiteKernel T B h‖ ^ 2) ≤
      Real.pi * (Real.log (B / T) ^ 2 + 4) / T := by
  calc
    _ ≤ ∫ h : ℝ, (Real.log (B / T) ^ 2 + 4) / (1 + (T * h) ^ 2) :=
      integral_mono (candidate_integrable_whiteKernel_norm_sq hT hTB)
        (majorant_integrable hT _) (candidate_whiteKernel_norm_sq_le_cauchy hT hTB)
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [integral_const_mul,
        Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) T,
        integral_univ_inv_one_add_sq, abs_of_pos (inv_pos.mpr hT), smul_eq_mul]
      ring

/-- Uniform row bound on an arbitrary retained frequency set. In particular,
the set may be the literal Euler-product screen for a fixed sign realization. -/
theorem candidate_integral_whiteKernel_row_norm_sq_le
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (t : ℝ) (s : Set ℝ) :
    (∫ v in s, ‖candidateCovarianceWhiteKernel T B (t - v)‖ ^ 2) ≤
      Real.pi * (Real.log (B / T) ^ 2 + 4) / T := by
  calc
    _ ≤ ∫ v, ‖candidateCovarianceWhiteKernel T B (t - v)‖ ^ 2 :=
      setIntegral_le_integral
        ((candidate_integrable_whiteKernel_norm_sq hT hTB).comp_sub_left t)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    _ = ∫ h, ‖candidateCovarianceWhiteKernel T B h‖ ^ 2 :=
      integral_sub_left_eq_self
        (fun h : ℝ => ‖candidateCovarianceWhiteKernel T B h‖ ^ 2) volume t
    _ ≤ _ := candidate_integral_whiteKernel_norm_sq_le hT hTB

end

end Erdos.Problem1144
