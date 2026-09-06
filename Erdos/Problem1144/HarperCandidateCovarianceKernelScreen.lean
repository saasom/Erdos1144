import Erdos.Problem1144.HarperCandidateCovarianceKernelRow
import Erdos.Problem1144.HarperCandidateCovarianceScreen

open MeasureTheory Set

namespace Erdos.Problem1144

noncomputable section

/-! Kernel-row contraction with a literal Euler-product barrier. The Euler
factor is the actual prefix at a selected strong-barrier cutoff. The result
retains the full D-star event and does not assume an analytic row estimate. -/

/-- A fixed sign realization gives a measurable frequency screen. -/
theorem candidate_measurableSet_covarianceScreen_frequencies
    (start N : ℕ) (W : ℝ) (s : Finset ℕ) (ω : Problem520.Omega) :
    MeasurableSet {v : ℝ | ω ∈ candidateCovarianceDStarEvent start N v W ∩
      candidateCovarianceStrongScreenEvent start v W s} := by
  have hp : Measurable (fun v : ℝ => (v, ω)) :=
    measurable_id.prodMk measurable_const
  have hD := (candidate_measurableSet_covarianceDStar_joint start N W).preimage hp
  have hS := (candidate_measurableSet_covarianceStrongScreen_joint start W s).preimage hp
  exact hD.inter hS

private theorem density_le_barrier_sq (start N j : ℕ) (W : ℝ)
    (s : Finset ℕ) (hj : j ∈ s) (ω : Problem520.Omega) (v : ℝ)
    (hv : ω ∈ candidateCovarianceDStarEvent start N v W ∩
      candidateCovarianceStrongScreenEvent start v W s) :
    Problem520.harperEulerDensity (Problem520.harperBlockEndpoint (start + j)) ω v ≤
      (Real.log (Problem520.harperBlockEndpoint (start + j) : ℝ) / W ^ 1000) ^ 2 := by
  have hb := hv.2 j hj
  have hs := Real.sq_sqrt (Problem520.harperEulerDensity_nonneg
    (Problem520.harperBlockEndpoint (start + j)) ω v)
  have hroot := Real.sqrt_nonneg (Problem520.harperEulerDensity
    (Problem520.harperBlockEndpoint (start + j)) ω v)
  nlinarith

/-- The actual prefix Euler density times the squared kernel is integrable
on the literal D-star and strong screen, on the full frequency line. -/
theorem candidate_integrable_screened_prefix_kernel_row
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (start N j : ℕ)
    (W : ℝ) (s : Finset ℕ) (hj : j ∈ s) (ω : Problem520.Omega) (t : ℝ) :
    Integrable (fun v : ℝ =>
      Problem520.harperEulerDensity (Problem520.harperBlockEndpoint (start + j)) ω v *
        ‖candidateCovarianceWhiteKernel T B (t - v)‖ ^ 2)
      (volume.restrict {v : ℝ | ω ∈ candidateCovarianceDStarEvent start N v W ∩
        candidateCovarianceStrongScreenEvent start v W s}) := by
  let C := (Real.log (Problem520.harperBlockEndpoint (start + j) : ℝ) / W ^ 1000) ^ 2
  have hi := (((candidate_integrable_whiteKernel_norm_sq hT hTB).comp_sub_left t).const_mul C).restrict
    (s := {v : ℝ | ω ∈ candidateCovarianceDStarEvent start N v W ∩
      candidateCovarianceStrongScreenEvent start v W s})
  have hm : Measurable (fun v : ℝ =>
      Problem520.harperEulerDensity (Problem520.harperBlockEndpoint (start + j)) ω v *
        ‖candidateCovarianceWhiteKernel T B (t - v)‖ ^ 2) :=
    ((Problem520.measurable_harperEulerDensity_joint _).comp
      (measurable_id.prodMk measurable_const)).mul
      (((candidate_measurable_whiteKernel T B).comp
        (measurable_const.sub measurable_id)).norm.pow_const 2)
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (candidate_measurableSet_covarianceScreen_frequencies start N W s ω)] with v hv
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Problem520.harperEulerDensity_nonneg _ ω v) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right
    (density_le_barrier_sq start N j W s hj ω v hv) (sq_nonneg _)

/-- A selected literal strong cutoff contributes its actual squared barrier
factor to the uniform kernel-row estimate. This is the prefix contraction
needed before the residual mixed Euler moments are integrated. -/
theorem candidate_integral_screened_prefix_kernel_row_le
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (start N j : ℕ)
    (W : ℝ) (s : Finset ℕ) (hj : j ∈ s) (ω : Problem520.Omega) (t : ℝ) :
    (∫ v in {v : ℝ | ω ∈ candidateCovarianceDStarEvent start N v W ∩
        candidateCovarianceStrongScreenEvent start v W s},
      Problem520.harperEulerDensity (Problem520.harperBlockEndpoint (start + j)) ω v *
        ‖candidateCovarianceWhiteKernel T B (t - v)‖ ^ 2) ≤
      (Real.log (Problem520.harperBlockEndpoint (start + j) : ℝ) / W ^ 1000) ^ 2 *
        (Real.pi * (Real.log (B / T) ^ 2 + 4) / T) := by
  let S := {v : ℝ | ω ∈ candidateCovarianceDStarEvent start N v W ∩
    candidateCovarianceStrongScreenEvent start v W s}
  let C := (Real.log (Problem520.harperBlockEndpoint (start + j) : ℝ) / W ^ 1000) ^ 2
  have hi := (((candidate_integrable_whiteKernel_norm_sq hT hTB).comp_sub_left t).const_mul C).restrict
    (s := S)
  calc
    _ ≤ ∫ v in S, C * ‖candidateCovarianceWhiteKernel T B (t - v)‖ ^ 2 := by
      apply integral_mono_ae
        (candidate_integrable_screened_prefix_kernel_row hT hTB start N j W s hj ω t) hi
      filter_upwards [ae_restrict_mem
        (candidate_measurableSet_covarianceScreen_frequencies start N W s ω)] with v hv
      exact mul_le_mul_of_nonneg_right
        (density_le_barrier_sq start N j W s hj ω v hv) (sq_nonneg _)
    _ = C * ∫ v in S, ‖candidateCovarianceWhiteKernel T B (t - v)‖ ^ 2 := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (candidate_integral_whiteKernel_row_norm_sq_le hT hTB t S) (sq_nonneg _)

end

end Erdos.Problem1144
