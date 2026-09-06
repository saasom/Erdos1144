import Erdos.Problem1144.HarperCandidateCovarianceNearScheduledRate
import Erdos.Problem1144.HarperCandidateGaussianAssembly

open Filter MeasureTheory
open scoped Topology
namespace Erdos.Problem1144
noncomputable section

/-- The literal screened common near-row envelope has a vanishing Markov
budget on the rounded schedule. All analytic moment constants are supplied
by the proved Euler row estimate. -/
theorem candidate_exists_scheduledNearRow_threshold_tendsto_zero :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ β c G : ℝ,
      1 ≤ β → 0 < c → 0 < G → ∀ N : ℝ → ℕ,
      (∀ᶠ T : ℝ in atTop, (N T : ℝ) ≤ G * T) →
      Tendsto (fun T : ℝ =>
        (∫ ω, candidateEulerBandNearRowEnvelope
          (candidateCovarianceScheduleStart J T) (candidateEulerTopIndex T)
          (candidateCovarianceScheduleStrong J T) (Real.log T)
          (candidateCovarianceScheduleHeight T) T (β * T)
          (candidateCovarianceScheduleWidth T) (candidateCovarianceScheduleOrder T) (N T) ω ∂Problem520.μ) /
          (T ^ ((4 : ℝ) / 5) * (c * Real.log T ^ (-(3 : ℝ) / 5) / 2) ^
            (2 * candidateCovarianceScheduleOrder T))) atTop (𝓝 0) := by
  obtain ⟨C, D, hC, hD, J₀, hm⟩ := candidate_exists_nearRowEnvelope_moment_bound
  refine ⟨J₀, ?_⟩
  intro J hJ β c G hβ hc hG N hN
  apply squeeze_zero' (g := fun T : ℝ =>
    candidateCovarianceScheduledNearBudget C D J β T (N T) /
      (T ^ ((4 : ℝ) / 5) * (c * Real.log T ^ (-(3 : ℝ) / 5) / 2) ^
        (2 * candidateCovarianceScheduleOrder T)))
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hTp : 0 < T := by linarith
    have hq : 0 < Real.log T := Real.log_pos hT
    apply div_nonneg
    · exact integral_nonneg fun ω => candidate_nearRowEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ ω
    · positivity
  · filter_upwards [candidate_eventually_covarianceSchedule_geometry J] with T hg
    rcases hg with ⟨hT, hq, hstart, hlength, hsa, has, hstrong, hk, hh, hd, hM, hwin⟩
    have hTp : 0 < T := by linarith
    have hstartJ : J₀ ≤ candidateCovarianceScheduleStart J T := by
      rw [← hstart]; omega
    have hTB : T ≤ β * T := by nlinarith only [mul_le_mul_of_nonneg_right hβ hTp.le]
    have hwindow : (candidateCovarianceScheduleHeight T : ℝ) ≤
        candidateCovarianceHeightWindow (candidateCovarianceScheduleStart J T) / 2 := by linarith
    have hbound := hm (candidateCovarianceScheduleOrder T) hk
      (candidateCovarianceScheduleStart J T) (candidateEulerTopIndex T)
      (candidateCovarianceScheduleStrong J T) hstartJ hsa has (Real.log T) hq
      (candidateCovarianceScheduleHeight T) (Nat.cast_nonneg _) hwindow T (β * T)
      (candidateCovarianceScheduleWidth T) hTp hTB hd.le (N T)
    exact div_le_div_of_nonneg_right hbound (by positivity)
  · exact candidate_scheduledNearBudget_threshold_tendsto_zero C D hC.le J β c G hβ hc hG N hN

/-- Canonical candidate grid specialization: no row-growth hypothesis
remains. The covariance threshold is an arbitrary fixed positive multiple
of `(log T)^(-3/5)`, allowing the Fourier normalization to be inserted. -/
theorem candidate_exists_scheduledNearRow_candidateGrid_tendsto_zero :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ β c κ : ℝ,
      1 ≤ β → 0 < c → 0 < κ →
      Tendsto (fun T : ℝ =>
        (∫ ω, candidateEulerBandNearRowEnvelope
          (candidateCovarianceScheduleStart J T) (candidateEulerTopIndex T)
          (candidateCovarianceScheduleStrong J T) (Real.log T)
          (candidateCovarianceScheduleHeight T) T (β * T)
          (candidateCovarianceScheduleWidth T) (candidateCovarianceScheduleOrder T)
          (candidateScheduleM κ T) ω ∂Problem520.μ) /
          (T ^ ((4 : ℝ) / 5) * (c * Real.log T ^ (-(3 : ℝ) / 5) / 2) ^
            (2 * candidateCovarianceScheduleOrder T))) atTop (𝓝 0) := by
  obtain ⟨J₀, hJ₀⟩ := candidate_exists_scheduledNearRow_threshold_tendsto_zero
  refine ⟨J₀, ?_⟩
  intro J hJ β c κ hβ hc hκ
  exact hJ₀ J hJ β c 1 hβ hc (by norm_num) (candidateScheduleM κ)
    (by simpa only [one_mul] using candidateScheduleM_eventually_le_time hκ)

end
end Erdos.Problem1144
