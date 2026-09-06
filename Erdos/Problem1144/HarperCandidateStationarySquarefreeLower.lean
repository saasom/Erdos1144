import Erdos.Problem1144.HarperCandidateGaussianWhiteGridLower
import Erdos.Problem1144.HarperCandidateWhiteCrossingProbability
import Erdos.Problem1144.HarperCandidateStationaryWhiteComparison
import Erdos.Problem1144.HarperCandidateStationaryThreshold
import Erdos.Problem1144.HarperCandidateScheduleWhiteTimeLogs

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos.Problem1144

/-- The actual outer selector has a fixed positive squarefree-white
crossing mass at the exact threshold demanded by the stationary bridge.
The observation time changes to T/W; the coordinates and selector are kept. -/
theorem candidate_exists_stationary_squarefree_selected_lower :
    ∃ p : ℝ, 0 < p ∧ ∀ α β κ ρ C : ℝ,
      1 < α → α < β → β < 4 / 3 → 0 < κ → 0 < ρ → ρ ≤ 1 → 0 < C →
      ∀ (s : Finset ℕ) (η : s → Bool) (K : ℝ), 0 ≤ K →
      ∀ᶠ T : ℝ in atTop,
      ∀ F : Omega → Fin (candidateScheduleM κ T) → ℝ,
      (∀ i, Measurable fun ω => F ω i) → ∀ b : ℝ,
      p ≤ ∫ ω, candidateComparisonWhiteCrossing true
        (fun i : Fin (candidateScheduleM κ T) =>
          α * candidateScheduleWhiteTime κ T + i * (2 * Real.pi))
        (candidateScheduleWhiteTime κ T) (candidateRetainedIndices F b ρ)
        (candidateStationaryWhiteTransferThreshold C κ β T K) ω
        ∂candidateCylinderLaw s η := by
  obtain ⟨p, hp, hwhite⟩ := candidate_exists_squarefreeWhite_linear_grid_crossing
  refine ⟨p, hp, ?_⟩
  intro α β κ ρ C hα hαβ hβ hκ hρ hρ1 hC s η K hK
  have hβ0 : 0 < β := (by linarith : 0 < α).trans hαβ
  obtain ⟨A, hA, hthreshold⟩ :=
    candidate_eventually_stationary_white_threshold_le_loglog_power hC hκ hβ0 hK
  have hVt := candidateScheduleWhiteTime_tendsto hκ
  have hlower := hVt.eventually
    (hwhite α β hα hαβ.le hβ s η (A * 2 ^ 8) (by positivity) 8)
  filter_upwards [hlower, hthreshold,
    candidateScheduleWhiteTime_eventually_log_scale_comparison hκ,
    candidateScheduleM_eventually_le_whiteTime hκ,
    candidateSchedule_translated_grid_mem_whiteTime_window hκ hαβ,
    candidateSchedule_retained_card_ge_whiteTime_rpow hκ hρ hρ1,
    hVt.eventually_gt_atTop 1, eventually_ge_atTop (1 : ℝ)]
    with T hlow hthreshold hlogs hM hgrid hcard hV hT
  intro F hF b
  let V := candidateScheduleWhiteTime κ T
  let u := fun i : Fin (candidateScheduleM κ T) => α * V + i * (2 * Real.pi)
  let selector := candidateRetainedIndices F b ρ
  have hs : ∀ i, MeasurableSet {ω | i ∈ selector ω} :=
    measurableSet_mem_candidateRetainedIndices F hF b ρ
  have hmass := hlow (candidateScheduleM κ T) hM (α * V) hgrid selector hs
    (hcard F b)
  have hlogT : 0 ≤ Real.log (1 + Real.log T) :=
    Real.log_nonneg (by linarith [Real.log_nonneg hT])
  have hbound : candidateStationaryWhiteTransferThreshold C κ β T K ≤
      (A * 2 ^ 8) * Real.log (1 + Real.log V) ^ 8 := by
    apply hthreshold.trans
    calc
      _ ≤ A * (2 * Real.log (1 + Real.log V)) ^ 8 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogT hlogs.1 8) hA.le
      _ = _ := by rw [mul_pow]; ring
  have hm := candidate_integral_comparisonWhiteCrossing_antitone
    (candidateCylinderLaw s η) true u (by dsimp only [V]; linarith : 0 < V)
    selector hs hbound
  exact hmass.trans hm

end Erdos.Problem1144
