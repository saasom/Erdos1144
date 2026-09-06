import Erdos.Problem1144.HarperCandidateCovarianceRetainedVarianceLower
import Erdos.Problem1144.HarperCandidateCovarianceScheduledDeletionDecay
import Erdos.Problem1144.HarperCandidateCovarianceScheduledMeshDecay
import Erdos.Problem1144.HarperCandidateCovarianceTopComparison

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- The literal retained Gaussian crossing with the canonical rounded
frequency parameters. The observation grid and selector remain explicit. -/
def candidateCovarianceScheduledRetainedCrossing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℕ) (β : ℝ) (u : ι → ℝ) (T : ℝ) (selector : Omega → Finset ι)
    (K : ℝ) (ω : Omega) : ℝ :=
  candidateRetainedEulerWhiteCrossing (candidateEulerTopCutoff T)
    (candidateCovarianceScheduleStart J T) (candidateCovarianceScheduleLength J T)
    (candidateCovarianceScheduleDepth T) (candidateCovarianceScheduleHeight T)
    (Real.log T) (candidateCovarianceScheduleSelected J T) u T (β * T) selector K ω

/-- The actual simultaneous retained variance event, with its literal
variance threshold supplied separately from the canonical parameters. -/
def candidateCovarianceScheduledRetainedVarianceFloor {ι : Type*}
    (J : ℕ) (β : ℝ) (u : ι → ℝ) (T v : ℝ) : Set Omega :=
  candidateRetainedWhiteVarianceFloor (candidateEulerTopCutoff T)
    (candidateCovarianceScheduleStart J T) (candidateCovarianceScheduleLength J T)
    (candidateCovarianceScheduleDepth T) (candidateCovarianceScheduleHeight T)
    (Real.log T) (candidateCovarianceScheduleSelected J T) u T (β * T) v

/-- The actual rounded frequency screen fits inside the cubic Perron band. -/
theorem candidate_eventually_covarianceSchedule_height_le_cubic (J : ℕ) :
    ∀ᶠ T : ℝ in atTop, (candidateCovarianceScheduleHeight T : ℝ) ≤ T ^ 3 := by
  filter_upwards [candidate_eventually_covarianceSchedule_scalar_bounds J,
    eventually_ge_atTop (1 : ℝ)] with T h hT
  dsimp only at h
  obtain ⟨hq, hT0, hAn, hLn, hMn, hA, hL, hM, hh, hpow, htime, hlogT, hlogL, hU⟩ := h
  have hT3 : T ≤ T ^ 3 := by nlinarith [sq_nonneg (T - 1)]
  linarith

end
end Erdos.Problem1144
