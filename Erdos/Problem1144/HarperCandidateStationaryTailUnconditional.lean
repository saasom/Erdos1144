import Erdos.Problem1144.HarperCandidateEnergyFatouUniform
import Erdos.Problem1144.HarperCandidateStationaryTailEnergyDecay

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace Erdos.Problem1144

/-- The actual stationary-extension error vanishes on the selected schedule.
The complete-energy moment is proved, so no weighted almost-sure bound or
unproved arithmetic moment is required. The remaining hypotheses identify
the Gaussian error and bound it by the literal omitted variance. -/
theorem candidate_stationary_gaussian_maximum_tendsto_zero
    {Ξ : ℝ → Type*} [∀ T, MeasurableSpace (Ξ T)]
    {P : (T : ℝ) → Measure (Ξ T)} [∀ T, IsProbabilityMeasure (P T)]
    (s : Finset ℕ) (η : s → Bool) {c κ r : ℝ}
    (hc : 0 ≤ c) (hκ : 0 < κ) (hgap : 2 < c * κ) (hr : 0 < r)
    (X : (T : ℝ) → Fin (candidateScheduleM κ T) → Omega × Ξ T → ℝ)
    (v : (T : ℝ) → Omega → Fin (candidateScheduleM κ T) → ℝ≥0)
    (hXm : ∀ T i, Measurable (X T i))
    (hX : ∀ T ω i, (P T).map (fun ξ => X T i (ω, ξ)) = gaussianReal 0 (v T ω i))
    (hv : ∀ᶠ T in atTop, ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ i,
      (v T ω i : ℝ) ≤ candidateCompleteStationaryTailVariance ω c T (candidateScheduleW κ T)) :
    Tendsto (fun T : ℝ => ((candidateCylinderLaw s η).prod (P T)).real
      {z | ∃ i, r ≤ |X T i z|}) atTop (𝓝 0) := by
  obtain ⟨C, _, hMoment⟩ := candidate_exists_dampedCompleteEnergy_uniform_eighth_moment
  exact candidate_stationary_gaussian_maximum_tendsto_zero_of_uniform_energy_moment
    s η hc hκ (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (0 : ℝ) < 1 / 8)
    hgap hr hMoment X v hXm hX hv

end Erdos.Problem1144
