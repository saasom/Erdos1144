import Erdos.Problem1144.HarperCandidateStationaryWhiteComparison
import Erdos.Problem1144.HarperCandidateStationaryGaussianTails
import Erdos.Problem1144.HarperCandidateWhiteCrossingProbability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Erdos.Problem1144

/-- Averaging the literal stationary comparison preserves every measurable
selector. The only losses are the actual high-frequency and omitted-time
Gaussian tails, with the universal coefficients proved by reflection. -/
theorem candidate_exists_integral_squarefree_complete_white_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ κ β : ℝ, 0 < κ → 0 < β →
      ∀ᶠ T : ℝ in atTop, ∀ s : Finset ℕ, ∀ η : s → Bool,
      ∀ (m : ℕ), 0 < m → ∀ (u v : Fin m → ℝ) (b t₀ : ℝ),
      (∀ i, u i = v i + b) →
      (∀ i, v i ≤ β * (T / candidateScheduleW κ T)) →
      (∀ i, u i ≤ β * T) → (∀ i, t₀ ≤ u i) →
      (∀ i, u i ≤ t₀ + candidateScheduleD κ T) →
      ∀ J : Omega → Finset (Fin m), (∀ i, MeasurableSet {ω | i ∈ J ω}) → ∀ K : ℝ,
      (∫ ω, candidateComparisonWhiteCrossing true v (T / candidateScheduleW κ T)
        J (candidateStationaryWhiteTransferThreshold C κ β T K) ω ∂candidateCylinderLaw s η) / 8 ≤
      (∫ ω, candidateComparisonWhiteCrossing false u T J K ω ∂candidateCylinderLaw s η) +
        (∫ ω, candidateGaussianMaximumTail (candidateSquarefreeHighCovariance ω
          (candidateScheduleW κ T / T) (Real.log T ^ 2) v) 1 ∂candidateCylinderLaw s η) / 4 +
        (∫ ω, candidateGaussianMaximumTail (candidateStationaryExtensionCovariance ω u T
          (candidateScheduleW κ T)) 1 ∂candidateCylinderLaw s η) / 2 := by
  obtain ⟨C, hC, hpoint⟩ := candidate_exists_ae_squarefree_complete_white_comparison
  refine ⟨C, hC, ?_⟩
  intro κ β hκ hβ
  filter_upwards [hpoint κ β hκ hβ, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop 1] with T hp hT hq
  intro s η m hm u v b t₀ huv hvβ huβ hu₀ huD J hJ K
  have hW : 0 < candidateScheduleW κ T := mul_pos hκ (Real.log_pos hq)
  have hσ : 0 < candidateScheduleW κ T / T := div_pos hW hT
  have hV : 0 < T / candidateScheduleW κ T := div_pos hT hW
  have hH : 0 < Real.log T ^ 2 := sq_pos_of_pos (by linarith)
  let Q := candidateCylinderLaw s η
  have hsf := candidate_integrable_comparisonWhiteCrossing Q true v hV J hJ
    (candidateStationaryWhiteTransferThreshold C κ β T K)
  have hco := candidate_integrable_comparisonWhiteCrossing Q false u hT J hJ K
  have hhi := (candidate_integral_squarefreeHighCovariance_tail_le s η hm v hσ hH
    (by norm_num : (0 : ℝ) < 1)).1
  have hext := candidate_integrable_stationaryExtension_tail s η u hT hW (1 : ℝ)
  have hh := integral_mono_ae (hsf.div_const 8)
    ((hco.add (hhi.div_const 4)).add (hext.div_const 2)) (by
      filter_upwards [hp s η] with ω hω
      exact hω m u v b t₀ huv hvβ huβ hu₀ huD (J ω) K)
  simp only [Pi.add_apply] at hh
  have hadd := integral_add (hco.add (hhi.div_const 4)) (hext.div_const 2)
  have hadd' := integral_add hco (hhi.div_const 4)
  simp only [Pi.add_apply] at hadd hadd'
  rw [integral_div, hadd, hadd', integral_div, integral_div] at hh
  exact hh

end Erdos.Problem1144
