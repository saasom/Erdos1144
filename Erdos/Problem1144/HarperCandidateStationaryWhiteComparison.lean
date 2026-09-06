import Erdos.Problem1144.HarperCandidateStationaryTimeGeometry
import Erdos.Problem1144.HarperCandidateSpectralCovarianceTail
import Erdos.Problem1144.HarperCandidateSchedule

open MeasureTheory ProbabilityTheory Set Matrix Filter
open scoped Topology
namespace Erdos.Problem1144
noncomputable section

/-- The exact squarefree-white threshold needed for a complete-white
crossing, including both unit error margins and every covariance scaling. -/
def candidateStationaryWhiteTransferThreshold (C κ β T K : ℝ) : ℝ :=
  let W := candidateScheduleW κ T
  let σ := W / T
  let c := 1 / (W * (C * Real.log (2 * Real.log T ^ 2 + 4) ^ 7) ^ 2)
  let lam := β * Real.exp (2 * σ * candidateScheduleD κ T)
  (((Real.sqrt lam * K + 1) / Real.sqrt c) + 1) / Real.exp (-(β - 1))

/-- The actual stationary spectral bridge, with all three PSD comparisons
and both decompositions instantiated. The two displayed tails are the
literal Gaussian high-frequency and omitted-time covariances. Any selected
set is preserved; all entry-integrability and PSD claims hold almost surely
from the already proved arithmetic moments. -/
theorem candidate_exists_ae_squarefree_complete_white_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ κ β : ℝ, 0 < κ → 0 < β →
      ∀ᶠ T : ℝ in atTop, ∀ s : Finset ℕ, ∀ η : s → Bool,
      ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ (m : ℕ) (u v : Fin m → ℝ) (b t₀ : ℝ),
      (∀ i, u i = v i + b) →
      (∀ i, v i ≤ β * (T / candidateScheduleW κ T)) →
      (∀ i, u i ≤ β * T) →
      (∀ i, t₀ ≤ u i) →
      (∀ i, u i ≤ t₀ + candidateScheduleD κ T) →
      ∀ J : Finset (Fin m), ∀ K : ℝ,
      candidateComparisonWhiteCrossing true v (T / candidateScheduleW κ T)
        (fun _ => J) (candidateStationaryWhiteTransferThreshold C κ β T K) ω / 8 ≤
      candidateComparisonWhiteCrossing false u T (fun _ => J) K ω +
        candidateGaussianMaximumTail (candidateSquarefreeHighCovariance ω
          (candidateScheduleW κ T / T) (Real.log T ^ 2) v) 1 / 4 +
        candidateGaussianMaximumTail (candidateStationaryExtensionCovariance ω u T
          (candidateScheduleW κ T)) 1 / 2 := by
  obtain ⟨C, hC, hspec⟩ := exists_candidate_complete_stationaryCovariance_window_domination
  refine ⟨C, hC, ?_⟩
  intro κ β hκ hβ
  filter_upwards [hspec κ hκ, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop 1] with T hspecT hT hq
  let W := candidateScheduleW κ T
  let σ := W / T
  let V := T / W
  have hW : 0 < W := mul_pos hκ (Real.log_pos hq)
  have hσ : 0 < σ := div_pos hW hT
  have hV : 0 < V := div_pos hT hW
  have hVσ : 1 / σ = V := by dsimp [σ, V]; field_simp
  have hσV : σ * V = 1 := by dsimp [σ, V]; field_simp
  intro s η
  filter_upwards [hspecT s η,
    candidateCylinderLaw_ae_squarefree_white_stationary_domination s η hσ hV,
    candidateCylinderLaw_ae_squarefree_covariance_split s η hσ,
    candidateCylinderLaw_ae_complete_stationary_split s η hT hW,
    candidateCylinderLaw_ae_complete_stationary_white_domination s η hT hW]
    with ω hspecω hfirstω hsplitSF hsplitC hlastω
  intro m u v b t₀ huv hvβ huβ hu₀ huD J K
  let A := candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) v V
  let L := candidateSquarefreeLowCovariance ω σ (Real.log T ^ 2) v
  let H := candidateSquarefreeHighCovariance ω σ (Real.log T ^ 2) v
  let Q := candidateStationaryTruncatedCovariance ω u T W
  let E := candidateStationaryExtensionCovariance ω u T W
  let B := candidateWhiteCovariance (harperCandidateLogProcess ω) u T
  let c := 1 / (W * (C * Real.log (2 * Real.log T ^ 2 + 4) ^ 7) ^ 2)
  let lam := β * Real.exp (2 * σ * candidateScheduleD κ T)
  let r : Fin m → ℝ := fun i => Real.exp (-σ * (v i - V))
  let d : Fin m → ℝ := fun i => Real.exp (σ * (u i - t₀))
  let r₀ := Real.exp (-(β - 1))
  have hc : 0 < c := by
    have hlog : 0 < Real.log (2 * Real.log T ^ 2 + 4) := Real.log_pos (by nlinarith [sq_nonneg (Real.log T)])
    dsimp only [c]
    positivity
  have hlam : 0 < lam := mul_pos hβ (Real.exp_pos _)
  have hr₀ : 0 < r₀ := Real.exp_pos _
  have hA : A.PosSemidef := candidate_comparisonWhiteCovariance_posSemidef true ω v hV
  have hB : B.PosSemidef := candidate_comparisonWhiteCovariance_posSemidef false ω u hT
  have hsf := hsplitSF m v (Real.log T ^ 2)
  rw [hVσ] at hsf
  have hcpl := hsplitC m u
  have hfirst : (L + H - candidateCovarianceDiagonal r A).PosSemidef := by
    have hh := hfirstω m v
    rw [hsf.1] at hh
    exact hh
  have hmid : (Q + E - c • L).PosSemidef := by
    have hh := hspecω m v
    have hvu : candidateStationaryCovariance (harperCandidateLogProcess ω) v σ T =
        candidateStationaryCovariance (harperCandidateLogProcess ω) u σ T := by
      have he := candidateStationaryCovariance_translate (harperCandidateLogProcess ω) v σ T b
      have heq : (fun i => v i + b) = u := funext fun i => (huv i).symm
      rw [heq] at he
      exact he.symm
    change (candidateStationaryCovariance (harperCandidateLogProcess ω) v σ T -
      c • candidateSpectralCovariance (volume.restrict {τ : ℝ | |τ| ≤ Real.log T ^ 2}) v
        (candidateLogSpectralDensity (harperCandidateSquarefreeLogProcess ω) σ V)).PosSemidef at hh
    rw [hvu, hcpl.1] at hh
    change (Q + E - c • candidateSpectralCovariance
      (volume.restrict {τ : ℝ | |τ| ≤ Real.log T ^ 2}) v
      (candidateLogSpectralDensity (harperCandidateSquarefreeLogProcess ω) σ V)).PosSemidef at hh
    simpa only [L, candidateSquarefreeLowCovariance, hVσ] using hh
  have hlast : (lam • B - candidateCovarianceDiagonal d Q).PosSemidef :=
    hlastω m u β t₀ (candidateScheduleD κ T) huβ huD
  have hr : ∀ i ∈ J, r₀ ≤ |r i| := by
    intro i hi
    dsimp only [r₀, r]
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (hvβ i) hσ.le
    change σ * v i ≤ σ * (β * V) at hh
    have hh' : σ * v i ≤ β := by
      calc
        _ ≤ σ * (β * V) := hh
        _ = β * (σ * V) := by ring
        _ = β := by rw [hσV, mul_one]
    nlinarith only [hh', hσV]
  have hd : ∀ i ∈ J, 1 ≤ |d i| := by
    intro i hi
    dsimp only [d]
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.one_le_exp_iff.mpr (mul_nonneg hσ.le (sub_nonneg.mpr (hu₀ i)))
  have h := candidate_gaussian_stationary_selected_comparison hA hsf.2.1 hsf.2.2.1
    hcpl.2.1 hcpl.2.2 hB r d hc hlam hr₀ hfirst hmid hlast J hr hd K 1 1
  unfold candidateComparisonWhiteCrossing
  rw [candidate_comparisonWhite_gram_eq_whiteCovariance true ω v hV,
    candidate_comparisonWhite_gram_eq_whiteCovariance false ω u hT]
  exact h

end
end Erdos.Problem1144
