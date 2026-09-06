import Erdos.Problem1144.HarperCandidateCovarianceScheduledRetained

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- The actual retained Euler Gaussian crossing transfers to the squarefree
white law on every scheduled block and shift. Both error budgets vanish,
uniformly in every measurable selector and every threshold. -/
theorem candidate_exists_scheduledRetained_white_crossing :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ α β κ : ℝ,
      α ≤ β → β < 4 / 3 → 0 < κ →
      ∀ (s : Finset ℕ) (η : s → Bool) (ε : ℝ), 0 < ε →
      ∀ᶠ T : ℝ in atTop, ∀ k < candidateScheduleN α β κ T,
        ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi),
        ∀ selector : Omega → Finset (Fin (candidateScheduleM κ T)),
          (∀ i, MeasurableSet {ω | i ∈ selector ω}) → ∀ K : ℝ,
        let u := fun i : Fin (candidateScheduleM κ T) =>
          candidateSchedulePoint α κ T k i shift
        (∫ ω, candidateCovarianceScheduledRetainedCrossing J β u T selector
          (K + Real.log (Real.log T) ^ 3 + T ^ (-(1 : ℝ) / 2)) ω
          ∂candidateCylinderLaw s η) ≤
        (∫ ω, candidateComparisonWhiteCrossing true u T selector K ω
          ∂candidateCylinderLaw s η) + ε := by
  obtain ⟨J₀, herr⟩ := candidate_exists_scheduledRetainedError_log_card_decay
  refine ⟨J₀, ?_⟩
  intro J hJ α β κ hαβ hβ hκ s η ε hε
  let d := mu.real (candidateCylinder s η)
  let E := fun T => ∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂mu
  let mesh := fun T => (candidateCylinderLaw s η).real
    (candidateCovarianceCommonMeshEvent (candidateCovarianceScheduleStart J T)
      (candidateCovarianceScheduleLength J T) (candidateCovarianceScheduleHeight T)
      (Real.log T))ᶜ
  have he : Tendsto (fun T : ℝ =>
      4 * Real.log (2 * (candidateScheduleM κ T : ℝ)) * E T /
        (d * Real.log (Real.log T) ^ 6)) atTop (𝓝 0) := by
    have hh := (herr J hJ κ hκ).const_mul (4 / d)
    simp only [mul_zero] at hh
    convert hh using 1
    funext T
    dsimp only [E]
    ring
  have hm : Tendsto (fun T : ℝ => 1 / (2 * (candidateScheduleM κ T : ℝ)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop
    ((tendsto_natCast_atTop_atTop.comp (candidateScheduleM_tendsto hκ)).const_mul_atTop
      (by norm_num : (0 : ℝ) < 2))
  have hmesh : Tendsto mesh atTop (𝓝 0) :=
    candidate_cylinder_scheduledCommonMesh_failure_tendsto_zero J s η
  have hsum := (hmesh.add he).add hm
  simp only [add_zero] at hsum
  have hε2 : 0 < ε / 2 := by positivity
  have htop := candidateSchedule_topEulerBand_white_selected_crossing
    (q := 3) (r := (1 : ℝ) / 2) hαβ hβ hκ (by norm_num) s η hε2
  filter_upwards [htop, hsum.eventually (gt_mem_nhds hε2),
    candidate_eventually_covarianceSchedule_height_le_cubic J,
    (candidateScheduleM_tendsto hκ).eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0,
    eventually_gt_atTop (0 : ℝ)] with T htopT hsmall hH hmT hlog hT
  intro k hk shift hshift selector hselector K
  letI : NeZero (candidateScheduleM κ T) := ⟨by omega⟩
  let u := fun i : Fin (candidateScheduleM κ T) => candidateSchedulePoint α κ T k i shift
  have hεscreen : 0 < Real.log (Real.log T) ^ 3 := pow_pos hlog _
  have hH' : (candidateCovarianceScheduleHeight T : ℝ) ≤ T ^ (3 : ℝ) := by
    simpa only [Real.rpow_ofNat] using hH
  have hb := candidate_retainedEuler_band_selected_crossing_le s η
    (candidateEulerTopCutoff T) (candidateCovarianceScheduleStart J T)
    (candidateCovarianceScheduleLength J T) (candidateCovarianceScheduleDepth T)
    (candidateCovarianceScheduleHeight T) (Real.log T) (candidateCovarianceScheduleSelected J T)
    u hH' hT (β * T) selector hselector (K + T ^ (-(1 : ℝ) / 2)) hεscreen
  have hw := htopT k hk shift hshift selector hselector K
  simp only [Fintype.card_fin] at hb
  have hp : (Real.log (Real.log T) ^ 3) ^ 2 = Real.log (Real.log T) ^ 6 := by ring
  rw [hp, show K + T ^ (-(1 : ℝ) / 2) + Real.log (Real.log T) ^ 3 =
    K + Real.log (Real.log T) ^ 3 + T ^ (-(1 : ℝ) / 2) by ring] at hb
  change _ ≤ _ + mesh T + 4 * Real.log (2 * (candidateScheduleM κ T : ℝ)) * E T /
    (d * Real.log (Real.log T) ^ 6) + 1 / (2 * (candidateScheduleM κ T : ℝ)) at hb
  change mesh T + 4 * Real.log (2 * (candidateScheduleM κ T : ℝ)) * E T /
    (d * Real.log (Real.log T) ^ 6) + 1 / (2 * (candidateScheduleM κ T : ℝ)) < ε / 2 at hsmall
  change (∫ ω, candidateCovarianceScheduledRetainedCrossing J β u T selector
    (K + Real.log (Real.log T) ^ 3 + T ^ (-(1 : ℝ) / 2)) ω ∂candidateCylinderLaw s η) ≤ _
  change (∫ ω, candidateCovarianceScheduledRetainedCrossing J β u T selector
    (K + Real.log (Real.log T) ^ 3 + T ^ (-(1 : ℝ) / 2)) ω ∂candidateCylinderLaw s η) ≤ _ at hb
  norm_num only [neg_div] at hw
  linarith

end
end Erdos.Problem1144
