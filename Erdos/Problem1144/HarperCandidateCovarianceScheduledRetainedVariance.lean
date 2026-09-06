import Erdos.Problem1144.HarperCandidateCovarianceScheduledRetained

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

private theorem variance_loss_tendsto_zero {E : ℝ → ℝ}
    (hE : Tendsto (fun T => E T * Real.log T ^ ((1 : ℝ) / 2)) atTop (𝓝 0))
    (hn : ∀ᶠ T : ℝ in atTop, 0 ≤ E T)
    {C v d : ℝ} (hC : 0 ≤ C) (hv : 0 < v) (hd : 0 < d) :
    Tendsto (fun T : ℝ =>
      (8 / (v * (1 + Real.log T) ^ (-(1 : ℝ) / 2))) *
        (E T + C / T ^ 2) / d)
      atTop (𝓝 0) := by
  have hct : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hl := (hE.add hct).const_mul (16 / (v * d))
  simp only [add_zero, mul_zero] at hl
  apply squeeze_zero' _ _ hl
  · filter_upwards [hn, eventually_ge_atTop (1 : ℝ)] with T hET hT
    have hs : 0 < 1 + Real.log T := by linarith [Real.log_nonneg hT]
    positivity
  · filter_upwards [hn,
      eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
      with T hET hT1 hq1
    have hT : 0 < T := by linarith
    have hq : 0 < Real.log T := by linarith
    have hs : 0 < 1 + Real.log T := by linarith
    have hscale : (1 + Real.log T) ^ ((1 : ℝ) / 2) ≤
        2 * Real.log T ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      have hh := Real.sqrt_le_sqrt (show 1 + Real.log T ≤ 4 * Real.log T by linarith)
      simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
        show Real.sqrt (4 : ℝ) = 2 by norm_num] using hh
    have htime : Real.log T ^ ((1 : ℝ) / 2) ≤ T := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.sqrt_le_iff.mpr
      refine ⟨hT.le, ?_⟩
      have hh := Real.log_le_self hT.le
      nlinarith
    have hp : (C / T ^ 2) *
        Real.log T ^ ((1 : ℝ) / 2) ≤ C / T := by
      calc
        _ = C * Real.log T ^ ((1 : ℝ) / 2) / T ^ 2 := by ring
        _ ≤ C * T / T ^ 2 := by gcongr
        _ = C / T := by field_simp
    have hp0 : 0 ≤ E T + C / T ^ 2 := by positivity
    have he :
        (8 / (v * (1 + Real.log T) ^ (-(1 : ℝ) / 2))) *
          (E T + C / T ^ 2) / d =
        (8 / (v * d)) * (E T + C / T ^ 2) *
          (1 + Real.log T) ^ ((1 : ℝ) / 2) := by
      rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hs.le]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    rw [he]
    calc
      _ ≤ (8 / (v * d)) * (E T + C / T ^ 2) *
          (2 * Real.log T ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = (16 / (v * d)) * (E T * Real.log T ^ ((1 : ℝ) / 2) +
          (C / T ^ 2) * Real.log T ^ ((1 : ℝ) / 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hp) (by positivity)

/-- The actual retained variance probability is uniform over every finite
observation grid of cardinality at most the time scale. This permits the
larger translated grids arising from the stationary extension. -/
theorem candidate_exists_scheduledRetainedVariance_probability_linear_grid :
    ∃ δ : ℝ, 0 < δ ∧ ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      ∀ α β : ℝ, 1 < α → α ≤ β → β < 4 / 3 →
      ∀ (s : Finset ℕ) (η : s → Bool), ∃ v > 0,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop,
        ∀ n : ℕ, (n : ℝ) ≤ T → ∀ u : Fin n → ℝ,
        (∀ i, u i ∈ Icc (α * T) (β * T)) →
        δ - ε ≤ (candidateCylinderLaw s η).real
          (candidateCovarianceScheduledRetainedVarianceFloor J β u T
            ((v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / 4)) := by
  obtain ⟨δ, hδ, hvar⟩ := candidate_exists_retainedWhite_variance_lower_probability
  obtain ⟨J₀, herr⟩ := candidate_exists_scheduledRetainedError_decay
  obtain ⟨C, hC, hperron⟩ := candidate_exists_topEulerBandWhiteTotalError_bound
  refine ⟨δ, hδ, J₀, ?_⟩
  intro J hJ α β hα hαβ hβ s η
  obtain ⟨v, hv, hvar⟩ := hvar α β hα (by linarith) hαβ s η
  refine ⟨v, hv, ?_⟩
  intro ε hε
  let E := fun T => ∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂mu
  let d := mu.real (candidateCylinder s η)
  let mesh := fun T => (candidateCylinderLaw s η).real
    (candidateCovarianceCommonMeshEvent (candidateCovarianceScheduleStart J T)
      (candidateCovarianceScheduleLength J T) (candidateCovarianceScheduleHeight T)
      (Real.log T))ᶜ
  have hd : 0 < d := ENNReal.toReal_pos (mu_candidateCylinder_ne_zero s η) (measure_ne_top _ _)
  have hEn : ∀ᶠ T : ℝ in atTop, 0 ≤ E T := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact integral_nonneg fun ω => candidate_retainedError_nonneg _ _ _ _ _ _ hT.le _ ω
  have he := variance_loss_tendsto_zero (herr J hJ).1 hEn hC.le hv hd
  have hmesh : Tendsto mesh atTop (𝓝 0) :=
    candidate_cylinder_scheduledCommonMesh_failure_tendsto_zero J s η
  have hl := hmesh.add he
  simp only [add_zero] at hl
  filter_upwards [hvar, hl.eventually (gt_mem_nhds hε),
    candidate_eventually_covarianceSchedule_height_le_cubic J,
    eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with T hvT hsmall hH hTbase hT1
  intro n hn u hpoints
  have hT : 0 < T := by linarith
  have hu (i : Fin n) : u i ≤ β * T := (hpoints i).2
  have hu2 (i : Fin n) : u i ≤ 3 / 2 * T :=
    (hu i).trans (mul_le_mul_of_nonneg_right (by linarith : β ≤ 3 / 2) hT.le)
  have hy (i : Fin n) : ⌊Real.exp (u i - T)⌋₊ ≤ candidateEulerTopCutoff T :=
    candidateEulerTopCutoff_covers_prefix hTbase (hu2 i)
  have hp := hperron u T (T ^ 3) (β * T) hTbase (pow_pos hT _) hu2 hu
  simp only [Fintype.card_fin] at hp
  have hp' : (∫ ω, candidateEulerBandWhiteTotalError (candidateEulerTopCutoff T)
      u (T ^ 3) T (β * T) ω ∂mu) ≤ C / T ^ 2 := by
    apply hp.trans
    calc
      _ ≤ C * T / T ^ 3 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn hC.le) (by positivity)
      _ = _ := by field_simp
  have hs : 0 < 1 + Real.log T := by linarith [Real.log_nonneg hT1]
  have hvscale : 0 < v * (1 + Real.log T) ^ (-(1 : ℝ) / 2) :=
    mul_pos hv (Real.rpow_pos_of_pos hs _)
  have hb := hvT n u hpoints
    (candidateEulerTopCutoff T) (candidateCovarianceScheduleStart J T)
    (candidateCovarianceScheduleLength J T) (candidateCovarianceScheduleDepth T)
    (candidateCovarianceScheduleHeight T) (Real.log T) (candidateCovarianceScheduleSelected J T)
    (T ^ 3) (β * T) hH (pow_pos hT _) hu hy
  have hcost := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl (E T)) hp')
      (show 0 ≤ 8 / (v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)) by positivity)) hd.le
  change mesh T + (8 / (v * (1 + Real.log T) ^ (-(1 : ℝ) / 2))) *
    (E T + C / T ^ 2) / d < ε at hsmall
  change δ - mesh T - (8 / (v * (1 + Real.log T) ^ (-(1 : ℝ) / 2))) *
    (E T + ∫ ω, candidateEulerBandWhiteTotalError (candidateEulerTopCutoff T) u
      (T ^ 3) T (β * T) ω ∂mu) / d ≤
      (candidateCylinderLaw s η).real (candidateCovarianceScheduledRetainedVarianceFloor
        J β u T ((v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / 4)) at hb
  change δ - ε ≤ (candidateCylinderLaw s η).real
    (candidateCovarianceScheduledRetainedVarianceFloor J β u T
      ((v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / 4))
  linarith

/-- The actual variance event on every canonical block and shift inherits
the uniform positive probability with all approximation losses paid. -/
theorem candidate_exists_scheduledRetainedVariance_probability :
    ∃ δ : ℝ, 0 < δ ∧ ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      ∀ α β κ : ℝ, 1 < α → α ≤ β → β < 4 / 3 → 0 < κ →
      ∀ (s : Finset ℕ) (η : s → Bool), ∃ v > 0,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop,
        ∀ k < candidateScheduleN α β κ T,
        ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi),
        let u := fun i : Fin (candidateScheduleM κ T) =>
          candidateSchedulePoint α κ T k i shift
        δ - ε ≤ (candidateCylinderLaw s η).real
          (candidateCovarianceScheduledRetainedVarianceFloor J β u T
            ((v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / 4)) := by
  obtain ⟨δ, hδ, J₀, hb⟩ := candidate_exists_scheduledRetainedVariance_probability_linear_grid
  refine ⟨δ, hδ, J₀, ?_⟩
  intro J hJ α β κ hα hαβ hβ hκ s η
  obtain ⟨v, hv, hb⟩ := hb J hJ α β hα hαβ hβ s η
  refine ⟨v, hv, ?_⟩
  intro ε hε
  filter_upwards [hb ε hε, candidateScheduleM_eventually_le_time hκ,
    eventually_gt_atTop (0 : ℝ)] with T hbT hm hT
  intro k hk shift hshift
  apply hbT (candidateScheduleM κ T) hm
  intro i
  exact Ioc_subset_Icc_self (candidate_grid_point_mem_window (by positivity)
    (candidateSchedule_cover hαβ hT.le) hk i.isLt hshift)

end
end Erdos.Problem1144
