import Erdos.Problem1144.HarperCandidateCovarianceScheduledRetainedError
import Erdos.Problem1144.HarperCandidateSchedule

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

private theorem rate_limits {f : ℝ → ℝ}
    (hn : ∀ᶠ T : ℝ in atTop, 0 ≤ f T)
    (hb : ∃ K > 0, ∀ᶠ T : ℝ in atTop,
      f T ≤ K * Real.log (Real.log T) ^ 4 / Real.log T) :
    Tendsto (fun T => f T * Real.log T ^ ((1 : ℝ) / 2)) atTop (𝓝 0) ∧
      Tendsto (fun T => Real.log T * f T / Real.log (Real.log T) ^ 6) atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := hb
  constructor
  · have hl := ((isLittleO_log_rpow_rpow_atTop (4 : ℝ)
      (s := (1 : ℝ) / 2) (by norm_num)).tendsto_div_nhds_zero.comp
        Real.tendsto_log_atTop).const_mul K
    norm_num only [Real.rpow_ofNat, mul_zero, Function.comp_def] at hl
    apply squeeze_zero' _ _ hl
    · filter_upwards [hn, Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hf hq
      exact mul_nonneg hf (Real.rpow_nonneg hq.le _)
    · filter_upwards [hbound, Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hf hq
      have hh := mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg hq.le ((1 : ℝ) / 2))
      apply hh.trans_eq
      have he : Real.log T ^ ((1 : ℝ) / 2) / Real.log T =
          1 / Real.log T ^ ((1 : ℝ) / 2) := by
        calc
          _ = Real.log T ^ ((1 : ℝ) / 2) / Real.log T ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = Real.log T ^ (-((1 : ℝ) / 2)) := by rw [← Real.rpow_sub hq]; norm_num
          _ = _ := by rw [Real.rpow_neg hq.le]; simp only [one_div]
      calc
        _ = (K * Real.log (Real.log T) ^ 4) *
          (Real.log T ^ ((1 : ℝ) / 2) / Real.log T) := by ring
        _ = _ := by rw [he]; ring
  · have hθ := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    have hl := (tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hθ)).const_mul K
    simp only [mul_zero, Function.comp_def] at hl
    apply squeeze_zero' _ _ hl
    · filter_upwards [hn, Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hf hq
      exact div_nonneg (mul_nonneg hq.le hf) (by positivity)
    · filter_upwards [hbound, Real.tendsto_log_atTop.eventually_gt_atTop 1] with T hf hq
      have hq0 : 0 < Real.log T := by linarith
      have hθ0 : 0 < Real.log (Real.log T) := Real.log_pos hq
      have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf hq0.le)
        (pow_nonneg hθ0.le 6)
      apply hh.trans_eq
      field_simp

/-- The unconditional error moment has both rates required by the literal
variance and logarithmic Gaussian-maximum comparisons. -/
theorem candidate_exists_scheduledRetainedError_decay :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      Tendsto (fun T => (∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂mu) *
        Real.log T ^ ((1 : ℝ) / 2)) atTop (𝓝 0) ∧
      Tendsto (fun T => Real.log T *
        (∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂mu) /
          Real.log (Real.log T) ^ 6) atTop (𝓝 0) := by
  obtain ⟨J₀, hb⟩ := candidate_exists_scheduledRetainedError_integral_le
  refine ⟨J₀, ?_⟩
  intro J hJ
  apply rate_limits _ (hb J hJ)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact integral_nonneg fun ω => candidate_retainedError_nonneg _ _ _ _ _ _ hT.le _ ω

/-- Under every fixed cylinder, the actual error vanishes relative to
the `(log T)^(-1/2)` variance floor, and after the maximum-comparison cost
`log T / (log log T)^6`. The latter corresponds to the fixed exponent `ell=3`. -/
theorem candidate_exists_cylinder_scheduledRetainedError_decay :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ (s : Finset ℕ) (η : s → Bool),
      Tendsto (fun T =>
        (∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂candidateCylinderLaw s η) *
          Real.log T ^ ((1 : ℝ) / 2)) atTop (𝓝 0) ∧
      Tendsto (fun T => Real.log T *
        (∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂candidateCylinderLaw s η) /
          Real.log (Real.log T) ^ 6) atTop (𝓝 0) := by
  obtain ⟨J₀, hb⟩ := candidate_exists_cylinder_scheduledRetainedError_integral_le
  refine ⟨J₀, ?_⟩
  intro J hJ s η
  apply rate_limits _ (hb J hJ s η)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact integral_nonneg fun ω => candidate_retainedError_nonneg _ _ _ _ _ _ hT.le _ ω

private theorem scheduled_log_card_le {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop,
      0 ≤ Real.log (2 * (candidateScheduleM κ T : ℝ)) ∧
        Real.log (2 * (candidateScheduleM κ T : ℝ)) ≤ 2 * Real.log T := by
  filter_upwards [(candidateScheduleM_tendsto hκ).eventually_ge_atTop 1,
    (candidateScheduleW_tendsto hκ).eventually_ge_atTop 1,
    eventually_ge_atTop (2 : ℝ)] with T hm hW hT2
  have hT : 0 < T := by linarith
  have hmR : (1 : ℝ) ≤ candidateScheduleM κ T := by exact_mod_cast hm
  have hden : 1 ≤ candidateScheduleW κ T ^ 2 * (2 * Real.pi) := by
    have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hW) hp
  have hfloor : (candidateScheduleM κ T : ℝ) ≤ T := by
    have hh := Nat.floor_le (show 0 ≤ candidateScheduleD κ T / (2 * Real.pi) by
      unfold candidateScheduleD; positivity)
    apply hh.trans
    unfold candidateScheduleD
    rw [div_div]
    exact div_le_self hT.le hden
  have hh := Real.log_le_log (by positivity : 0 < 2 * (candidateScheduleM κ T : ℝ))
    (mul_le_mul_of_nonneg_left hfloor (by norm_num : (0 : ℝ) ≤ 2))
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hT.ne'] at hh
  have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT2
  exact ⟨Real.log_nonneg (by linarith), by linarith⟩

/-- The actual grid-cardinality version of the unconditional error rate,
as it occurs in the retained crossing theorem before cylinder normalization. -/
theorem candidate_exists_scheduledRetainedError_log_card_decay :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ κ : ℝ, 0 < κ →
      Tendsto (fun T => Real.log (2 * (candidateScheduleM κ T : ℝ)) *
        (∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂mu) /
          Real.log (Real.log T) ^ 6) atTop (𝓝 0) := by
  obtain ⟨J₀, hb⟩ := candidate_exists_scheduledRetainedError_decay
  refine ⟨J₀, ?_⟩
  intro J hJ κ hκ
  have hl := (hb J hJ).2.const_mul 2
  simp only [mul_zero] at hl
  apply squeeze_zero' _ _ hl
  · filter_upwards [scheduled_log_card_le hκ, eventually_gt_atTop (0 : ℝ)] with T hc hT
    have hf : 0 ≤ ∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂mu :=
      integral_nonneg fun ω => candidate_retainedError_nonneg _ _ _ _ _ _ hT.le _ ω
    exact div_nonneg (mul_nonneg hc.1 hf) (by positivity)
  · filter_upwards [scheduled_log_card_le hκ, eventually_gt_atTop (0 : ℝ)] with T hc hT
    have hf : 0 ≤ ∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂mu :=
      integral_nonneg fun ω => candidate_retainedError_nonneg _ _ _ _ _ _ hT.le _ ω
    convert div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc.2 hf)
      (show 0 ≤ Real.log (Real.log T) ^ 6 by positivity) using 1 <;> ring

/-- The maximum comparison loses only the actual logarithm of the rounded
grid cardinality. With `ell=3`, this loss times the literal common error
vanishes under every fixed cylinder. -/
theorem candidate_exists_cylinder_scheduledRetainedError_log_card_decay :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ (s : Finset ℕ) (η : s → Bool)
      (κ : ℝ), 0 < κ →
      Tendsto (fun T => Real.log (2 * (candidateScheduleM κ T : ℝ)) *
        (∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂candidateCylinderLaw s η) /
          Real.log (Real.log T) ^ 6) atTop (𝓝 0) := by
  obtain ⟨J₀, hb⟩ := candidate_exists_cylinder_scheduledRetainedError_decay
  refine ⟨J₀, ?_⟩
  intro J hJ s η κ hκ
  have hl := (hb J hJ s η).2.const_mul 2
  simp only [mul_zero, Function.comp_def] at hl
  apply squeeze_zero' _ _ hl
  · filter_upwards [scheduled_log_card_le hκ, eventually_gt_atTop (0 : ℝ)] with T hc hT
    have hf : 0 ≤ ∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂candidateCylinderLaw s η :=
      integral_nonneg fun ω => candidate_retainedError_nonneg _ _ _ _ _ _ hT.le _ ω
    exact div_nonneg (mul_nonneg hc.1 hf) (by positivity)
  · filter_upwards [scheduled_log_card_le hκ, eventually_gt_atTop (0 : ℝ)] with T hc hT
    have hf : 0 ≤ ∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂candidateCylinderLaw s η :=
      integral_nonneg fun ω => candidate_retainedError_nonneg _ _ _ _ _ _ hT.le _ ω
    convert div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc.2 hf)
      (show 0 ≤ Real.log (Real.log T) ^ 6 by positivity) using 1 <;> ring

end
end Erdos.Problem1144
