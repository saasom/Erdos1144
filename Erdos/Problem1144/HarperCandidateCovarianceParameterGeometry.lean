import Erdos.Problem1144.HarperCandidateCovarianceParameterSchedule

open Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

private theorem log_div_log_tendsto :
    Tendsto (fun T : ℝ => Real.log T / Real.log (Real.log T)) atTop atTop := by
  have hzero := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in atTop, Real.log x / x ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  have hwithin : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero.comp Real.tendsto_log_atTop
  simpa only [Function.comp_def, Pi.inv_apply, inv_div] using hinv

private theorem unrounded_order_tendsto :
    Tendsto (fun T : ℝ => Real.log T / (4000 * Real.log (Real.log T))) atTop atTop := by
  convert log_div_log_tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 4000) using 1
  ext T
  ring

theorem candidate_covarianceSchedule_order_tendsto :
    Tendsto candidateCovarianceScheduleOrder atTop atTop :=
  tendsto_nat_floor_atTop.comp unrounded_order_tendsto

/-- Rounding the actual order preserves the coefficient `1/4000` in the
high-moment scale; no order-comparison hypothesis is supplied. -/
theorem candidate_covarianceSchedule_order_ratio_tendsto :
    Tendsto (fun T : ℝ => (candidateCovarianceScheduleOrder T : ℝ) /
      (Real.log T / Real.log (Real.log T))) atTop (𝓝 (1 / 4000 : ℝ)) := by
  have h := (tendsto_nat_floor_div_atTop.comp unrounded_order_tendsto).div_const (4000 : ℝ)
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 1] with T hT
  have hq : Real.log T ≠ 0 := by linarith
  have hqq : Real.log (Real.log T) ≠ 0 := (Real.log_pos hT).ne'
  dsimp only [Function.comp_def, candidateCovarianceScheduleOrder]
  field_simp

/-- Equivalent form directly usable in logarithms of the printed moment
bound. -/
theorem candidate_covarianceSchedule_order_log_ratio_tendsto :
    Tendsto (fun T : ℝ => (candidateCovarianceScheduleOrder T : ℝ) *
      Real.log (Real.log T) / Real.log T) atTop (𝓝 (1 / 4000 : ℝ)) := by
  simpa only [div_div_eq_mul_div] using candidate_covarianceSchedule_order_ratio_tendsto

private theorem eventually_window_scalar :
    ∀ᶠ q : ℝ in atTop, 4 * q ^ 2 ≤ Real.exp (q ^ ((1 : ℝ) / 20)) := by
  have h := candidate_tendsto_rpow_mul_exp_rpow_sub (2 : ℝ)
    (ν := (0 : ℝ)) (a := (1 : ℝ) / 20) (c := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [(tendsto_order.mp h).2 (1 / 4) (by norm_num)] with q hq
  norm_num only [Real.rpow_zero, Real.rpow_ofNat, one_mul] at hq
  have hl : q ^ 2 * Real.exp (-(q ^ ((1 : ℝ) / 20))) ≤
      q ^ 2 * Real.exp (1 - q ^ ((1 : ℝ) / 20)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg q)
  rw [Real.exp_neg, ← div_eq_mul_inv] at hl
  have hb := (div_le_iff₀ (Real.exp_pos (q ^ ((1 : ℝ) / 20)))).mp
    (hl.trans hq.le)
  linarith

/-- The actual natural frequency window is eventually inside the
growing-height arithmetic window for every fixed analytic offset. -/
theorem candidate_eventually_covarianceSchedule_window (J : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      2 * (candidateCovarianceScheduleHeight T : ℝ) ≤
        candidateCovarianceHeightWindow (candidateCovarianceScheduleStart J T) := by
  have hq : Tendsto (fun T : ℝ => Real.log T ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 2,
    hq.eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)),
    Real.tendsto_log_atTop.eventually eventually_window_scalar] with T hlog hqT hwin
  have hb := (candidate_covarianceSchedule_start_log_bounds J hqT).1
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ J := one_le_pow₀ (by norm_num)
  have hA : Real.log T ≤ Real.log (Problem520.harperBlockEndpoint
      (candidateCovarianceScheduleStart J T) : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hpow (show 0 ≤ Real.log T ^ 2 / 2 by positivity)
    nlinarith
  have hM := (candidate_covarianceSchedule_height_bounds T).2
  calc
    2 * (candidateCovarianceScheduleHeight T : ℝ) ≤ 4 * Real.log T ^ 2 := by nlinarith
    _ ≤ Real.exp (Real.log T ^ ((1 : ℝ) / 20)) := hwin
    _ ≤ _ := Real.exp_le_exp.mpr
      (Real.rpow_le_rpow (by linarith : 0 ≤ Real.log T) hA (by norm_num))

/-- All discrete screen, real annulus and moment geometry conditions are
eventual consequences of the fixed-offset rounded definitions. -/
theorem candidate_eventually_covarianceSchedule_geometry (J : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      1 < T ∧ 1 ≤ Real.log T ∧
      J + candidateCovarianceScheduleDepth T = candidateCovarianceScheduleStart J T ∧
      6 ≤ candidateCovarianceScheduleLength J T ∧
      candidateCovarianceScheduleStart J T < candidateCovarianceScheduleStrong J T ∧
      candidateCovarianceScheduleStrong J T ≤ candidateEulerTopIndex T ∧
      3 ≤ candidateCovarianceScheduleStrong J T - candidateCovarianceScheduleStart J T ∧
      1 ≤ candidateCovarianceScheduleOrder T ∧
      0 < candidateCovarianceScheduleLowerHeight T ∧
      0 < candidateCovarianceScheduleWidth T ∧
      0 < candidateCovarianceScheduleHeight T ∧
      2 * (candidateCovarianceScheduleHeight T : ℝ) ≤
        candidateCovarianceHeightWindow (candidateCovarianceScheduleStart J T) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    candidate_eventually_covarianceSchedule_room J 6,
    candidate_covarianceSchedule_order_tendsto.eventually_ge_atTop 1,
    candidate_eventually_covarianceSchedule_window J] with T hT hlog hroom hk hwin
  have hlength : 6 ≤ candidateCovarianceScheduleLength J T := by
    unfold candidateCovarianceScheduleLength
    omega
  have hmid : candidateCovarianceScheduleStart J T < candidateCovarianceScheduleStrong J T ∧
      candidateCovarianceScheduleStrong J T ≤ candidateEulerTopIndex T ∧
      3 ≤ candidateCovarianceScheduleStrong J T - candidateCovarianceScheduleStart J T := by
    unfold candidateCovarianceScheduleStrong candidateCovarianceScheduleLength
    omega
  have hM : 0 < candidateCovarianceScheduleHeight T := by
    have hm := (candidate_covarianceSchedule_height_bounds T).1
    have hmr : (0 : ℝ) < candidateCovarianceScheduleHeight T := by nlinarith
    exact_mod_cast hmr
  exact ⟨hT, hlog, rfl, hlength, hmid.1, hmid.2.1, hmid.2.2, hk,
    candidate_covarianceSchedule_lowerHeight_pos T,
    Real.rpow_pos_of_pos (by linarith) _, hM, hwin⟩

/-- The reciprocal strong-gap cutoff has an explicit `q*sqrt(T)` bound.
Only the fixed analytic offset enters its constant. -/
theorem candidate_eventually_covarianceSchedule_strong_scale (J : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      1 / Problem520.invLog (Problem520.harperBlockEndpoint
        (candidateCovarianceScheduleStrong J T - 1)) ≤
          Real.sqrt ((2 : ℝ) ^ J) * Real.log T * Real.sqrt T := by
  have hq : Tendsto (fun T : ℝ => Real.log T ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)),
    eventually_gt_atTop (1 : ℝ),
    hq.eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)),
    candidate_eventually_covarianceSchedule_room J 0] with T hT hT1 hqT hroom
  have hST : candidateCovarianceScheduleStart J T ≤ candidateEulerTopIndex T := by simpa using hroom
  have hA := (candidate_covarianceSchedule_start_log_bounds J hqT).2
  have hL := (candidateEulerTopCutoff_log_bounds hT).2
  have hLn : 0 ≤ Real.log (candidateEulerTopCutoff T : ℝ) :=
    zero_le_one.trans (Problem520.one_le_log_harperBlockEndpoint _)
  have hlogn : 0 ≤ Real.log T := (Real.log_pos hT1).le
  calc
    _ = Real.log (Problem520.harperBlockEndpoint
        (candidateCovarianceScheduleStrong J T - 1) : ℝ) := by simp [Problem520.invLog]
    _ ≤ Real.sqrt (Real.log (Problem520.harperBlockEndpoint
        (candidateCovarianceScheduleStart J T) : ℝ) * Real.log (candidateEulerTopCutoff T : ℝ)) :=
      candidate_covarianceSchedule_strong_log_le_sqrt J T hST
    _ ≤ Real.sqrt (((2 : ℝ) ^ J * Real.log T ^ 2) * T) :=
      Real.sqrt_le_sqrt (mul_le_mul hA hL hLn (by positivity))
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hlogn]

end
end Erdos.Problem1144
