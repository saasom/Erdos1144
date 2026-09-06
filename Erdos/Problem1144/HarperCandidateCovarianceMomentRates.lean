import Erdos.Problem1144.HarperCandidateCovarianceParameterGeometry

open Filter
open scoped Topology
namespace Erdos.Problem1144
noncomputable section

/-- Variable powers at the actual rounded moment order. The coefficient
`1/4000` is proved from the schedule, rather than supplied as an assumption. -/
theorem candidate_covarianceSchedule_variable_power_tendsto_zero
    (a b : ℝ) (hab : a + b / 4000 < 0) :
    Tendsto (fun T : ℝ => T ^ a *
      Real.log T ^ (b * (candidateCovarianceScheduleOrder T : ℝ))) atTop (𝓝 0) := by
  let r := (a + b / 4000) / 2
  have hr : r < 0 := by dsimp [r]; linarith
  have hl := candidate_covarianceSchedule_order_log_ratio_tendsto.const_mul b |>.const_add a
  have hlim : Tendsto (fun T : ℝ => T ^ r) atTop (𝓝 0) :=
    by simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hr)
  apply squeeze_zero' (g := fun T : ℝ => T ^ r)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (Real.log_pos hT).le _)
  · have he := (tendsto_order.mp hl).2 r (by dsimp [r]; linarith)
    filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with T he hT
    have hTp : 0 < T := by linarith
    have hq : 0 < Real.log T := Real.log_pos hT
    have hex : a * Real.log T + b * (candidateCovarianceScheduleOrder T : ℝ) *
        Real.log (Real.log T) ≤ r * Real.log T := by
      have hh := mul_le_mul_of_nonneg_right he.le hq.le
      field_simp at hh
      nlinarith
    rw [Real.rpow_def_of_pos hTp, Real.rpow_def_of_pos hq, Real.rpow_def_of_pos hTp,
      ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [hex])
  · exact hlim

/-- The three explicit exponents left by the printed near-row estimate all
decay at degree exponent `4/5`. -/
theorem candidate_covarianceSchedule_near_majorant_tendsto_zero :
    Tendsto (fun T : ℝ =>
      T ^ ((1 : ℝ) / 5) * Real.log T ^ (-1886 * (candidateCovarianceScheduleOrder T : ℝ)) +
      T ^ (-(1 : ℝ) / 20) * Real.log T ^ (131 * (candidateCovarianceScheduleOrder T : ℝ)) +
      T ^ (-(3 : ℝ) / 10) * Real.log T ^ (130 * (candidateCovarianceScheduleOrder T : ℝ)))
      atTop (𝓝 0) := by
  have h₁ := candidate_covarianceSchedule_variable_power_tendsto_zero (1 / 5) (-1886) (by norm_num)
  have h₂ := candidate_covarianceSchedule_variable_power_tendsto_zero (-1 / 20) 131 (by norm_num)
  have h₃ := candidate_covarianceSchedule_variable_power_tendsto_zero (-3 / 10) 130 (by norm_num)
  simpa only [add_zero] using (h₁.add h₂).add h₃

end
end Erdos.Problem1144
