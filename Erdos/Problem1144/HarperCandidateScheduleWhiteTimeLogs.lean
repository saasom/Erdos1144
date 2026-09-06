import Erdos.Problem1144.HarperCandidateScheduleWhiteTime

open Set Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- The literal smaller white time lies between the square root and the
outer time, eventually. -/
theorem candidateScheduleWhiteTime_eventually_sqrt_bounds
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, 0 < T ∧
      Real.sqrt T ≤ candidateScheduleWhiteTime κ T ∧
      candidateScheduleWhiteTime κ T ≤ T := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (candidateScheduleW_tendsto hκ).eventually_ge_atTop 1,
    (candidateScheduleW_sq_div_tendsto hκ).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with T hT hW hsmall
  have hW0 : 0 < candidateScheduleW κ T := by linarith
  have hWsq : candidateScheduleW κ T ^ 2 ≤ T :=
    le_of_lt (by simpa using (div_lt_iff₀ hT).mp hsmall)
  have hsW := Real.le_sqrt_of_sq_le hWsq
  refine ⟨hT, ?_, div_le_self hT.le hW⟩
  apply (le_div_iff₀ hW0).mpr
  calc
    Real.sqrt T * candidateScheduleW κ T ≤ Real.sqrt T * Real.sqrt T :=
      mul_le_mul_of_nonneg_left hsW (Real.sqrt_nonneg T)
    _ = T := Real.mul_self_sqrt hT.le

/-- Taking logarithms loses at most a factor of two in the time scale. -/
theorem candidateScheduleWhiteTime_eventually_log_bounds
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop,
      Real.log T / 2 ≤ Real.log (candidateScheduleWhiteTime κ T) ∧
      Real.log (candidateScheduleWhiteTime κ T) ≤ Real.log T := by
  filter_upwards [candidateScheduleWhiteTime_eventually_sqrt_bounds hκ] with T h
  have hs := Real.sqrt_pos.2 h.1
  have hV := hs.trans_le h.2.1
  refine ⟨?_, Real.log_le_log hV h.2.2⟩
  simpa only [Real.log_sqrt h.1.le] using Real.log_le_log hs h.2.1

/-- The logarithmic thresholds appearing on the outer and smaller white
scales are comparable, with explicit absolute constants. -/
theorem candidateScheduleWhiteTime_eventually_log_scale_comparison
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop,
      Real.log (1 + Real.log T) ≤
          2 * Real.log (1 + Real.log (candidateScheduleWhiteTime κ T)) ∧
      Real.log (Real.log T) ≤
          2 * Real.log (1 + Real.log (candidateScheduleWhiteTime κ T)) ∧
      Real.log (2 * Real.log T ^ 2 + 4) ≤
          3 * Real.log (1 + Real.log (candidateScheduleWhiteTime κ T)) := by
  filter_upwards [candidateScheduleWhiteTime_eventually_log_bounds hκ,
    Real.tendsto_log_atTop.eventually_ge_atTop 32] with T h hq
  let q := Real.log T
  let x := Real.log (candidateScheduleWhiteTime κ T)
  have hqx : q ≤ 2 * x := by dsimp [q, x]; linarith [h.1]
  have hx : 16 ≤ x := by dsimp [q, x] at *; linarith [h.1]
  have hx0 : 0 ≤ x := by linarith
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hx1 : 0 < 1 + x := by positivity
  have hp2 : 1 + q ≤ (1 + x) ^ 2 := by nlinarith [sq_nonneg x]
  have hfirst : Real.log (1 + q) ≤ 2 * Real.log (1 + x) := by
    have hh := Real.log_le_log (by positivity : 0 < 1 + q) hp2
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hq2 : q ^ 2 ≤ 4 * x ^ 2 := by
    have hh : q ^ 2 ≤ (2 * x) ^ 2 := pow_le_pow_left₀ hq0.le hqx 2
    nlinarith
  have hp3 : 2 * q ^ 2 + 4 ≤ (1 + x) ^ 3 := by
    nlinarith [mul_nonneg (show 0 ≤ x - 16 by linarith) (sq_nonneg x)]
  have hlast : Real.log (2 * q ^ 2 + 4) ≤ 3 * Real.log (1 + x) := by
    have hh := Real.log_le_log (by positivity : 0 < 2 * q ^ 2 + 4) hp3
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  exact ⟨hfirst, (Real.log_le_log hq0 (by linarith : q ≤ 1 + q)).trans hfirst,
    hlast⟩

/-- The damping exponent across the outer block is exactly the reciprocal
of its slowly growing weight, so its exponential cost is bounded. -/
theorem candidateScheduleWhiteTime_eventually_damping_bound
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop,
      Real.exp (2 * candidateScheduleD κ T / candidateScheduleWhiteTime κ T) ≤
        Real.exp 2 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (candidateScheduleW_tendsto hκ).eventually_ge_atTop 1] with T hT hW
  have hW0 : 0 < candidateScheduleW κ T := by linarith
  apply Real.exp_le_exp.mpr
  rw [mul_div_assoc, candidateScheduleD_div_whiteTime hT.ne' hW0.ne']
  have hh : 1 / candidateScheduleW κ T ≤ 1 :=
    (div_le_iff₀ hW0).mpr (by simpa using hW)
  linarith

end
end Erdos.Problem1144
