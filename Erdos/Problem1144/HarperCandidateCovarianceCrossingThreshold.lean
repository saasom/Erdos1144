import Erdos.Problem1144.HarperCandidateGaussianVarianceAsymptotics

open Filter
open scoped Topology

namespace Erdos.Problem1144

/-- The scheduled covariance threshold is eventually below half the retained
variance floor, including every fixed positive cylinder-dependent coefficient. -/
theorem candidate_eventually_covarianceThreshold_le_retained_half_variance
    {v : ℝ} (hv : 0 < v) :
    ∀ᶠ T : ℝ in atTop, (Real.log T) ^ (-(3 : ℝ) / 5) ≤
      (v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / 8 := by
  have hz : Tendsto (fun T : ℝ => (2 : ℝ) ^ ((1 : ℝ) / 2) *
      Real.log T ^ (-(1 : ℝ) / 10)) atTop (nhds 0) := by
    have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      Real.tendsto_log_atTop).const_mul ((2 : ℝ) ^ ((1 : ℝ) / 2))
    convert h using 1 <;> norm_num
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (tendsto_order.mp hz).2 (v / 8) (by positivity)] with T hq hsmall
  let q := Real.log T
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hx : 0 < 1 + q := by linarith
  have hb : q ^ (-(3 : ℝ) / 5) * (1 + q) ^ ((1 : ℝ) / 2) ≤
      (2 : ℝ) ^ ((1 : ℝ) / 2) * q ^ (-(1 : ℝ) / 10) := by
    calc
      _ ≤ q ^ (-(3 : ℝ) / 5) * (2 * q) ^ ((1 : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hq0.le _)
        exact Real.rpow_le_rpow hx.le (by dsimp [q]; linarith) (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hq0.le]
        rw [show q ^ (-(3 : ℝ) / 5) *
          ((2 : ℝ) ^ ((1 : ℝ) / 2) * q ^ ((1 : ℝ) / 2)) =
          (2 : ℝ) ^ ((1 : ℝ) / 2) *
            (q ^ (-(3 : ℝ) / 5) * q ^ ((1 : ℝ) / 2)) by ring,
          ← Real.rpow_add hq0]
        norm_num
  have hdiv := (le_div_iff₀ (Real.rpow_pos_of_pos hx ((1 : ℝ) / 2))).mpr
    (hb.trans hsmall.le)
  have he : (v / 8) / (1 + q) ^ ((1 : ℝ) / 2) =
      v * (1 + q) ^ (-(1 : ℝ) / 2) / 8 := by
    rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hx.le]
    ring
  exact hdiv.trans_eq he

end Erdos.Problem1144
