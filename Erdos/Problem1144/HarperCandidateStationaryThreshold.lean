import Erdos.Problem1144.HarperCandidateScheduleThinning

open Filter
open scoped Topology

namespace Erdos.Problem1144

/-- The exact three-comparison threshold costs only the eighth power of
the iterated logarithm. The seventh power comes from the spectral factor;
one further power bounds the square root of the schedule weight. -/
theorem candidate_eventually_stationary_white_threshold_le_loglog_power
    {C κ β K : ℝ} (hC : 0 < C) (hκ : 0 < κ) (hβ : 0 < β) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop,
      (((Real.sqrt (β * Real.exp (2 * (candidateScheduleW κ T / T) *
        candidateScheduleD κ T)) * K + 1) /
          Real.sqrt (1 / (candidateScheduleW κ T *
            (C * Real.log (2 * Real.log T ^ 2 + 4) ^ 7) ^ 2)) + 1) /
              Real.exp (-(β - 1))) ≤ A * Real.log (1 + Real.log T) ^ 8 := by
  let B := Real.sqrt (β * Real.exp 2)
  let R := C * (κ + 1) * 4 ^ 7
  let A := ((B * K + 1) * R + 1) / Real.exp (-(β - 1))
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hR : 0 < R := by dsimp only [R]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  have hL : Tendsto (fun T : ℝ => Real.log (1 + Real.log T)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left atTop 1 Real.tendsto_log_atTop)
  refine ⟨A, hA, ?_⟩
  filter_upwards [(candidateScheduleW_tendsto hκ).eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop 3, hL.eventually_ge_atTop 1,
    eventually_gt_atTop (0 : ℝ)] with T hW1 hq3 hL1 hT
  let W := candidateScheduleW κ T
  let q := Real.log T
  let L := Real.log (1 + Real.log T)
  let H := Real.log (2 * Real.log T ^ 2 + 4)
  have hW : 0 < W := zero_lt_one.trans_le hW1
  have hq : 0 < q := by dsimp only [q]; linarith
  have hLn : 0 ≤ L := zero_le_one.trans hL1
  have hHn : 0 ≤ H := Real.log_nonneg (by nlinarith [sq_nonneg q])
  have hlog : Real.log q ≤ L := Real.log_le_log hq (by dsimp only [L, q]; linarith)
  have hWL : W ≤ κ * L := mul_le_mul_of_nonneg_left hlog hκ.le
  have hsW : Real.sqrt W ≤ (κ + 1) * L := by
    have hh : Real.sqrt W ≤ W + 1 := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by positivity, by nlinarith [sq_nonneg W]⟩
    nlinarith
  have hH : H ≤ 4 * L := by
    have hq2 : 6 ≤ q ^ 2 := by dsimp only [q]; nlinarith
    have hpoly : 2 * q ^ 2 + 4 ≤ q ^ 4 := by
      nlinarith [mul_nonneg (sq_nonneg q) (show 0 ≤ q ^ 2 - 6 by linarith)]
    have hh := Real.log_le_log (by positivity : 0 < 2 * q ^ 2 + 4) hpoly
    rw [Real.log_pow] at hh
    change H ≤ 4 * L
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hsched : 2 * (W / T) * candidateScheduleD κ T = 2 / W := by
    dsimp only [candidateScheduleD]
    change 2 * (W / T) * (T / W ^ 2) = 2 / W
    field_simp
  have he : Real.exp (2 * (W / T) * candidateScheduleD κ T) ≤ Real.exp 2 := by
    rw [hsched]
    apply Real.exp_le_exp.mpr
    exact (div_le_iff₀ hW).mpr (by linarith)
  have hsLam : Real.sqrt (β * Real.exp (2 * (W / T) * candidateScheduleD κ T)) ≤ B :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left he hβ.le)
  have hsC : 1 / Real.sqrt (1 / (W * (C * H ^ 7) ^ 2)) =
      Real.sqrt W * (C * H ^ 7) := by
    simp only [one_div, Real.sqrt_inv, inv_inv]
    rw [Real.sqrt_mul hW.le, Real.sqrt_sq (by positivity : 0 ≤ C * H ^ 7)]
  have hscale : 1 / Real.sqrt (1 / (W * (C * H ^ 7) ^ 2)) ≤ R * L ^ 8 := by
    rw [hsC]
    calc
      _ ≤ ((κ + 1) * L) * (C * (4 * L) ^ 7) := by gcongr
      _ = R * L ^ 8 := by dsimp only [R]; ring
  have hroot : 0 ≤ 1 / Real.sqrt (1 / (W * (C * H ^ 7) ^ 2)) := by positivity
  have hnum : 0 ≤ B * K + 1 := by positivity
  have hp : 1 ≤ L ^ 8 := one_le_pow₀ hL1
  change (((Real.sqrt (β * Real.exp (2 * (W / T) * candidateScheduleD κ T)) * K + 1) /
    Real.sqrt (1 / (W * (C * H ^ 7) ^ 2)) + 1) / Real.exp (-(β - 1))) ≤ A * L ^ 8
  have hn := mul_le_mul (add_le_add (mul_le_mul_of_nonneg_right hsLam hK) le_rfl)
    hscale hroot hnum
  rw [mul_one_div] at hn
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have hcancel : (A * L ^ 8) * Real.exp (-(β - 1)) =
      ((B * K + 1) * R + 1) * L ^ 8 := by dsimp only [A]; field_simp
  rw [hcancel]
  nlinarith

end Erdos.Problem1144
