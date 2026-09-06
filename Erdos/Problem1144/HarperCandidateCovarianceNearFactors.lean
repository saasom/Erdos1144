import Erdos.Problem1144.HarperCandidateCovarianceParameterBounds
import Erdos.Problem1144.HarperCandidateCovarianceGapMoment

open Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- The actual rounded order is much smaller than `log T`, so the
interaction logarithm is bounded without doubling its leading coefficient. -/
theorem candidate_eventually_covarianceSchedule_small_order :
    ∀ᶠ T : ℝ in atTop,
      1 ≤ candidateCovarianceScheduleOrder T ∧
      4 * (candidateCovarianceScheduleOrder T : ℝ) ≤ Real.log T ∧
      2 * (candidateCovarianceScheduleOrder T : ℝ) + 1 ≤ Real.log T := by
  filter_upwards [candidate_covarianceSchedule_order_tendsto.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with T hk hq hlogq
  change 1 ≤ Real.log (Real.log T) at hlogq
  have hu : 0 ≤ Real.log T / (4000 * Real.log (Real.log T)) := by positivity
  have hf := Nat.floor_le hu
  change (candidateCovarianceScheduleOrder T : ℝ) ≤
    Real.log T / (4000 * Real.log (Real.log T)) at hf
  have hden : 0 < 4000 * Real.log (Real.log T) := by positivity
  have hmul := (le_div_iff₀ hden).mp hf
  have hk0 : (0 : ℝ) ≤ candidateCovarianceScheduleOrder T := Nat.cast_nonneg _
  have h4 : 4 * (candidateCovarianceScheduleOrder T : ℝ) ≤ Real.log T := by
    nlinarith
  exact ⟨hk, h4, by linarith⟩

/-- The squared-log initial cutoff eventually dominates the moment order. -/
theorem candidate_eventually_covarianceSchedule_log_start_ge_log (J : ℕ) :
    ∀ᶠ T : ℝ in atTop, Real.log T ≤
      Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T) : ℝ) := by
  have hq : Tendsto (fun T : ℝ => Real.log T ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 2,
    hq.eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ))] with T hlog hqT
  have hb := (candidate_covarianceSchedule_start_log_bounds J hqT).1
  have hh := mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := J))
    (show 0 ≤ Real.log T ^ 2 / 2 by positivity)
  nlinarith

/-- An explicit power bound for the actual mixed-Euler interaction factor.
The exponent 69 consists of 64 interaction powers, two normalizer powers,
two fixed linear-error powers, and one PNT-error power. -/
theorem candidate_eventually_covarianceSchedule_gapMomentFactor_le
    (C D : ℝ) (hC : 0 ≤ C) (J : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      candidateCovarianceGapMomentFactor C D (candidateCovarianceScheduleStart J T)
        (2 * candidateCovarianceScheduleOrder T) ≤
          Real.log T ^ (69 * candidateCovarianceScheduleOrder T) := by
  let c₀ : ℝ := 4 * Real.log 4 + 8 / 3
  filter_upwards [candidate_eventually_covarianceSchedule_small_order,
    candidate_eventually_covarianceSchedule_log_start_ge_log J,
    Real.tendsto_log_atTop.eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop (max 1 D),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp c₀),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp (8 * C))]
    with T hk hA hq hD hlin herror
  let k := candidateCovarianceScheduleOrder T
  let q := Real.log T
  let A := Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T) : ℝ)
  have hk1 : 1 ≤ k := hk.1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hq1 : 1 ≤ q := by dsimp only [q]; linarith
  have hq0 : 0 < q := by dsimp only [q]; linarith
  have hA0 : 0 < A := hq0.trans_le hA
  have hkA : (k : ℝ) ≤ A := by dsimp only [k] at *; linarith [hk.2.1]
  have hki : (k : ℝ) / A ≤ 1 := (div_le_one hA0).mpr hkA
  have hkisq : ((k : ℝ) / A) ^ 2 ≤ 1 := by
    have hn : 0 ≤ (k : ℝ) / A := div_nonneg hk0 hA0.le
    nlinarith
  have hE : 2 * C * ((2 * k : ℕ) : ℝ) ^ 2 *
      Problem520.invLog (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T)) ^ 2 ≤
        8 * C := by
    have hh := mul_le_mul_of_nonneg_left hkisq (show 0 ≤ 8 * C by positivity)
    convert hh using 1 <;> dsimp only [A, Problem520.invLog] <;> push_cast <;> ring
  have herr : Real.exp (2 * C * ((2 * k : ℕ) : ℝ) ^ 2 *
      Problem520.invLog (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T)) ^ 2) ≤
        q ^ k := by
    exact ((Real.exp_le_exp.mpr hE).trans herror).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hq1 hk1)
  have hnormal : (max 1 D) ^ (2 * k) ≤ q ^ (2 * k) :=
    pow_le_pow_left₀ ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)) hD _
  have hlinear : Real.exp (c₀ * ((2 * k : ℕ) : ℝ)) ≤ q ^ (2 * k) := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos c₀).le hlin _
  have hinteraction : Real.exp (32 * ((2 * k : ℕ) : ℝ) *
      Real.log (((2 * k : ℕ) : ℝ) + 1)) ≤ q ^ (64 * k) := by
    have hlog : Real.log (((2 * k : ℕ) : ℝ) + 1) ≤ Real.log q :=
      Real.log_le_log (by positivity) (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hk.2.2)
    have hh := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hlog (show 0 ≤ 32 * ((2 * k : ℕ) : ℝ) by positivity))
    apply hh.trans_eq
    rw [show 32 * ((2 * k : ℕ) : ℝ) * Real.log q = ((64 * k : ℕ) : ℝ) * Real.log q by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log hq0]
  unfold candidateCovarianceGapMomentFactor
  change (max 1 D) ^ (2 * k) * Real.exp (c₀ * ((2 * k : ℕ) : ℝ) +
    32 * ((2 * k : ℕ) : ℝ) * Real.log (((2 * k : ℕ) : ℝ) + 1) +
    2 * C * ((2 * k : ℕ) : ℝ) ^ 2 *
      Problem520.invLog (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T)) ^ 2) ≤ _
  rw [Real.exp_add, Real.exp_add]
  calc
    _ ≤ q ^ (2 * k) * (q ^ (2 * k) * q ^ (64 * k) * q ^ k) := by gcongr
    _ = q ^ (69 * k) := by simp only [← pow_add]; congr 1; omega

end
end Erdos.Problem1144
