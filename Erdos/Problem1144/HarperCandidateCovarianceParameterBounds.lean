import Erdos.Problem1144.HarperCandidateCovarianceParameterGeometry

open Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- Simultaneous numerical bounds for the actual rounded parameters.
The logarithmic product bounds retain the required polynomial powers. -/
theorem candidate_eventually_covarianceSchedule_scalar_bounds (J : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      let q := Real.log T
      let A := Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T) : ℝ)
      let L := Real.log (candidateEulerTopCutoff T : ℝ)
      let M := (candidateCovarianceScheduleHeight T : ℝ)
      1 ≤ q ∧ 0 < T ∧ 0 ≤ A ∧ 0 ≤ L ∧ 0 ≤ M ∧
      A ≤ (2 : ℝ) ^ J * q ^ 2 ∧ L ≤ T ∧ M ≤ 2 * q ^ 2 ∧
      1 / candidateCovarianceScheduleLowerHeight T ≤ 2 * q ^ 2 ∧
      q ^ 2 ≤ T ^ ((3 : ℝ) / 4) ∧ 2 * M ≤ T ∧
      Real.log (1 + 2 * T * M) ≤ 3 * q ∧
      Real.log (1 + 2 * L * M) ≤ 3 * q ∧
      A * (2 * M) + 3 * Real.log (1 + L * (2 * M)) ≤
        (4 * (2 : ℝ) ^ J + 9) * q ^ 4 := by
  have hq : Tendsto (fun T : ℝ => Real.log T ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  have hsmall := Real.isLittleO_pow_log_id_atTop (n := 2) |>.tendsto_div_nhds_zero
  have hsmallpow := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (s := (3 : ℝ) / 4) (by norm_num)).tendsto_div_nhds_zero
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)),
    hq.eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)),
    (tendsto_order.mp hsmall).2 (1 / 4) (by norm_num),
    (tendsto_order.mp hsmallpow).2 1 (by norm_num)] with T hlog hT2 hTbase hqbase hs hp
  let q := Real.log T
  let A := Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T) : ℝ)
  let L := Real.log (candidateEulerTopCutoff T : ℝ)
  let M := (candidateCovarianceScheduleHeight T : ℝ)
  have hT : 0 < T := by linarith
  have hAn : 0 ≤ A := zero_le_one.trans (Problem520.one_le_log_harperBlockEndpoint _)
  have hLn : 0 ≤ L := zero_le_one.trans (Problem520.one_le_log_harperBlockEndpoint _)
  have hMn : 0 ≤ M := Nat.cast_nonneg _
  have hA : A ≤ (2 : ℝ) ^ J * q ^ 2 :=
    (candidate_covarianceSchedule_start_log_bounds J hqbase).2
  have hL : L ≤ T := (candidateEulerTopCutoff_log_bounds hTbase).2
  have hM : M ≤ 2 * q ^ 2 := by
    have hh := (candidate_covarianceSchedule_height_bounds T).2
    change M < q ^ 2 + 1 at hh
    change 1 ≤ q at hlog
    nlinarith
  have htime : 2 * M ≤ T := by
    change q ^ 2 / T < 1 / 4 at hs
    have hh := (div_lt_iff₀ hT).mp hs
    linarith
  have hpow : q ^ 2 ≤ T ^ ((3 : ℝ) / 4) := by
    norm_num only [Real.rpow_ofNat] at hp
    simpa only [one_mul] using ((div_lt_iff₀ (Real.rpow_pos_of_pos hT _)).mp hp).le
  have hlogBound (V : ℝ) (hVn : 0 ≤ V) (hVT : V ≤ T) :
      Real.log (1 + 2 * V * M) ≤ 3 * q := by
    have hm : 2 * V * M ≤ T ^ 2 := by
      have hv := mul_le_mul_of_nonneg_right hVT (show 0 ≤ 2 * M by positivity)
      have ht := mul_le_mul_of_nonneg_left htime hT.le
      nlinarith
    have hh : Real.log (1 + 2 * V * M) ≤ Real.log (2 * T ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hT.ne'), Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT2
    dsimp only [q]
    linarith
  have hlogT := hlogBound T hT.le le_rfl
  have hlogL := hlogBound L hLn hL
  have hU : A * (2 * M) + 3 * Real.log (1 + L * (2 * M)) ≤
      (4 * (2 : ℝ) ^ J + 9) * q ^ 4 := by
    have hpAM := mul_le_mul hA (show 2 * M ≤ 4 * q ^ 2 by linarith) (by positivity)
      (by positivity)
    have hq4 : q ≤ q ^ 4 := by
      change 1 ≤ q at hlog
      have hq2 : 1 ≤ q ^ 2 := by nlinarith
      nlinarith [sq_nonneg (q ^ 2 - 1)]
    rw [show L * (2 * M) = 2 * L * M by ring]
    nlinarith
  exact ⟨hlog, hT, hAn, hLn, hMn, hA, hL, hM,
    candidate_covarianceSchedule_lowerHeight_inv_le hqbase, hpow, htime, hlogT, hlogL, hU⟩

end
end Erdos.Problem1144
