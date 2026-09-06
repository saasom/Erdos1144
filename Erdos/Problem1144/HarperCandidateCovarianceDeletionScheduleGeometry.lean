import Erdos.Problem1144.HarperCandidateCovarianceParameterBounds

open Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- Exact affine dependence of the iterated logarithm on the block index. -/
theorem candidate_log_log_blockEndpoint (j : ℕ) :
    Real.log (Real.log (Problem520.harperBlockEndpoint j : ℝ)) =
      (j : ℝ) * Real.log 2 +
        Real.log (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)) := by
  have hb : 0 < Real.log (Problem520.harperBlockEndpoint 0 : ℝ) :=
    lt_of_lt_of_le (by norm_num) (Problem520.one_le_log_harperBlockEndpoint 0)
  have he := candidate_schedule_log_block_add j 0
  simp only [Nat.add_zero] at he
  rw [he, Real.log_mul (pow_ne_zero _ (by norm_num)) hb.ne', Real.log_pow]

/-- The actual rounded remaining path has length comparable to `log T`.
The fixed analytic offset does not cost an extra logarithm. -/
theorem candidate_eventually_covarianceSchedule_length_log_bounds (J : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      Real.log T / 2 ≤ (candidateCovarianceScheduleLength J T : ℝ) * Real.log 2 ∧
      (candidateCovarianceScheduleLength J T : ℝ) * Real.log 2 ≤ Real.log T := by
  let D := (J : ℝ) * Real.log 2 + Real.log 2
  have hs : Tendsto (fun q : ℝ => D / q + 2 * (Real.log q / q)) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun q : ℝ => D / q) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h₂ := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul 2
    simpa only [zero_add, mul_zero] using h₁.add h₂
  have hq2 : Tendsto (fun T : ℝ => Real.log T ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)),
    Real.tendsto_log_atTop.eventually_gt_atTop 1,
    hq2.eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)),
    candidate_eventually_covarianceSchedule_room J 0,
    Real.tendsto_log_atTop.eventually ((tendsto_order.mp hs).2 (1 / 2) (by norm_num))]
    with T hT hq hqbase hroom hsmall
  let q := Real.log T
  let start := candidateCovarianceScheduleStart J T
  let N := candidateCovarianceScheduleLength J T
  have hST : start ≤ candidateEulerTopIndex T := by simpa [start] using hroom
  have hsum : start + N = candidateEulerTopIndex T := by
    dsimp only [N, start, candidateCovarianceScheduleLength]
    omega
  have hq0 : 0 < q := by dsimp only [q]; linarith
  have hlo := (candidateEulerTopCutoff_log_bounds hT).1
  have hhi := (candidateEulerTopCutoff_log_bounds hT).2
  have hA := (candidate_covarianceSchedule_start_log_bounds J hqbase).2
  have hT0 : 0 < T :=
    (lt_of_lt_of_le (by norm_num) (Problem520.one_le_log_harperBlockEndpoint 0)).trans_le hT
  have hLo : q - Real.log 2 <
      Real.log (Real.log (candidateEulerTopCutoff T : ℝ)) := by
    have hh := Real.log_lt_log (by positivity : 0 < T / 2) hlo
    simpa only [Real.log_div hT0.ne' (by norm_num : (2 : ℝ) ≠ 0), q] using hh
  have hHi : Real.log (Real.log (candidateEulerTopCutoff T : ℝ)) ≤ q :=
    Real.log_le_log (lt_of_lt_of_le (by norm_num)
      (Problem520.one_le_log_harperBlockEndpoint _)) hhi
  have hAi : Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) ≤
      (J : ℝ) * Real.log 2 + 2 * Real.log q := by
    have hh := Real.log_le_log (lt_of_lt_of_le (by norm_num)
      (Problem520.one_le_log_harperBlockEndpoint start)) hA
    rw [Real.log_mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hq0.ne'),
      Real.log_pow, Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hAn : 0 ≤ Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) :=
    Real.log_nonneg (Problem520.one_le_log_harperBlockEndpoint start)
  have he : Real.log (Real.log (candidateEulerTopCutoff T : ℝ)) =
      (N : ℝ) * Real.log 2 +
        Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) := by
    unfold candidateEulerTopCutoff
    rw [← hsum, candidate_log_log_blockEndpoint (start + N),
      candidate_log_log_blockEndpoint start, Nat.cast_add]
    ring
  have hs' : D + 2 * Real.log q < q / 2 := by
    change D / q + 2 * (Real.log q / q) < 1 / 2 at hsmall
    have hh := (div_lt_iff₀ hq0).mp (show (D + 2 * Real.log q) / q < 1 / 2 by
      convert hsmall using 1 <;> ring)
    linarith
  rw [he] at hLo hHi
  dsimp only [D] at hs'
  exact ⟨by change q / 2 ≤ (N : ℝ) * Real.log 2; linarith,
    by change (N : ℝ) * Real.log 2 ≤ q; linarith⟩

/-- Exact depth rounding gives an inverse-square logarithmic upper bound
for the dyadic error at the scheduled initial block. -/
theorem candidate_covarianceSchedule_dyadic_le (J : ℕ) {T : ℝ}
    (hq : 0 < Real.log T)
    (hbase : Real.log (Problem520.harperBlockEndpoint 0 : ℝ) ≤ Real.log T ^ 2) :
    (1 / 2 : ℝ) ^ candidateCovarianceScheduleStart J T ≤
      (2 * Real.log (Problem520.harperBlockEndpoint 0 : ℝ)) / Real.log T ^ 2 := by
  have hd := (candidateEulerTopCutoff_log_bounds hbase).1
  have he := candidate_schedule_log_block_add (candidateCovarianceScheduleDepth T) 0
  simp only [Nat.add_zero] at he
  change Real.log T ^ 2 / 2 <
    Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleDepth T) : ℝ) at hd
  rw [he] at hd
  have hi : (1 / 2 : ℝ) ^ candidateCovarianceScheduleDepth T =
      1 / (2 : ℝ) ^ candidateCovarianceScheduleDepth T := by rw [div_pow, one_pow]
  have hmono : (1 / 2 : ℝ) ^ candidateCovarianceScheduleStart J T ≤
      (1 / 2 : ℝ) ^ candidateCovarianceScheduleDepth T :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by
      unfold candidateCovarianceScheduleStart; omega)
  apply hmono.trans
  rw [hi]
  apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hq)).mpr
  nlinarith

end
end Erdos.Problem1144
