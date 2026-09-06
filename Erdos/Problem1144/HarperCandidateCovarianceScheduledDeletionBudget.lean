import Erdos.Problem1144.HarperCandidateCovarianceDeletionScalar

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- The inclusive midpoint-to-terminal screen on the actual rounded path. -/
def candidateCovarianceScheduleSelected (J : ℕ) (T : ℝ) : Finset ℕ :=
  Finset.Icc (candidateCovarianceScheduleLength J T / 2)
    (candidateCovarianceScheduleLength J T)

/-- The actual printed interior and terminal budgets decay at the required
fourth-iterated-log over logarithm rate. Terminal-prefix deletion is included. -/
theorem candidate_exists_scheduledDeletionBudget_le (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (J : ℕ) : ∃ K > 0, ∀ᶠ T : ℝ in atTop,
    let N := candidateCovarianceScheduleLength J T
    candidateCovarianceFrequencyDeletionBudget C (Real.log T)
      (candidateCovarianceScheduleStart J T) N (N / 2)
      ((candidateCovarianceScheduleSelected J T).erase N) +
    candidateCovarianceTerminalDeletionBudget D (Real.log T)
      (candidateCovarianceScheduleStart J T) N ≤
        K * Real.log (Real.log T) ^ 4 / Real.log T := by
  obtain ⟨P, hP, hp⟩ := candidate_exists_scheduledDeletion_prefactor_bound C hC J
  obtain ⟨Q, hQ, hq⟩ := candidate_exists_scheduledDeletion_prefactor_bound D hD J
  let A := Real.exp (16 * (1 + (Real.log 4 + 4) / Real.log 2)) + 1
  let U := 1 / Real.log 2 + 1
  let V := 2 * Real.log 2
  let R := 2 * Real.log (Problem520.harperBlockEndpoint 0 : ℝ)
  let K := A * U + 128 * P * V + 64 * U * R + 4 * Q * V + 64 * R
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hU : 0 < U := by dsimp only [U]; positivity
  have hV : 0 < V := by dsimp only [V]; positivity
  have hR : 0 < R := by
    have := Problem520.one_le_log_harperBlockEndpoint 0
    dsimp only [R]; linarith
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  have hq2 : Tendsto (fun T : ℝ => Real.log T ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  filter_upwards [hp, hq, candidate_eventually_covarianceSchedule_length_log_bounds J,
    (candidate_covarianceSchedule_length_tendsto J).eventually_ge_atTop 12,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    hq2.eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ))]
    with T hpT hqT hNlog hN hq1 hθ1 hbase
  let q := Real.log T
  let θ := Real.log q
  let N := candidateCovarianceScheduleLength J T
  let start := candidateCovarianceScheduleStart J T
  let s := (candidateCovarianceScheduleSelected J T).erase N
  let x := Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 7 * θ
  let r := Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 1013 * θ
  change 1 ≤ q at hq1
  change 1 ≤ θ at hθ1
  change 12 ≤ N at hN
  change q / 2 ≤ (N : ℝ) * Real.log 2 ∧ (N : ℝ) * Real.log 2 ≤ q at hNlog
  change candidateEulerDeletionPrefactor C x r ≤ P * θ ^ 4 ∧ _ at hpT
  change _ ∧ candidateEulerTerminalDeletionPrefactor D x r ≤ Q * θ ^ 4 at hqT
  have hq0 : 0 < q := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hθ4 : 1 ≤ θ ^ 4 := one_le_pow₀ hθ1
  have hNp : (N + 1 : ℕ) ≤ U * q := by
    have hh := (le_div_iff₀ hlog2).mpr hNlog.2
    rw [Nat.cast_add, Nat.cast_one]
    dsimp only [U]
    simp only [div_eq_mul_inv, one_mul] at hh ⊢
    nlinarith
  have hNi : 1 / (N : ℝ) ≤ V / q := by
    apply (div_le_div_iff₀ hN0 hq0).mpr
    dsimp only [V]
    nlinarith [hNlog.1]
  have hdy : (1 / 2 : ℝ) ^ start ≤ R / q ^ 2 :=
    candidate_covarianceSchedule_dyadic_le J hq0 hbase
  have hcard : (s.card : ℝ) ≤ (N + 1 : ℕ) := by
    have hh : s ⊆ Finset.range (N + 1) := by
      intro j hj
      have hj' := (Finset.mem_erase.mp hj).2
      have hjN : j ≤ N := (Finset.mem_Icc.mp hj').2
      exact Finset.mem_range.mpr (by omega)
    exact_mod_cast (Finset.card_le_card hh).trans_eq (Finset.card_range _)
  have hmesh : A * (N + 1 : ℕ) / q ^ 2 ≤ (A * U) * θ ^ 4 / q := by
    calc
      _ ≤ A * (U * q) / q ^ 2 := by gcongr
      _ = A * U / q := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (by positivity) hθ4) hq0.le
  have hratio : 2 * Real.sqrt (N : ℝ) / Real.sqrt ((N / 2 / 3 : ℕ) : ℝ) ^ 3 ≤
      (128 * V) / q := by
    apply (candidate_midpoint_deletion_ratio_le hN).trans
    convert mul_le_mul_of_nonneg_left hNi (by norm_num : (0 : ℝ) ≤ 128) using 1 <;> ring
  have hint : candidateEulerDeletionPrefactor C x r *
      (2 * Real.sqrt (N : ℝ) / Real.sqrt ((N / 2 / 3 : ℕ) : ℝ) ^ 3) ≤
      (128 * P * V) * θ ^ 4 / q := by
    calc
      _ ≤ (P * θ ^ 4) * ((128 * V) / q) :=
        mul_le_mul hpT.1 hratio (by positivity) (by positivity)
      _ = _ := by ring
  have hcarddy : (s.card : ℝ) * (64 * (1 / 2 : ℝ) ^ start) ≤
      (64 * U * R) * θ ^ 4 / q := by
    calc
      _ ≤ (U * q) * (64 * (R / q ^ 2)) := by
        apply mul_le_mul (hcard.trans hNp) _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hdy (by norm_num)
      _ = 64 * U * R / q := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (by positivity) hθ4) hq0.le
  have htratio : 1 / Real.sqrt ((N / 3 : ℕ) : ℝ) ^ 3 ≤ (4 * V) / q := by
    apply (candidate_terminal_deletion_ratio_le hN).trans
    convert mul_le_mul_of_nonneg_left hNi (by norm_num : (0 : ℝ) ≤ 4) using 1 <;> ring
  have hterm : candidateEulerTerminalDeletionPrefactor D x r /
      Real.sqrt ((N / 3 : ℕ) : ℝ) ^ 3 ≤ (4 * Q * V) * θ ^ 4 / q := by
    calc
      _ = candidateEulerTerminalDeletionPrefactor D x r *
        (1 / Real.sqrt ((N / 3 : ℕ) : ℝ) ^ 3) := by ring
      _ ≤ (Q * θ ^ 4) * ((4 * V) / q) :=
        mul_le_mul hqT.2 htratio (by positivity) (by positivity)
      _ = _ := by ring
  have hsmall : 64 * (1 / 2 : ℝ) ^ start ≤ (64 * R) * θ ^ 4 / q := by
    calc
      _ ≤ 64 * (R / q ^ 2) := mul_le_mul_of_nonneg_left hdy (by norm_num)
      _ ≤ 64 * (R / q) := by gcongr; nlinarith
      _ = 64 * R / q := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (by positivity) hθ4) hq0.le
  change candidateCovarianceFrequencyDeletionBudget C q start N (N / 2) s +
    candidateCovarianceTerminalDeletionBudget D q start N ≤ K * θ ^ 4 / q
  unfold candidateCovarianceFrequencyDeletionBudget candidateCovarianceTerminalDeletionBudget
  change A * (N + 1 : ℕ) / q ^ 2 +
      (candidateEulerDeletionPrefactor C x r *
        (2 * Real.sqrt (N : ℝ) / Real.sqrt ((N / 2 / 3 : ℕ) : ℝ) ^ 3) +
        (s.card : ℝ) * (64 * (1 / 2 : ℝ) ^ start)) +
      (candidateEulerTerminalDeletionPrefactor D x r /
        Real.sqrt ((N / 3 : ℕ) : ℝ) ^ 3 + 64 * (1 / 2 : ℝ) ^ start) ≤ _
  calc
    _ ≤ (A * U) * θ ^ 4 / q + ((128 * P * V) * θ ^ 4 / q +
        (64 * U * R) * θ ^ 4 / q) +
        ((4 * Q * V) * θ ^ 4 / q + (64 * R) * θ ^ 4 / q) := by linarith
    _ = _ := by dsimp only [K]; ring

end
end Erdos.Problem1144
