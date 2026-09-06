import Erdos.Problem1144.HarperCandidateCovarianceRetainedDeletion
import Erdos.Problem1144.HarperCandidateCovarianceDeletionScheduleGeometry

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

private theorem prefactor_bounds {C x r L θ : ℝ}
    (hC : 0 ≤ C) (hx : 0 ≤ x) (hr : 0 ≤ r) (hL : 0 ≤ L) (hθ : 1 ≤ θ)
    (hxb : x ≤ L * θ) (hrb : r ≤ L * θ) :
    candidateEulerDeletionPrefactor C x r ≤
      (Real.exp 2 * 524288 * (L + 2 * C + 6) ^ 4) * θ ^ 4 ∧
    candidateEulerTerminalDeletionPrefactor C x r ≤
      (Real.exp 2 * 8192 * (L + 2 * C + 6) ^ 3) * θ ^ 3 := by
  have hθ0 : 0 ≤ θ := by linarith
  have hb₁ : x + C + 4 ≤ (L + 2 * C + 6) * θ := by nlinarith
  have hb₂ : r + 2 * C + 6 ≤ (L + 2 * C + 6) * θ := by nlinarith
  have hb₃ : r + 2 * C + 4 ≤ (L + 2 * C + 6) * θ := by nlinarith
  constructor
  · unfold candidateEulerDeletionPrefactor
    calc
      _ ≤ Real.exp 2 * 524288 * ((L + 2 * C + 6) * θ) *
          ((L + 2 * C + 6) * θ) ^ 2 * ((L + 2 * C + 6) * θ) := by gcongr
      _ = _ := by ring
  · unfold candidateEulerTerminalDeletionPrefactor
    calc
      _ ≤ Real.exp 2 * 8192 * ((L + 2 * C + 6) * θ) *
          ((L + 2 * C + 6) * θ) * ((L + 2 * C + 6) * θ) := by gcongr
      _ = _ := by ring

/-- Natural midpoint and one-third rounding retain the inverse-length
factor in the literal interior ballot deletion bound. -/
theorem candidate_midpoint_deletion_ratio_le {N : ℕ} (hN : 12 ≤ N) :
    2 * Real.sqrt (N : ℝ) / (Real.sqrt ((N / 2 / 3 : ℕ) : ℝ)) ^ 3 ≤
      128 / (N : ℝ) := by
  let a : ℕ := N / 2 / 3
  have ha : 0 < a := by dsimp only [a]; omega
  have hna : (N : ℝ) ≤ 16 * (a : ℝ) := by
    exact_mod_cast (show N ≤ 16 * a by dsimp only [a]; omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hsq := Real.sq_sqrt ha0.le
  have hs : Real.sqrt (N : ℝ) ≤ 4 * Real.sqrt (a : ℝ) := by
    simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), show Real.sqrt (16 : ℝ) = 4 by norm_num] using
      Real.sqrt_le_sqrt hna
  have hm := mul_le_mul_of_nonneg_left hna (Real.sqrt_nonneg (a : ℝ))
  change 2 * Real.sqrt (N : ℝ) / (Real.sqrt (a : ℝ)) ^ 3 ≤ 128 / (N : ℝ)
  apply (div_le_div_iff₀ (pow_pos (Real.sqrt_pos.mpr ha0) _) hN0).mpr
  have hp := mul_le_mul_of_nonneg_right hs hN0.le
  have hcube : Real.sqrt (a : ℝ) ^ 3 = (a : ℝ) * Real.sqrt (a : ℝ) := by
    rw [pow_succ, hsq]
  rw [hcube]
  linarith

/-- The terminal strip has at least the same inverse-length decay. This
weaker bound is sufficient to combine it with the interior deletion cost. -/
theorem candidate_terminal_deletion_ratio_le {N : ℕ} (hN : 12 ≤ N) :
    1 / (Real.sqrt ((N / 3 : ℕ) : ℝ)) ^ 3 ≤ 4 / (N : ℝ) := by
  let a : ℕ := N / 3
  have ha : 1 ≤ a := by dsimp only [a]; omega
  have hna : (N : ℝ) ≤ 4 * (a : ℝ) := by
    exact_mod_cast (show N ≤ 4 * a by dsimp only [a]; omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  have hsq := Real.sq_sqrt ha0.le
  have hs : 1 ≤ Real.sqrt (a : ℝ) := Real.one_le_sqrt.mpr ha1
  change 1 / (Real.sqrt (a : ℝ)) ^ 3 ≤ 4 / (N : ℝ)
  apply (div_le_div_iff₀ (pow_pos (Real.sqrt_pos.mpr ha0) _) hN0).mpr
  have hm := mul_le_mul_of_nonneg_right hs ha0.le
  nlinarith [hsq]

/-- Both literal Euler approximation prefactors grow at most as the
fourth power of `log log T` on the actual rounded start. -/
theorem candidate_exists_scheduledDeletion_prefactor_bound (C : ℝ) (hC : 0 ≤ C)
    (J : ℕ) : ∃ K > 0, ∀ᶠ T : ℝ in atTop,
    let x := Real.log (Real.log (Problem520.harperBlockEndpoint
      (candidateCovarianceScheduleStart J T) : ℝ)) + 7 * Real.log (Real.log T)
    let r := Real.log (Real.log (Problem520.harperBlockEndpoint
      (candidateCovarianceScheduleStart J T) : ℝ)) + 1013 * Real.log (Real.log T)
    candidateEulerDeletionPrefactor C x r ≤ K * Real.log (Real.log T) ^ 4 ∧
      candidateEulerTerminalDeletionPrefactor C x r ≤ K * Real.log (Real.log T) ^ 4 := by
  let L := (J : ℝ) * Real.log 2 + 1015
  let K := Real.exp 2 * 524288 * (L + 2 * C + 6) ^ 4
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hq2 : Tendsto (fun T : ℝ => Real.log T ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  filter_upwards [(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_gt_atTop 0,
    hq2.eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ))]
    with T hθ hq hbase
  let θ := Real.log (Real.log T)
  change 1 ≤ θ at hθ
  let b := Real.log (Real.log (Problem520.harperBlockEndpoint
    (candidateCovarianceScheduleStart J T) : ℝ))
  have hb0 : 0 ≤ b := Real.log_nonneg (Problem520.one_le_log_harperBlockEndpoint _)
  have hb : b ≤ ((J : ℝ) * Real.log 2 + 2) * θ := by
    have hh := Real.log_le_log (lt_of_lt_of_le (by norm_num)
      (Problem520.one_le_log_harperBlockEndpoint _))
      (candidate_covarianceSchedule_start_log_bounds J hbase).2
    rw [Real.log_mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hq.ne'),
      Real.log_pow, Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    change b ≤ (J : ℝ) * Real.log 2 + 2 * θ at hh
    have hn : 0 ≤ (J : ℝ) * Real.log 2 := by positivity
    change 1 ≤ θ at hθ
    nlinarith
  have hx : b + 7 * θ ≤ L * θ := by dsimp only [L]; nlinarith
  have hr : b + 1013 * θ ≤ L * θ := by dsimp only [L]; nlinarith
  obtain ⟨h₁, h₂⟩ := prefactor_bounds hC (by positivity : 0 ≤ b + 7 * θ)
    (by positivity : 0 ≤ b + 1013 * θ) hL hθ hx hr
  refine ⟨h₁, h₂.trans ?_⟩
  have hbase1 : 1 ≤ L + 2 * C + 6 := by linarith
  have hθ0 : 0 ≤ θ := by linarith
  have ht : θ ^ 3 ≤ θ ^ 4 := pow_le_pow_right₀ hθ (by omega)
  have hp : (L + 2 * C + 6) ^ 3 ≤ (L + 2 * C + 6) ^ 4 :=
    pow_le_pow_right₀ hbase1 (by omega)
  dsimp only [K]
  gcongr
  norm_num

end
end Erdos.Problem1144
