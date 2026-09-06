import Erdos.Problem1144.HarperCandidatePrimeBins
import Erdos.Problem520.HarperMovingHeightMoments

open Set Filter Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace Erdos.Problem1144

noncomputable section

/-!
# Growing frequency windows for actual prime-block arithmetic

The strong-PNT exponent is `1/10`. Keeping half of it allows the frequency
window `exp((log B_start)^(1/20))`, while preserving summable arithmetic
errors. This avoids a starting threshold depending arbitrarily on a fixed
height bound, or a shift linear in its logarithm.
-/

/-- The frequency window supported by the retained strong-PNT error. -/
def candidateCovarianceHeightWindow (start : ℕ) : ℝ :=
  Real.exp ((Real.log (Problem520.harperBlockEndpoint start : ℝ)) ^ ((1 : ℝ) / 20))

private theorem eventually_weighted_theta_scalar_le {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (L ^ ((1 : ℝ) / 20)) *
        (C * Real.exp (-c * L ^ ((1 : ℝ) / 10)) + 4 * L / Real.exp (L / 2)) ≤
      (C + 1) / L ^ 2 := by
  have hfirst := candidate_tendsto_rpow_mul_exp_rpow_sub (2 : ℝ)
    (a := (1 : ℝ) / 10) (ν := (1 : ℝ) / 20) (by norm_num) (by norm_num) hc
  have hsecond := (candidate_tendsto_rpow_mul_exp_rpow_sub (3 : ℝ)
    (a := (1 : ℝ)) (ν := (1 : ℝ) / 20) (c := (1 : ℝ) / 2)
    (by norm_num) (by norm_num) (by norm_num)).const_mul 4
  filter_upwards [(tendsto_order.mp hfirst).2 1 (by norm_num),
    (tendsto_order.mp hsecond).2 1 (by norm_num), eventually_gt_atTop (0 : ℝ)]
    with L hfirst hsecond hL
  norm_num only [Real.rpow_ofNat, Real.rpow_one] at hfirst hsecond
  apply (le_div_iff₀ (sq_pos_of_pos hL)).2
  calc
    _ = C * (L ^ 2 * Real.exp (L ^ ((1 : ℝ) / 20) - c * L ^ ((1 : ℝ) / 10))) +
        4 * (L ^ 3 * Real.exp (L ^ ((1 : ℝ) / 20) - (1 / 2 : ℝ) * L)) := by
      rw [Real.exp_sub, Real.exp_sub, neg_mul, Real.exp_neg]
      rw [show L / 2 = (1 / 2 : ℝ) * L by ring]
      ring
    _ ≤ C * 1 + 1 := add_le_add (mul_le_mul_of_nonneg_left hfirst.le hC) hsecond.le
    _ = _ := by ring

/-- The strong-PNT envelope remains summably small after multiplication by
the growing height window. The threshold is independent of that height. -/
theorem candidate_eventually_heightWindow_mul_theta_le
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ j : ℕ in atTop,
      candidateCovarianceHeightWindow j * Problem520.harperScheduledThetaEnvelope c C j ≤
        (C + 1) * Problem520.invLog (Problem520.harperBlockEndpoint j) ^ 2 := by
  have hL : Tendsto (fun j : ℕ => Real.log (Problem520.harperBlockEndpoint j : ℝ))
      atTop atTop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp Problem520.strictMono_harperBlockEndpoint.tendsto_atTop)
  filter_upwards [hL.eventually (eventually_weighted_theta_scalar_le hc hC)] with j hj
  have hB : (0 : ℝ) < Problem520.harperBlockEndpoint j := by
    exact_mod_cast Problem520.harperBlockEndpoint_pos j
  have hsqrt : Real.sqrt (Problem520.harperBlockEndpoint j : ℝ) =
      Real.exp (Real.log (Problem520.harperBlockEndpoint j : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hB]
    congr 1
    ring
  rw [candidateCovarianceHeightWindow, Problem520.harperScheduledThetaEnvelope,
    Problem520.harperBlockEndpoint_succ, Problem520.mediumThetaBlockDelta_square_eq, hsqrt]
  convert hj using 1 <;> unfold Problem520.invLog <;> ring

/-- The supported frequency window grows monotonically with the starting
prime block. -/
theorem candidateCovarianceHeightWindow_monotone : Monotone candidateCovarianceHeightWindow := by
  intro i j hij
  unfold candidateCovarianceHeightWindow
  apply Real.exp_le_exp.mpr
  apply Real.rpow_le_rpow
    (Problem520.one_le_log_harperBlockEndpoint i |>.trans' (by norm_num)) _ (by norm_num)
  exact Real.log_le_log (by exact_mod_cast Problem520.harperBlockEndpoint_pos i)
    (by exact_mod_cast Problem520.monotone_harperBlockEndpoint hij)

/-- Uniform actual second-harmonic cancellation throughout the growing
height window. The right side is a summable geometric envelope. -/
theorem candidate_exists_growingHeight_oscillation_bound :
    ∃ K ≥ 0, ∃ J : ℕ, ∀ start j M y : ℕ, J ≤ start → start ≤ j →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start →
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
      |Problem520.harperScheduledOscillationMass y j (2 * t)| ≤
        (1 / 2 : ℝ) ^ j + K * (1 / 2 : ℝ) ^ (2 * j) := by
  obtain ⟨c, hc, C, hC, Jo, ho⟩ := Problem520.exists_harperScheduledMovingHeightOscillationBounds
  obtain ⟨Jt, ht⟩ := Filter.eventually_atTop.mp (candidate_eventually_heightWindow_mul_theta_le hc hC.le)
  refine ⟨5 * (C + 1), by positivity, max Jo Jt, ?_⟩
  intro start j M y hstart hsj hM hy t htlo hthi
  have hbound := ho M j y (by omega) hy (2 * t) (by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith) (by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hthi (by norm_num))
  have hwin := hM.trans (candidateCovarianceHeightWindow_monotone hsj)
  have hwinOne : 1 ≤ candidateCovarianceHeightWindow j := by
    unfold candidateCovarianceHeightWindow
    apply Real.one_le_exp
    positivity
  have hcoef : 3 + 2 * (M : ℝ) ≤ 5 * candidateCovarianceHeightWindow j := by linarith
  have htheta := ht j (by omega)
  have hinv := Problem520.invLog_harperBlockEndpoint_le_geometric j
  have hinv0 := (Problem520.invLog_harperBlockEndpoint_pos j).le
  calc
    _ ≤ Problem520.harperScheduledOscillationEnvelope M c C j := hbound
    _ = Problem520.invLog (Problem520.harperBlockEndpoint j) +
        (3 + 2 * (M : ℝ)) * Problem520.harperScheduledThetaEnvelope c C j := rfl
    _ ≤ (1 / 2 : ℝ) ^ j + 5 *
        (candidateCovarianceHeightWindow j * Problem520.harperScheduledThetaEnvelope c C j) := by
      exact add_le_add hinv (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef
          (Problem520.harperScheduledThetaEnvelope_nonneg hC.le j))
    _ ≤ (1 / 2 : ℝ) ^ j + 5 * ((C + 1) *
        Problem520.invLog (Problem520.harperBlockEndpoint j) ^ 2) := by gcongr
    _ ≤ (1 / 2 : ℝ) ^ j + 5 * ((C + 1) * ((1 / 2 : ℝ) ^ j) ^ 2) := by gcongr
    _ = _ := by rw [← pow_mul, Nat.mul_comm j 2]; ring


/-- Twenty extra block indices per binary logarithm of the logarithmic
height suffice. The factor twenty is the reciprocal retained PNT exponent.
-/
theorem candidate_exp_two_pow_le_heightWindow (k start : ℕ) (hk : 20 * k ≤ start) :
    Real.exp ((2 : ℝ) ^ k) ≤ candidateCovarianceHeightWindow start := by
  have hcoef : (1 : ℝ) ≤ 16 * Real.log 2 := by nlinarith [Real.log_two_gt_d9]
  have hlog : ((2 : ℝ) ^ k) ^ 20 ≤
      Real.log (Problem520.harperBlockEndpoint (20 * k) : ℝ) := by
    rw [Problem520.log_harperBlockEndpoint_eq, ← pow_mul, Nat.mul_comm k 20]
    nlinarith [mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (2 : ℝ) ^ (20 * k))]
  have hpow : (((2 : ℝ) ^ k) ^ 20) ^ ((1 : ℝ) / 20) = (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ) ^ k)]
    norm_num
  have hs := Real.rpow_le_rpow (by positivity) hlog (by norm_num : (0 : ℝ) ≤ 1 / 20)
  rw [hpow] at hs
  exact (Real.exp_le_exp.mpr hs).trans (candidateCovarianceHeightWindow_monotone hk)

/-- An explicit double-logarithmic starting index supports every prescribed
natural height window. -/
theorem candidate_heightWindow_ge_of_clog_log (M start : ℕ)
    (hstart : 20 * Nat.clog 2 ⌈Real.log ((M : ℝ) + 1)⌉₊ ≤ start) :
    (M : ℝ) ≤ candidateCovarianceHeightWindow start := by
  let k := Nat.clog 2 ⌈Real.log ((M : ℝ) + 1)⌉₊
  have hlog : Real.log ((M : ℝ) + 1) ≤ (2 : ℝ) ^ k := by
    have hceil : Real.log ((M : ℝ) + 1) ≤ (⌈Real.log ((M : ℝ) + 1)⌉₊ : ℝ) := Nat.le_ceil _
    have hnat : ⌈Real.log ((M : ℝ) + 1)⌉₊ ≤ 2 ^ k := by
      exact Nat.le_pow_clog (by norm_num) _
    have hreal : (⌈Real.log ((M : ℝ) + 1)⌉₊ : ℝ) ≤ (2 : ℝ) ^ k := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_le.mpr hnat :
        (⌈Real.log ((M : ℝ) + 1)⌉₊ : ℝ) ≤ (2 ^ k : ℕ))
    exact hceil.trans hreal
  calc
    (M : ℝ) ≤ (M : ℝ) + 1 := by linarith
    _ = Real.exp (Real.log ((M : ℝ) + 1)) := (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp ((2 : ℝ) ^ k) := Real.exp_le_exp.mpr hlog
    _ ≤ _ := candidate_exp_two_pow_le_heightWindow k start hstart

end

end Erdos.Problem1144
