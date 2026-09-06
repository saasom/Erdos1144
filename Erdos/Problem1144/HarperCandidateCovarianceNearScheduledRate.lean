import Erdos.Problem1144.HarperCandidateCovarianceNearBudget
import Erdos.Problem1144.HarperCandidateCovarianceMomentRates

open Filter
open scoped Topology
namespace Erdos.Problem1144
noncomputable section
set_option maxHeartbeats 0

private theorem eventually_threshold_inverse (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop,
      1 / (c * Real.log T ^ (-(3 : ℝ) / 5) / 2) ≤ Real.log T ^ 2 := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (2 / c)] with T hq hcq
  have hq0 : 0 < Real.log T := zero_lt_one.trans_le hq
  have hp : Real.log T ^ ((3 : ℝ) / 5) ≤ Real.log T := by
    simpa using Real.rpow_le_rpow_of_exponent_le hq (by norm_num : (3 : ℝ) / 5 ≤ 1)
  calc
    _ = (2 / c) * Real.log T ^ ((3 : ℝ) / 5) := by
      rw [show -(3 : ℝ) / 5 = -(3 / 5 : ℝ) by ring, Real.rpow_neg hq0.le]
      field_simp
    _ ≤ Real.log T * Real.log T := mul_le_mul hcq hp
      (Real.rpow_nonneg hq0.le _) hq0.le
    _ = _ := by ring

private theorem numerical_majorant_identity (T q : ℝ) (hT : 0 < T) (hq : 0 < q) (k : ℕ) :
    (T * q ^ (122 * k) / q ^ (2012 * k) +
        T * T ^ (-(3 : ℝ) / 4) * Real.sqrt T * q ^ (127 * k) +
        Real.sqrt T * q ^ (126 * k)) * q ^ (4 * k) / T ^ ((4 : ℝ) / 5) =
      T ^ ((1 : ℝ) / 5) * q ^ (-1886 * (k : ℝ)) +
      T ^ (-(1 : ℝ) / 20) * q ^ (131 * (k : ℝ)) +
      T ^ (-(3 : ℝ) / 10) * q ^ (130 * (k : ℝ)) := by
  have hp (a b : ℕ) : q ^ a * q ^ b = q ^ ((a : ℝ) + b) := by
    rw [Real.rpow_add hq, Real.rpow_natCast, Real.rpow_natCast]
  have hp' (a b d : ℕ) : q ^ a * q ^ b / q ^ d = q ^ ((a : ℝ) + b - d) := by
    rw [Real.rpow_sub hq, Real.rpow_add hq]
    simp only [Real.rpow_natCast]
  have h₁ : T / T ^ ((4 : ℝ) / 5) = T ^ ((1 : ℝ) / 5) := by
    rw [show (1 : ℝ) / 5 = 1 - 4 / 5 by norm_num, Real.rpow_sub hT, Real.rpow_one]
  have h₂ : T * T ^ (-(3 : ℝ) / 4) * Real.sqrt T / T ^ ((4 : ℝ) / 5) =
      T ^ (-(1 : ℝ) / 20) := by
    rw [Real.sqrt_eq_rpow]
    nth_rw 1 [← Real.rpow_one T]
    rw [← Real.rpow_add hT, ← Real.rpow_add hT, ← Real.rpow_sub hT]
    norm_num
  have h₃ : Real.sqrt T / T ^ ((4 : ℝ) / 5) = T ^ (-(3 : ℝ) / 10) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hT]
    norm_num
  calc
    _ = (T / T ^ ((4 : ℝ) / 5)) * (q ^ (122 * k) * q ^ (4 * k) / q ^ (2012 * k)) +
        (T * T ^ (-(3 : ℝ) / 4) * Real.sqrt T / T ^ ((4 : ℝ) / 5)) *
          (q ^ (127 * k) * q ^ (4 * k)) +
        (Real.sqrt T / T ^ ((4 : ℝ) / 5)) * (q ^ (126 * k) * q ^ (4 * k)) := by ring
    _ = _ := by
      rw [h₁, h₂, h₃, hp', hp, hp]
      congr 2 <;> congr 1 <;> push_cast <;> ring

/-- The complete printed near budget tends to zero after the actual
`T^(4/5)` degree and `c (log T)^(-3/5)` covariance threshold. The conclusion
is uniform over every row-length function bounded by a fixed multiple of T. -/
theorem candidate_scheduledNearBudget_threshold_tendsto_zero
    (C D : ℝ) (hC : 0 ≤ C) (J : ℕ) (β c G : ℝ)
    (hβ : 1 ≤ β) (hc : 0 < c) (hG : 0 < G) (N : ℝ → ℕ)
    (hN : ∀ᶠ T : ℝ in atTop, (N T : ℝ) ≤ G * T) :
    Tendsto (fun T : ℝ => candidateCovarianceScheduledNearBudget C D J β T (N T) /
      (T ^ ((4 : ℝ) / 5) * (c * Real.log T ^ (-(3 : ℝ) / 5) / 2) ^
        (2 * candidateCovarianceScheduleOrder T))) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun T : ℝ =>
      T ^ ((1 : ℝ) / 5) * Real.log T ^ (-1886 * (candidateCovarianceScheduleOrder T : ℝ)) +
      T ^ (-(1 : ℝ) / 20) * Real.log T ^ (131 * (candidateCovarianceScheduleOrder T : ℝ)) +
      T ^ (-(3 : ℝ) / 10) * Real.log T ^ (130 * (candidateCovarianceScheduleOrder T : ℝ)))
  · filter_upwards [candidate_eventually_covarianceSchedule_near_scalars J β G hβ hG] with T hs
    rcases hs with ⟨hq, hT, hk, _, hU, _, hR, _, _, _, hS, _, _, _⟩
    apply div_nonneg
    · let k := candidateCovarianceScheduleOrder T
      let q := Real.log T
      let A := Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T) : ℝ)
      let L := Real.log (candidateEulerTopCutoff T : ℝ)
      let M := (candidateCovarianceScheduleHeight T : ℝ)
      let δ := Problem520.invLog (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStrong J T - 1))
      let U := A * M + 3 * Real.log (1 + L * M)
      let S := 2 * (2 * k - 1 : ℕ) * (A + 2 / δ)
      let F := ((2 : ℝ) ^ (2 * k) * (Nat.factorial (2 * k) : ℝ)) *
        (((4 : ℝ) ^ (2 * k) * candidateCovarianceGapMomentFactor C D
          (candidateCovarianceScheduleStart J T) (2 * k) * L ^ (2 * k) / Real.log 3) *
          (q ^ (12 * (2 * k - 1)) * M))
      let V := candidateCovarianceReflectedCellBound C D (candidateCovarianceScheduleStart J T)
        (candidateEulerTopIndex T) (candidateCovarianceScheduleStrong J T) k q M
      have hV (e : ℝ) : V e = F * (U ^ (2 * k - 1) / q ^ (2012 * k) +
          e * S * U ^ (2 * k - 2)) := by
        dsimp only [V, F, U, S, A, L, M, δ, q, k, candidateCovarianceReflectedCellBound,
          candidateEulerTopCutoff]
        ring
      have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
      have hgap : 0 ≤ candidateCovarianceGapMomentFactor C D (candidateCovarianceScheduleStart J T)
          (2 * k) := by unfold candidateCovarianceGapMomentFactor; positivity
      have hM : 0 ≤ M := Nat.cast_nonneg _
      have hL : 0 ≤ L := zero_le_one.trans (Problem520.one_le_log_harperBlockEndpoint _)
      have hF : 0 ≤ F := by dsimp only [F]; positivity
      have hh : (0 : ℝ) ≤ harmonic (N T) := by
        exact_mod_cast (show (0 : ℚ) ≤ harmonic (N T) by unfold harmonic; positivity)
      have hdiff : V 1 - V 0 = F * S * U ^ (2 * k - 2) := by rw [hV, hV]; ring
      change 0 ≤ (4 * k * M + 2) *
        (2 * (Real.log ((β * T) / T) + 2) * Real.log (1 + T * candidateCovarianceScheduleWidth T) / T) ^
          (2 * k) * (((N T : ℝ) + 1) * V (2 * k * candidateCovarianceScheduleWidth T) +
            ((1 + (harmonic (N T) : ℝ)) / 2) * (V 1 - V 0))
      rw [hdiff, hV]
      have hUn : 0 ≤ U := hU
      have hSn : 0 ≤ S := hS
      have hwidth : 0 ≤ candidateCovarianceScheduleWidth T := by
        unfold candidateCovarianceScheduleWidth
        positivity
      positivity
    · positivity
  · filter_upwards [candidate_eventually_scheduledNearBudget_le C D hC J β G hβ hG,
      eventually_threshold_inverse c hc, hN, eventually_gt_atTop (1 : ℝ)] with T hB hinv hNT hT1
    let q := Real.log T
    let k := candidateCovarianceScheduleOrder T
    let Z := T * q ^ (122 * k) / q ^ (2012 * k) +
      T * candidateCovarianceScheduleWidth T * Real.sqrt T * q ^ (127 * k) +
      Real.sqrt T * q ^ (126 * k)
    let τ := c * q ^ (-(3 : ℝ) / 5) / 2
    have hT : 0 < T := by linarith
    have hq : 0 < q := Real.log_pos hT1
    have hτ : 0 < τ := by dsimp [τ]; positivity
    have hZ : 0 ≤ Z := by dsimp [Z, candidateCovarianceScheduleWidth]; positivity
    have hi : 1 / τ ^ (2 * k) ≤ q ^ (4 * k) := by
      calc
        _ = (1 / τ) ^ (2 * k) := by simp only [one_div, inv_pow]
        _ ≤ (q ^ 2) ^ (2 * k) := pow_le_pow_left₀ (by positivity) hinv _
        _ = _ := by rw [← pow_mul]; congr 1; omega
    calc
      _ ≤ Z / (T ^ ((4 : ℝ) / 5) * τ ^ (2 * k)) :=
        div_le_div_of_nonneg_right (hB (N T) hNT) (by positivity)
      _ = Z * (1 / τ ^ (2 * k)) / T ^ ((4 : ℝ) / 5) := by ring
      _ ≤ Z * q ^ (4 * k) / T ^ ((4 : ℝ) / 5) := by gcongr
      _ = _ := numerical_majorant_identity T q hT hq k
  · exact candidate_covarianceSchedule_near_majorant_tendsto_zero

end
end Erdos.Problem1144
