import Erdos.Problem1144.HarperCandidateCovarianceNearNumerical

open Filter
open scoped Topology
namespace Erdos.Problem1144
noncomputable section
set_option maxHeartbeats 0

private theorem pow_scale {q : ℝ} (hq : 1 ≤ q) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    q ^ n ≤ q ^ (n * k) := pow_le_pow_right₀ hq (by simpa using Nat.mul_le_mul_left n hk)

/-- The full printed near budget, including factorials, labels and the
harmonic sum, is bounded by three explicit terms. This is uniform in the
actual row length and uses the actual rounded block and moment choices. -/
theorem candidate_eventually_scheduledNearBudget_le (C D : ℝ) (hC : 0 ≤ C)
    (J : ℕ) (β G : ℝ) (hβ : 1 ≤ β) (hG : 0 < G) :
    ∀ᶠ T : ℝ in atTop, ∀ N : ℕ, (N : ℝ) ≤ G * T →
      let q := Real.log T
      let k := candidateCovarianceScheduleOrder T
      candidateCovarianceScheduledNearBudget C D J β T N ≤
        T * q ^ (122 * k) / q ^ (2012 * k) +
        T * candidateCovarianceScheduleWidth T * Real.sqrt T * q ^ (127 * k) +
        Real.sqrt T * q ^ (126 * k) := by
  filter_upwards [candidate_eventually_covarianceSchedule_near_scalars J β G hβ hG,
    candidate_eventually_covarianceSchedule_gapMomentFactor_le C D hC J,
    Real.tendsto_log_atTop.eventually_ge_atTop 4,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 / Real.log 3)] with T hs hgap hq4 hqlog
  intro N hN
  let q := Real.log T
  let k := candidateCovarianceScheduleOrder T
  let A := Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T) : ℝ)
  let L := Real.log (candidateEulerTopCutoff T : ℝ)
  let M := (candidateCovarianceScheduleHeight T : ℝ)
  let δ := Problem520.invLog (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStrong J T - 1))
  let U := A * M + 3 * Real.log (1 + L * M)
  let R := 2 * (Real.log ((β * T) / T) + 2) * Real.log (1 + T * candidateCovarianceScheduleWidth T) / T
  let S := 2 * (2 * k - 1 : ℕ) * (A + 2 / δ)
  let P := (4 * k * M + 2) * (R * L) ^ (2 * k) *
    (2 : ℝ) ^ (2 * k) * (Nat.factorial (2 * k) : ℝ) * (4 : ℝ) ^ (2 * k) *
    candidateCovarianceGapMomentFactor C D (candidateCovarianceScheduleStart J T) (2 * k) *
    (1 / Real.log 3) * q ^ (12 * (2 * k - 1)) * M
  rcases hs with ⟨hq2, hT1, hk1, hk2, hU0, hU, hR0, hRL, hlabel, hM, hS0, hS, hη, hNs⟩
  rcases hNs N hN with ⟨hNN, hhar⟩
  have hq1 : 1 ≤ q := by dsimp [q]; linarith only [hq2]
  have hq0 : 0 < q := zero_lt_one.trans_le hq1
  have hT : 0 < T := zero_lt_one.trans_le hT1
  have hLn : 0 ≤ L := zero_le_one.trans (Problem520.one_le_log_harperBlockEndpoint _)
  have hMn : 0 ≤ M := Nat.cast_nonneg _
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hd : 0 ≤ candidateCovarianceScheduleWidth T := (Real.rpow_pos_of_pos hT _).le
  have hGP : 0 ≤ candidateCovarianceGapMomentFactor C D
      (candidateCovarianceScheduleStart J T) (2 * k) := by
    unfold candidateCovarianceGapMomentFactor
    positivity
  have hP0 : 0 ≤ P := by dsimp only [P]; positivity
  have hRLp : (R * L) ^ (2 * k) ≤ q ^ (4 * k) := by
    calc
      _ ≤ (q ^ 2) ^ (2 * k) := pow_le_pow_left₀ (mul_nonneg hR0 hLn) hRL _
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hfac : (Nat.factorial (2 * k) : ℝ) ≤ q ^ (2 * k) := by
    calc
      _ ≤ (((2 * k : ℕ) : ℝ)) ^ (2 * k) := by exact_mod_cast Nat.factorial_le_pow (2 * k)
      _ ≤ q ^ (2 * k) := pow_le_pow_left₀ (Nat.cast_nonneg _) (by simpa using hk2) _
  have htwo : (2 : ℝ) ^ (2 * k) ≤ q ^ (2 * k) := pow_le_pow_left₀ (by norm_num) hq2 _
  have hfour : (4 : ℝ) ^ (2 * k) ≤ q ^ (2 * k) := pow_le_pow_left₀ (by norm_num) hq4 _
  have hlog : 1 / Real.log 3 ≤ q ^ k := hqlog.trans (by simpa using pow_scale hq1 hk1 1)
  have hW : q ^ (12 * (2 * k - 1)) ≤ q ^ (24 * k) :=
    pow_le_pow_right₀ hq1 (by omega)
  have hlabel' : 4 * k * M + 2 ≤ q ^ (4 * k) := hlabel.trans (pow_scale hq1 hk1 4)
  have hM' : M ≤ q ^ (3 * k) := hM.trans (pow_scale hq1 hk1 3)
  have hPP : P ≤ q ^ (111 * k) := by
    calc
      _ ≤ q ^ (4 * k) * q ^ (4 * k) * q ^ (2 * k) * q ^ (2 * k) * q ^ (2 * k) *
          q ^ (69 * k) * q ^ k * q ^ (24 * k) * q ^ (3 * k) := by
        dsimp only [P]
        gcongr
      _ = _ := by simp only [← pow_add]; congr 1; omega
  have hUp (n : ℕ) (hn : n ≤ 2 * k) : U ^ n ≤ q ^ (10 * k) := by
    calc
      _ ≤ (q ^ 5) ^ n := pow_le_pow_left₀ hU0 hU _
      _ ≤ (q ^ 5) ^ (2 * k) := pow_le_pow_right₀ (one_le_pow₀ hq1) hn
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hU₁ := hUp (2 * k - 1) (Nat.sub_le _ _)
  have hU₂ := hUp (2 * k - 2) (Nat.sub_le _ _)
  have hSS : S ≤ q ^ (3 * k) * Real.sqrt T :=
    hS.trans (mul_le_mul_of_nonneg_right (pow_scale hq1 hk1 3) (Real.sqrt_nonneg _))
  have hηη : 2 * k * candidateCovarianceScheduleWidth T ≤
      q ^ (2 * k) * candidateCovarianceScheduleWidth T := by
    exact hη.trans (mul_le_mul_of_nonneg_right (pow_scale hq1 hk1 2) hd)
  have hNN' : (N : ℝ) + 1 ≤ q ^ k * T :=
    hNN.trans (mul_le_mul_of_nonneg_right (by simpa using pow_scale hq1 hk1 1) hT.le)
  have hhar' : (1 + (harmonic N : ℝ)) / 2 ≤ q ^ (2 * k) := hhar.trans (pow_scale hq1 hk1 2)
  have hhar0 : 0 ≤ (1 + (harmonic N : ℝ)) / 2 := by
    have hh : (0 : ℝ) ≤ harmonic N := by exact_mod_cast (show (0 : ℚ) ≤ harmonic N by unfold harmonic; positivity)
    positivity
  have heq : candidateCovarianceScheduledNearBudget C D J β T N =
      P * (((N : ℝ) + 1) * (U ^ (2 * k - 1) / q ^ (2012 * k) +
        (2 * k * candidateCovarianceScheduleWidth T) * S * U ^ (2 * k - 2)) +
        ((1 + (harmonic N : ℝ)) / 2) * (S * U ^ (2 * k - 2))) := by
    dsimp only [candidateCovarianceScheduledNearBudget, candidateCovarianceReflectedCellBound,
      P, R, U, S, A, L, M, δ, q, k, candidateEulerTopCutoff]
    rw [mul_pow]
    ring
  rw [heq]
  calc
    _ ≤ q ^ (111 * k) * ((q ^ k * T) *
        (q ^ (10 * k) / q ^ (2012 * k) +
          (q ^ (2 * k) * candidateCovarianceScheduleWidth T) *
            (q ^ (3 * k) * Real.sqrt T) * q ^ (10 * k)) +
        q ^ (2 * k) * ((q ^ (3 * k) * Real.sqrt T) * q ^ (10 * k))) := by
      gcongr
    _ = T * q ^ (122 * k) / q ^ (2012 * k) +
        T * candidateCovarianceScheduleWidth T * Real.sqrt T * q ^ (127 * k) +
        Real.sqrt T * q ^ (126 * k) := by
      rw [mul_add, mul_add, mul_add]
      simp only [mul_div_assoc]
      ring_nf

end
end Erdos.Problem1144
