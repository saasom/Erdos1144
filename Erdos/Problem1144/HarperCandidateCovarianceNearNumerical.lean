import Erdos.Problem1144.HarperCandidateCovarianceNearFactors
import Erdos.Problem1144.HarperCandidateCovarianceNearRowMoment

open Filter
open scoped Topology
namespace Erdos.Problem1144
noncomputable section
set_option maxHeartbeats 0

/-- The literal printed near-row bound, evaluated at the rounded schedule. -/
def candidateCovarianceScheduledNearBudget (C D : ℝ) (J : ℕ) (β T : ℝ) (N : ℕ) : ℝ :=
  let k := candidateCovarianceScheduleOrder T
  let M := (candidateCovarianceScheduleHeight T : ℝ)
  let d := candidateCovarianceScheduleWidth T
  let V := candidateCovarianceReflectedCellBound C D
    (candidateCovarianceScheduleStart J T) (candidateEulerTopIndex T)
    (candidateCovarianceScheduleStrong J T) k (Real.log T) M
  (4 * k * M + 2) *
    (2 * (Real.log ((β * T) / T) + 2) * Real.log (1 + T * d) / T) ^ (2 * k) *
    (((N : ℝ) + 1) * V (2 * k * d) + ((1 + (harmonic N : ℝ)) / 2) * (V 1 - V 0))

/-- All remaining scalar factors in the printed near bound have explicit
polynomial envelopes. The statement is uniform over row lengths `N ≤ G T`. -/
theorem candidate_eventually_covarianceSchedule_near_scalars (J : ℕ) (β G : ℝ)
    (hβ : 1 ≤ β) (hG : 0 < G) :
    ∀ᶠ T : ℝ in atTop,
      let q := Real.log T
      let k := candidateCovarianceScheduleOrder T
      let A := Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T) : ℝ)
      let L := Real.log (candidateEulerTopCutoff T : ℝ)
      let M := (candidateCovarianceScheduleHeight T : ℝ)
      let δ := Problem520.invLog (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStrong J T - 1))
      let U := A * M + 3 * Real.log (1 + L * M)
      let R := 2 * (Real.log ((β * T) / T) + 2) *
        Real.log (1 + T * candidateCovarianceScheduleWidth T) / T
      2 ≤ q ∧ 1 ≤ T ∧ 1 ≤ k ∧ 2 * (k : ℝ) ≤ q ∧
      0 ≤ U ∧ U ≤ q ^ 5 ∧ 0 ≤ R ∧ R * L ≤ q ^ 2 ∧
      4 * k * M + 2 ≤ q ^ 4 ∧ M ≤ q ^ 3 ∧
      0 ≤ 2 * (2 * k - 1 : ℕ) * (A + 2 / δ) ∧
      2 * (2 * k - 1 : ℕ) * (A + 2 / δ) ≤ q ^ 3 * Real.sqrt T ∧
      2 * k * candidateCovarianceScheduleWidth T ≤ q ^ 2 * T ^ (-(3 : ℝ) / 4) ∧
      ∀ N : ℕ, (N : ℝ) ≤ G * T →
        (N : ℝ) + 1 ≤ q * T ∧ (1 + (harmonic N : ℝ)) / 2 ≤ q ^ 2 := by
  let P : ℝ := 2 ^ J
  have hP : 0 < P := by positivity
  filter_upwards [candidate_eventually_covarianceSchedule_scalar_bounds J,
    candidate_eventually_covarianceSchedule_small_order,
    candidate_eventually_covarianceSchedule_strong_scale J,
    Real.tendsto_log_atTop.eventually_ge_atTop 10,
    Real.tendsto_log_atTop.eventually_ge_atTop (4 * P + 9),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 * (Real.log β + 2)),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * (P + 2 * Real.sqrt P)),
    Real.tendsto_log_atTop.eventually_ge_atTop (G + 1),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 + Real.log G),
    eventually_ge_atTop (2 : ℝ)] with T hs hk hδ hq10 hqP hqβ hqδ hqG hqlogG hT2
  dsimp only at hs ⊢
  let q := Real.log T
  let k := candidateCovarianceScheduleOrder T
  let A := Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T) : ℝ)
  let L := Real.log (candidateEulerTopCutoff T : ℝ)
  let M := (candidateCovarianceScheduleHeight T : ℝ)
  let δ := Problem520.invLog (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStrong J T - 1))
  let U := A * M + 3 * Real.log (1 + L * M)
  let R := 2 * (Real.log ((β * T) / T) + 2) * Real.log (1 + T * candidateCovarianceScheduleWidth T) / T
  rcases hs with ⟨hq1, hT, hA0, hL0, hM0, hA, hL, hM, hh, hpow, hMT, hlogT, hlogL, hU⟩
  have hq : 2 ≤ q := by dsimp [q]; linarith
  have hq0 : 0 < q := by linarith
  have hq1' : 1 ≤ q := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hk2 : 2 * (k : ℝ) ≤ q := by dsimp [k, q]; linarith [hk.2.1]
  have hMn : 0 ≤ M := hM0
  have hAn : 0 ≤ A := hA0
  have hLn : 0 ≤ L := hL0
  have hUn : 0 ≤ U := by
    dsimp [U]; exact add_nonneg (mul_nonneg hAn hMn)
      (mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith)))
  have hUU : U ≤ q ^ 5 := by
    have hu' : U ≤ (4 * P + 9) * q ^ 4 := by
      apply le_trans (b := A * (2 * M) + 3 * Real.log (1 + L * (2 * M))) _ hU
      dsimp only [U]
      gcongr <;> linarith
    exact hu'.trans (by nlinarith [mul_le_mul_of_nonneg_right hqP (pow_nonneg hq0.le 4)])
  have hM3 : M ≤ q ^ 3 := by nlinarith only [hM, hq, mul_nonneg (sq_nonneg q) (show 0 ≤ q - 2 by linarith)]
  have hlabel : 4 * k * M + 2 ≤ q ^ 4 := by
    have hm := mul_le_mul hk.2.1 hM hMn (show 0 ≤ q by positivity)
    change 4 * (k : ℝ) * M ≤ q * (2 * q ^ 2) at hm
    have hq3 : 3 ≤ q := by dsimp [q]; linarith only [hq10]
    have hc : 2 ≤ q ^ 3 := hq.trans (by simpa using pow_le_pow_right₀ hq1' (by norm_num : 1 ≤ 3))
    nlinarith only [hm, hc, mul_nonneg (pow_nonneg hq0.le 3) (show 0 ≤ q - 3 by linarith only [hq3])]
  have hqT : q ≤ Real.sqrt T := by
    apply (Real.le_sqrt hq0.le hT.le).mpr
    have hm : q ^ 2 ≤ M := (candidate_covarianceSchedule_height_bounds T).1
    linarith
  have hAs : A + 2 / δ ≤ (P + 2 * Real.sqrt P) * q * Real.sqrt T := by
    have ha' : A ≤ P * q * Real.sqrt T :=
      hA.trans (by nlinarith only [mul_le_mul_of_nonneg_left hqT (show 0 ≤ P * q by positivity)])
    change 1 / δ ≤ Real.sqrt P * q * Real.sqrt T at hδ
    calc
      A + 2 / δ = A + 2 * (1 / δ) := by ring
      _ ≤ P * q * Real.sqrt T + 2 * (Real.sqrt P * q * Real.sqrt T) :=
        add_le_add ha' (mul_le_mul_of_nonneg_left hδ (by norm_num))
      _ = _ := by ring
  have hδ0 : 0 < δ := by
    dsimp only [δ, Problem520.invLog]
    exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (Problem520.one_le_log_harperBlockEndpoint _))
  have hslope0 : 0 ≤ 2 * (2 * k - 1 : ℕ) * (A + 2 / δ) := by positivity
  have hslope : 2 * (2 * k - 1 : ℕ) * (A + 2 / δ) ≤ q ^ 3 * Real.sqrt T := by
    have hn : ((2 * k - 1 : ℕ) : ℝ) ≤ q := by
      exact (Nat.cast_le.mpr (Nat.sub_le (2 * k) 1)).trans (by simpa using hk2)
    calc
      _ ≤ 2 * q * ((P + 2 * Real.sqrt P) * q * Real.sqrt T) := by gcongr
      _ ≤ q ^ 3 * Real.sqrt T := by
        have h := mul_le_mul_of_nonneg_right hqδ (show 0 ≤ q ^ 2 * Real.sqrt T by positivity)
        nlinarith only [h]
  have hd0 : 0 ≤ candidateCovarianceScheduleWidth T := (Real.rpow_pos_of_pos hT _).le
  have hd1 : candidateCovarianceScheduleWidth T ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hlogR0 : 0 ≤ Real.log (1 + T * candidateCovarianceScheduleWidth T) :=
    Real.log_nonneg (by nlinarith only [mul_nonneg hT.le hd0])
  have hlogR : Real.log (1 + T * candidateCovarianceScheduleWidth T) ≤ 2 * q := by
    have hb : Real.log (1 + T * candidateCovarianceScheduleWidth T) ≤ Real.log (2 * T) :=
      Real.log_le_log (by positivity) (by nlinarith only [hd1, hT2, mul_le_mul_of_nonneg_left hd1 hT.le])
    rw [Real.log_mul (by norm_num) hT.ne'] at hb
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT2
    dsimp [q]; linarith
  have hβ0 : 0 ≤ Real.log β + 2 := by have := Real.log_nonneg hβ; linarith
  have he : (β * T) / T = β := mul_div_cancel_right₀ β hT.ne'
  have hR0 : 0 ≤ R := by dsimp [R]; rw [he]; positivity
  have hRL : R * L ≤ q ^ 2 := by
    calc
      _ ≤ R * T := mul_le_mul_of_nonneg_left hL hR0
      _ = 2 * (Real.log β + 2) * Real.log (1 + T * candidateCovarianceScheduleWidth T) := by
        dsimp only [R]; rw [he]; field_simp
      _ ≤ 4 * (Real.log β + 2) * q := by nlinarith only [mul_le_mul_of_nonneg_left hlogR hβ0]
      _ ≤ q ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_right hqβ hq0.le]
  refine ⟨hq, by linarith, hk.1, hk2, hUn, hUU, hR0, hRL, hlabel, hM3,
    hslope0, hslope, ?_, ?_⟩
  · change 2 * (k : ℝ) * T ^ (-(3 : ℝ) / 4) ≤ q ^ 2 * T ^ (-(3 : ℝ) / 4)
    gcongr
    nlinarith
  · intro N hN
    have hN1 : (N : ℝ) + 1 ≤ q * T := by
      have hg := mul_le_mul_of_nonneg_right hqG hT.le
      nlinarith
    refine ⟨hN1, ?_⟩
    by_cases hN0 : N = 0
    · simp only [hN0, harmonic_zero, Rat.cast_zero, add_zero]
      nlinarith
    have hlogN : Real.log (N : ℝ) ≤ Real.log G + q := by
      have he := Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)) hN
      rw [Real.log_mul hG.ne' hT.ne'] at he
      exact he
    have hhar := harmonic_le_one_add_log N
    have hb : (harmonic N : ℝ) ≤ 1 + Real.log G + q := by linarith
    nlinarith

end
end Erdos.Problem1144
