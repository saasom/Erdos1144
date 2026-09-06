import Erdos.Problem1144.HarperCandidateCovarianceParameterBounds
import Erdos.Problem1144.HarperCandidateCovarianceFarMoment

open Filter MeasureTheory
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- The printed far-moment budget with all actual rounded parameters
inserted and time window `[T,βT]`. -/
def candidateCovarianceScheduledFarBudget (C : ℝ) (J : ℕ) (β T : ℝ) : ℝ :=
  let A := Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T) : ℝ)
  let L := Real.log (candidateEulerTopCutoff T : ℝ)
  let M := (candidateCovarianceScheduleHeight T : ℝ)
  let h := candidateCovarianceScheduleLowerHeight T
  let d := candidateCovarianceScheduleWidth T
  C * Real.sqrt L * Real.sqrt (max A (1 / h)) * Real.sqrt (A + 2 / d) *
    (2 * (Real.log ((β * T) / T) + 2) * Real.log (1 + T * (2 * M)) / T) *
    (Real.sqrt (2 * M) * Real.sqrt (A * (2 * M) + 3 * Real.log (1 + L * (2 * M))))

private theorem farBudget_nonneg {C β T : ℝ} (hC : 0 ≤ C) (hβ : 1 ≤ β)
    (hT : 0 < T) (J : ℕ) : 0 ≤ candidateCovarianceScheduledFarBudget C J β T := by
  have hratio : β * T / T = β := mul_div_cancel_right₀ β hT.ne'
  have hlog := Real.log_nonneg hβ
  have hM : (0 : ℝ) ≤ candidateCovarianceScheduleHeight T := Nat.cast_nonneg _
  have hlogM : 0 ≤ Real.log (1 + T * (2 * (candidateCovarianceScheduleHeight T : ℝ))) :=
    Real.log_nonneg (by nlinarith)
  unfold candidateCovarianceScheduledFarBudget
  dsimp only
  rw [hratio]
  positivity

private theorem sqrt_time_ratio {T : ℝ} (hT : 0 < T) :
    Real.sqrt T * Real.sqrt (T ^ ((3 : ℝ) / 4)) / T = 1 / T ^ ((1 : ℝ) / 8) := by
  have he : Real.sqrt T * Real.sqrt (T ^ ((3 : ℝ) / 4)) = T ^ ((7 : ℝ) / 8) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hT.le, ← Real.rpow_add hT]
    norm_num
  rw [he]
  calc
    T ^ ((7 : ℝ) / 8) / T = T ^ ((7 : ℝ) / 8) / T ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = T ^ (-(1 : ℝ) / 8) := by rw [← Real.rpow_sub hT]; congr 1; ring
    _ = _ := by
      rw [show -(1 : ℝ) / 8 = -((1 : ℝ) / 8) by ring, Real.rpow_neg hT.le]
      simp only [one_div]

/-- The actual far budget has the polynomial bound predicted by the
mathematical rate check. Its constant may depend on the fixed offset and
time-window ratio, but not on time. -/
theorem candidate_exists_scheduledFarBudget_le_log_pow (C : ℝ) (hC : 0 ≤ C)
    (J : ℕ) (β : ℝ) (hβ : 1 ≤ β) :
    ∃ K > 0, ∀ᶠ T : ℝ in atTop,
      candidateCovarianceScheduledFarBudget C J β T ≤
        K * Real.log T ^ 5 / T ^ ((1 : ℝ) / 8) := by
  let P : ℝ := (2 : ℝ) ^ J
  let H : ℝ := max P 2
  let Q : ℝ := P + 2
  let V : ℝ := 4 * P + 9
  let K : ℝ := 12 * C * Real.sqrt H * Real.sqrt Q *
    (Real.log β + 2) * Real.sqrt V
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hH : 0 ≤ H := hP.trans (le_max_left _ _)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hβlog : 0 ≤ Real.log β + 2 := by linarith [Real.log_nonneg hβ]
  refine ⟨K + 1, by dsimp [K]; positivity, ?_⟩
  filter_upwards [candidate_eventually_covarianceSchedule_scalar_bounds J] with T h
  dsimp only at h
  let q := Real.log T
  let A := Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T) : ℝ)
  let L := Real.log (candidateEulerTopCutoff T : ℝ)
  let M := (candidateCovarianceScheduleHeight T : ℝ)
  obtain ⟨hq, hT, hAn, hLn, hMn, hA, hL, hM, hh, hpow, htime, hlogT, hlogL, hU⟩ := h
  change 1 ≤ q at hq
  change A ≤ P * q ^ 2 at hA
  change M ≤ 2 * q ^ 2 at hM
  have hq0 : 0 ≤ q := by linarith
  have hrL : Real.sqrt L ≤ Real.sqrt T := Real.sqrt_le_sqrt hL
  have hrH : Real.sqrt (max A (1 / candidateCovarianceScheduleLowerHeight T)) ≤
      Real.sqrt H * q := by
    have hm : max A (1 / candidateCovarianceScheduleLowerHeight T) ≤ H * q ^ 2 := by
      apply max_le
      · exact hA.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg q))
      · exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg q))
    simpa only [Real.sqrt_mul hH, Real.sqrt_sq hq0] using Real.sqrt_le_sqrt hm
  have hd : 2 / candidateCovarianceScheduleWidth T = 2 * T ^ ((3 : ℝ) / 4) := by
    unfold candidateCovarianceScheduleWidth
    rw [show -(3 : ℝ) / 4 = -((3 : ℝ) / 4) by ring, Real.rpow_neg hT.le, div_inv_eq_mul]
  have hrQ : Real.sqrt (A + 2 / candidateCovarianceScheduleWidth T) ≤
      Real.sqrt Q * Real.sqrt (T ^ ((3 : ℝ) / 4)) := by
    have ha : A ≤ P * T ^ ((3 : ℝ) / 4) :=
      hA.trans (mul_le_mul_of_nonneg_left hpow hP)
    have hb : A + 2 / candidateCovarianceScheduleWidth T ≤ Q * T ^ ((3 : ℝ) / 4) := by
      rw [hd]
      dsimp only [Q]
      nlinarith
    simpa only [Real.sqrt_mul hQ] using Real.sqrt_le_sqrt hb
  have hrM : Real.sqrt (2 * M) ≤ 2 * q := by
    have hb : 2 * M ≤ (2 * q) ^ 2 := by nlinarith
    simpa only [Real.sqrt_sq (show 0 ≤ 2 * q by positivity)] using Real.sqrt_le_sqrt hb
  have hrU : Real.sqrt (A * (2 * M) + 3 * Real.log (1 + L * (2 * M))) ≤
      Real.sqrt V * q ^ 2 := by
    have he : q ^ 4 = (q ^ 2) ^ 2 := by ring
    change A * (2 * M) + 3 * Real.log (1 + L * (2 * M)) ≤ V * q ^ 4 at hU
    rw [he] at hU
    simpa only [Real.sqrt_mul hV, Real.sqrt_sq (sq_nonneg q)] using Real.sqrt_le_sqrt hU
  have hkernel :
      2 * (Real.log ((β * T) / T) + 2) * Real.log (1 + T * (2 * M)) / T ≤
        6 * (Real.log β + 2) * q / T := by
    rw [mul_div_cancel_right₀ β hT.ne']
    have hh := mul_le_mul_of_nonneg_left hlogT (show 0 ≤ 2 * (Real.log β + 2) by positivity)
    apply (div_le_div_iff_of_pos_right hT).mpr
    convert hh using 1 <;> dsimp only [M, q] <;> ring
  have hkn : 0 ≤ 6 * (Real.log β + 2) * q / T := by positivity
  have hkernel0 : 0 ≤ 2 * (Real.log ((β * T) / T) + 2) *
      Real.log (1 + T * (2 * M)) / T := by
    rw [mul_div_cancel_right₀ β hT.ne']
    have hm0 : 0 ≤ Real.log (1 + T * (2 * M)) := Real.log_nonneg (by nlinarith)
    positivity
  have hb : candidateCovarianceScheduledFarBudget C J β T ≤
      C * Real.sqrt T * (Real.sqrt H * q) *
        (Real.sqrt Q * Real.sqrt (T ^ ((3 : ℝ) / 4))) *
        (6 * (Real.log β + 2) * q / T) * ((2 * q) * (Real.sqrt V * q ^ 2)) := by
    unfold candidateCovarianceScheduledFarBudget
    dsimp only
    gcongr
  calc
    _ ≤ _ := hb
    _ = K * q ^ 5 * (Real.sqrt T * Real.sqrt (T ^ ((3 : ℝ) / 4)) / T) := by
      dsimp only [K]
      ring
    _ = K * q ^ 5 / T ^ ((1 : ℝ) / 8) := by rw [sqrt_time_ratio hT]; ring
    _ ≤ (K + 1) * Real.log T ^ 5 / T ^ ((1 : ℝ) / 8) := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hT.le _)
      dsimp only [q]
      nlinarith [pow_nonneg hq0 5]

/-- The printed far budget vanishes even after division by the actual
`(log T)^(-3/5)` covariance threshold. -/
theorem candidate_scheduledFarBudget_threshold_tendsto_zero
    (C : ℝ) (hC : 0 ≤ C) (J : ℕ) (β : ℝ) (hβ : 1 ≤ β) :
    Tendsto (fun T : ℝ => candidateCovarianceScheduledFarBudget C J β T *
      Real.log T ^ ((3 : ℝ) / 5)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := candidate_exists_scheduledFarBudget_le_log_pow C hC J β hβ
  have hlim := ((isLittleO_log_rpow_rpow_atTop ((28 : ℝ) / 5)
    (s := (1 : ℝ) / 8) (by norm_num)).tendsto_div_nhds_zero).const_mul K
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact mul_nonneg (farBudget_nonneg hC hβ (by linarith) J)
      (Real.rpow_nonneg (Real.log_pos hT).le _)
  · filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with T hb hT
    have hq : 0 < Real.log T := Real.log_pos hT
    have hh := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hq.le ((3 : ℝ) / 5))
    apply hh.trans_eq
    rw [div_mul_eq_mul_div, mul_assoc, ← Real.rpow_natCast (Real.log T) 5, ← Real.rpow_add hq]
    norm_num
    ring

/-- Unconditional decay of the actual scheduled far-mass expectation at
the required covariance threshold. Only the fixed initial offset must
dominate the absolute offset already proved in the arithmetic moment. -/
theorem candidate_exists_scheduledFarMass_threshold_tendsto_zero :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ β : ℝ, 1 ≤ β →
      Tendsto (fun T : ℝ =>
        (∫ ω, candidateEulerBandFarMass (candidateEulerTopCutoff T) T (β * T)
          (candidateCovarianceScheduleLowerHeight T) (candidateCovarianceScheduleHeight T)
          (candidateCovarianceScheduleWidth T) ω ∂mu) * Real.log T ^ ((3 : ℝ) / 5))
        atTop (𝓝 0) := by
  obtain ⟨C, hC, J₀, hm⟩ := candidate_exists_farMass_expectation_bound
  refine ⟨J₀, ?_⟩
  intro J hJ β hβ
  apply squeeze_zero' _ _ (candidate_scheduledFarBudget_threshold_tendsto_zero C hC.le J β hβ)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    apply mul_nonneg
    · exact integral_nonneg fun ω => candidate_farMass_nonneg _ _ _ _ _ _ ω
    · exact Real.rpow_nonneg (Real.log_pos hT).le _
  · filter_upwards [candidate_eventually_covarianceSchedule_geometry J] with T h
    obtain ⟨hT, hq, hstart, hlength, hstrong, hstop, hgap, hk, hh, hd, hM, hwin⟩ := h
    have hJstart : J₀ ≤ candidateCovarianceScheduleStart J T := by
      unfold candidateCovarianceScheduleStart
      omega
    have hss : candidateCovarianceScheduleStart J T ≤ candidateEulerTopIndex T :=
      hstrong.le.trans hstop
    have hb := hm (candidateCovarianceScheduleStart J T) (candidateEulerTopIndex T)
      hJstart hss (candidateCovarianceScheduleLowerHeight T) (candidateCovarianceScheduleHeight T)
      (candidateCovarianceScheduleWidth T) T (β * T) hh (Nat.cast_nonneg _) hd (by linarith)
      (by nlinarith) hwin
    exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (by linarith) _)

end
end Erdos.Problem1144
