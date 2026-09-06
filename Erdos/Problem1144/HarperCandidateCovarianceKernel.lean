import Erdos.Problem1144.HarperCandidateCovariancePerronKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set
open scoped Interval BigOperators

namespace Erdos.Problem1144

noncomputable section

local instance : ContinuousSMul ℝ ℂ where
  continuous_smul := by
    change Continuous (fun z : ℝ × ℂ => (z.1 : ℂ) * z.2)
    fun_prop

/-! Actual oscillatory bounds for the reciprocal-logarithmic white kernel.
The phase is angular frequency, exactly as in the finite Euler covariance
identity. No constant-weight surrogate is used. -/

private theorem phase_norm (x : ℝ) : ‖candidateCovariancePhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

private theorem phase_deriv (h r : ℝ) :
    HasDerivAt (fun x : ℝ => candidateCovariancePhase (-h * x))
      (((-h : ℝ) : ℂ) * Complex.I * candidateCovariancePhase (-h * r)) r := by
  have hd := (((hasDerivAt_id r).const_mul (-h)).ofReal_comp.mul_const Complex.I).cexp
  convert hd using 1 <;> simp only [candidateCovariancePhase, id_eq, mul_one] <;> ring

private theorem phase_div_deriv (h r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun x : ℝ => candidateCovariancePhase (-h * x) / (x : ℂ))
      (((-h : ℝ) : ℂ) * Complex.I * (candidateCovariancePhase (-h * r) / (r : ℂ)) -
        candidateCovariancePhase (-h * r) / (r : ℂ) ^ 2) r := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  convert (phase_deriv h r).div (hasDerivAt_id r).ofReal_comp hrC using 1 <;>
    simp only [Complex.ofReal_one, id_eq] <;> field_simp <;> ring

private theorem continuousOn_phase_div_pow (T B h : ℝ) (hT : 0 < T) (n : ℕ) :
    ContinuousOn (fun r : ℝ => candidateCovariancePhase (-h * r) / (r : ℂ) ^ n) (Icc T B) := by
  apply ContinuousOn.div
  · unfold candidateCovariancePhase
    fun_prop
  · fun_prop
  · intro r hr
    apply pow_ne_zero
    exact_mod_cast (hT.trans_le hr.1).ne'

/-- Exact interval-integral form of the literal set-integral kernel. -/
theorem candidate_whiteKernel_eq_interval {T B : ℝ} (hTB : T ≤ B) (h : ℝ) :
    candidateCovarianceWhiteKernel T B h =
      ∫ r in T..B, candidateCovariancePhase (-h * r) / (r : ℂ) := by
  rw [candidateCovarianceWhiteKernel, candidateCovarianceMeasureKernel,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hTB]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => by push_cast; ring

/-- The nonoscillatory bound, including zero frequency. -/
theorem candidate_whiteKernel_norm_le_log {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (h : ℝ) :
    ‖candidateCovarianceWhiteKernel T B h‖ ≤ Real.log (B / T) := by
  rw [candidate_whiteKernel_eq_interval hTB]
  have hi : IntervalIntegrable (fun r : ℝ => 1 / r) volume T B := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hTB]
    exact continuousOn_const.div continuousOn_id fun r hr => (hT.trans_le hr.1).ne'
  calc
    _ ≤ ∫ r in T..B, 1 / r := by
      apply intervalIntegral.norm_integral_le_of_norm_le hTB _ hi
      exact Filter.Eventually.of_forall fun r hr => by
        rw [norm_div, phase_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hT.trans hr.1)]
    _ = _ := integral_one_div_of_pos hT (hT.trans_le hTB)

private theorem integral_inv_sq (T B : ℝ) (hT : 0 < T) (hTB : T ≤ B) :
    (∫ r in T..B, 1 / r ^ 2) = 1 / T - 1 / B := by
  have hd (r : ℝ) (hr : r ∈ uIcc T B) :
      HasDerivAt (fun x : ℝ => -(1 / x)) (1 / r ^ 2) r := by
    have hr0 : r ≠ 0 := (hT.trans_le (uIcc_of_le hTB ▸ hr).1).ne'
    convert ((hasDerivAt_id r).inv hr0).neg using 1
    · funext x
      simp
    · simp [neg_div]
  have hi : IntervalIntegrable (fun r : ℝ => 1 / r ^ 2) volume T B := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hTB]
    exact continuousOn_const.div (continuousOn_id.pow 2) fun r hr =>
      pow_ne_zero 2 (hT.trans_le hr.1).ne'
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  linarith

/-- Integration by parts retains the two endpoint terms and the exact
reciprocal-square remainder, uniformly even when the frequency is zero. -/
theorem candidate_whiteKernel_integration_by_parts
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (h : ℝ) :
    (((-h : ℝ) : ℂ) * Complex.I) * candidateCovarianceWhiteKernel T B h =
      candidateCovariancePhase (-h * B) / (B : ℂ) -
      candidateCovariancePhase (-h * T) / (T : ℂ) +
      ∫ r in T..B, candidateCovariancePhase (-h * r) / (r : ℂ) ^ 2 := by
  have hi (n : ℕ) : IntervalIntegrable
      (fun r : ℝ => candidateCovariancePhase (-h * r) / (r : ℂ) ^ n) volume T B := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hTB]
    exact continuousOn_phase_div_pow T B h hT n
  have hi1 : IntervalIntegrable
      (fun r : ℝ => candidateCovariancePhase (-h * r) / (r : ℂ)) volume T B := by
    simpa only [pow_one] using hi 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => phase_div_deriv h r (hT.trans_le (uIcc_of_le hTB ▸ hr).1).ne')
    ((hi1.const_mul (((-h : ℝ) : ℂ) * Complex.I)).sub (hi 2))
  rw [intervalIntegral.integral_sub
    (hi1.const_mul (((-h : ℝ) : ℂ) * Complex.I)) (hi 2),
    ] at hFTC
  have hconst : (∫ r in T..B, (((-h : ℝ) : ℂ) * Complex.I) *
      (candidateCovariancePhase (-h * r) / (r : ℂ))) =
      (((-h : ℝ) : ℂ) * Complex.I) *
      ∫ r in T..B, candidateCovariancePhase (-h * r) / (r : ℂ) := by
    simpa only [smul_eq_mul] using intervalIntegral.integral_smul
      (((-h : ℝ) : ℂ) * Complex.I)
      (fun r : ℝ => candidateCovariancePhase (-h * r) / (r : ℂ))
  rw [hconst, ← candidate_whiteKernel_eq_interval hTB] at hFTC
  exact sub_eq_iff_eq_add.mp hFTC

/-- The actual continuous covariance kernel has the required inverse-gap
oscillation bound. -/
theorem candidate_whiteKernel_norm_le_inverse_gap
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) {h : ℝ} (hh : h ≠ 0) :
    ‖candidateCovarianceWhiteKernel T B h‖ ≤ 2 / (T * |h|) := by
  have hB : 0 < B := hT.trans_le hTB
  have hrem : ‖∫ r in T..B, candidateCovariancePhase (-h * r) / (r : ℂ) ^ 2‖ ≤ 1 / T - 1 / B := by
    have hi : IntervalIntegrable (fun r : ℝ => 1 / r ^ 2) volume T B := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hTB]
      exact continuousOn_const.div (continuousOn_id.pow 2) fun r hr =>
        pow_ne_zero 2 (hT.trans_le hr.1).ne'
    calc
      _ ≤ ∫ r in T..B, 1 / r ^ 2 := by
        apply intervalIntegral.norm_integral_le_of_norm_le hTB _ hi
        exact Filter.Eventually.of_forall fun r hr => by
          rw [norm_div, phase_norm, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (hT.trans hr.1)]
      _ = _ := integral_inv_sq T B hT hTB
  have heq := candidate_whiteKernel_integration_by_parts hT hTB h
  have hnorm := congrArg norm heq
  have hcoef : ‖(((-h : ℝ) : ℂ) * Complex.I)‖ = |h| := by simp
  rw [norm_mul, hcoef] at hnorm
  have hbound : |h| * ‖candidateCovarianceWhiteKernel T B h‖ ≤ 2 / T := by
    rw [hnorm]
    calc
      _ ≤ ‖candidateCovariancePhase (-h * B) / (B : ℂ) -
          candidateCovariancePhase (-h * T) / (T : ℂ)‖ +
          ‖∫ r in T..B, candidateCovariancePhase (-h * r) / (r : ℂ) ^ 2‖ := norm_add_le _ _
      _ ≤ (‖candidateCovariancePhase (-h * B) / (B : ℂ)‖ +
          ‖candidateCovariancePhase (-h * T) / (T : ℂ)‖) + (1 / T - 1 / B) :=
        add_le_add (norm_sub_le _ _) hrem
      _ = _ := by
        rw [norm_div, norm_div, phase_norm, phase_norm,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos hB, abs_of_pos hT]
        ring
  apply (le_div_iff₀ (mul_pos hT (abs_pos.mpr hh))).mpr
  have := (mul_le_mul_of_nonneg_left hbound hT.le)
  have hcancel : T * (2 / T) = 2 := by field_simp
  rw [hcancel] at this
  nlinarith

end

end Erdos.Problem1144
