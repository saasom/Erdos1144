import Erdos.Problem1144.HarperRankinTwoHeightLaw
import Erdos.Problem1144.HarperLogBarrierBallot

open Finset MeasureTheory ProbabilityTheory
open Erdos.Problem520
open scoped BigOperators

namespace Erdos.Problem1144

private theorem candidate_log_normSq_quadratic_upper
    {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (theta : ℝ) (b : Bool) :
    Real.log ((1 + cubeSign b * r * Real.cos theta) ^ 2 +
      (cubeSign b * r * Real.sin theta) ^ 2) ≤
        2 * cubeSign b * r * Real.cos theta - r ^ 2 * Real.cos (2 * theta) +
          (4 / 3 : ℝ) * r ^ 3 := by
  let z : ℂ := ((cubeSign b * r : ℝ) : ℂ) *
    Complex.exp ((theta : ℂ) * Complex.I)
  have hz : ‖z‖ = r := by
    dsimp [z]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_mul, show |cubeSign b| = 1 by cases b <;> norm_num [cubeSign],
      one_mul, abs_of_nonneg hr]
  have hre : z.re = cubeSign b * r * Real.cos theta := by
    rw [show z = ((cubeSign b * r : ℝ) : ℂ) * Complex.exp ((theta : ℝ) * Complex.I) by rfl, Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add, sub_zero]
    ring
  have him : z.im = cubeSign b * r * Real.sin theta := by
    rw [show z = ((cubeSign b * r : ℝ) : ℂ) * Complex.exp ((theta : ℝ) * Complex.I) by rfl, Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add, sub_zero]
    ring
  have hlog : Real.log ((1 + cubeSign b * r * Real.cos theta) ^ 2 +
      (cubeSign b * r * Real.sin theta) ^ 2) =
      2 * (Complex.log (1 + z)).re := by
    rw [Complex.log_re, show 2 * Real.log ‖1 + z‖ = Real.log (‖1 + z‖ ^ 2) by rw [Real.log_pow]; norm_num]
    congr 1
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hre, him, sq]
  have hpoly : (harperLogQuadratic z).re =
      cubeSign b * r * Real.cos theta - r ^ 2 * Real.cos (2 * theta) / 2 := by
    unfold harperLogQuadratic
    simp only [pow_two, Complex.sub_re, Complex.div_re, Complex.mul_re,
      Complex.mul_im, hre, him]
    norm_num [Complex.normSq]
    rw [Real.cos_two_mul]
    have heps : cubeSign b ^ 2 = 1 := by cases b <;> norm_num [cubeSign]
    have htrig := Real.sin_sq_add_cos_sq theta
    have htrigmul := congrArg (fun x : ℝ => r ^ 2 * x) htrig
    have hepsmul := congrArg (fun x : ℝ => x * r ^ 2 * (Real.cos theta ^ 2 - Real.sin theta ^ 2)) heps
    nlinarith
  have hbound := Complex.norm_log_sub_logTaylor_le 2
    (show ‖z‖ < 1 by rw [hz]; linarith)
  have htaylor : Complex.logTaylor 3 z = harperLogQuadratic z := by
    simp [Complex.logTaylor_succ, Complex.logTaylor_zero, harperLogQuadratic]
    ring
  rw [htaylor, hz] at hbound
  norm_num at hbound
  have hinv : (1 - r)⁻¹ ≤ (2 : ℝ) := by
    apply (inv_le_comm₀ (by linarith) (by norm_num)).2
    linarith
  have hbound' : ‖Complex.log (1 + z) - harperLogQuadratic z‖ ≤
      (2 / 3 : ℝ) * r ^ 3 := by
    calc
      _ ≤ r ^ 3 * (1 - r)⁻¹ / 3 := hbound
      _ ≤ r ^ 3 * 2 / 3 := by gcongr
      _ = _ := by ring
  have hreal := (Complex.abs_re_le_norm
    (Complex.log (1 + z) - harperLogQuadratic z)).trans hbound'
  rw [Complex.sub_re, hpoly] at hreal
  rw [hlog]
  linarith [le_of_abs_le hreal]

/-- The literal shifted normalized factor has the same summable Taylor
error as the critical factor. The centering is its own one-height bias. -/
theorem candidate_rankin_log_normalized_factor_le
    {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) {a : ℝ} (ha : 0 ≤ a)
    (t : ℝ) (b : Bool) :
    Real.log (harperRankinCoordinateFactor p a t b / harperRankinEulerNormalizer p a) ≤
      2 * harperRankinCenteredLinearPrimeIncrement p a t t b +
        harperRankinEulerRadius p a ^ 2 +
        harperRankinEulerRadius p a ^ 2 * Real.cos (2 * t * Real.log (p : ℝ)) +
        harperRankinEulerRadius p a ^ 4 +
        (4 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  let r := harperRankinEulerRadius p a
  let c := Real.cos (t * Real.log (p : ℝ))
  have hr : 0 ≤ r := harperRankinEulerRadius_nonneg p a
  have hrle : r ≤ (Real.sqrt (p : ℝ))⁻¹ :=
    harperRankinEulerRadius_le_inv_sqrt hp.one_le ha
  have hsqrt : (2 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast hp4
  have hrhalf : r ≤ 1 / 2 := hrle.trans (by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hsqrt)
  have hlog := candidate_log_normSq_quadratic_upper hr hrhalf
    (t * Real.log (p : ℝ)) b
  have heps : ε (fun _ => b) p = cubeSign b := by
    cases b <;> rfl
  change Real.log (harperRankinCoordinateFactor p a t b) ≤ _ at hlog
  have hnorm : r ^ 2 - (r ^ 2) ^ 2 ≤ Real.log (1 + r ^ 2) := by
    have hrat : r ^ 2 - (r ^ 2) ^ 2 ≤ 2 * r ^ 2 / (r ^ 2 + 2) := by
      apply (le_div_iff₀ (by positivity)).2
      nlinarith [pow_nonneg hr 6]
    exact hrat.trans (Real.le_log_one_add_of_nonneg (sq_nonneg r))
  have hcenter : harperRankinCenteredLinearPrimeIncrement p a t t b =
      cubeSign b * r * c - 2 * r ^ 2 * c ^ 2 / (1 + r ^ 2) := by
    unfold harperRankinCenteredLinearPrimeIncrement harperRankinLinearPrimeIncrement
      harperRankinTiltBias harperRankinEulerNormalizer
    dsimp [r, c]
    ring
  have hden : 0 < 1 + r ^ 2 := by positivity
  have hmean : 2 * r ^ 2 * c ^ 2 / (1 + r ^ 2) ≤ 2 * r ^ 2 * c ^ 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg c),
      mul_nonneg (sq_nonneg (r ^ 2)) (sq_nonneg c)]
  have hc : Real.cos (2 * t * Real.log (p : ℝ)) = 2 * c ^ 2 - 1 := by
    rw [mul_assoc, Real.cos_two_mul]
  have hc' : Real.cos (2 * (t * Real.log (p : ℝ))) = 2 * c ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have hcubic := pow_le_pow_left₀ hr hrle 3
  rw [Real.log_div (harperRankinCoordinateFactor_pos hp ha t b).ne'
      (harperRankinEulerNormalizer_pos p a).ne', hcenter, hc]
  change Real.log (harperRankinCoordinateFactor p a t b) - Real.log (1 + r ^ 2) ≤ _
  rw [hc'] at hlog
  change Real.log (harperRankinCoordinateFactor p a t b) ≤
    2 * cubeSign b * r * c - r ^ 2 * (2 * c ^ 2 - 1) + 4 / 3 * r ^ 3 at hlog
  change _ ≤ 2 * (cubeSign b * r * c - 2 * r ^ 2 * c ^ 2 / (1 + r ^ 2)) +
    r ^ 2 + r ^ 2 * (2 * c ^ 2 - 1) + r ^ 4 + _
  nlinarith

end Erdos.Problem1144
