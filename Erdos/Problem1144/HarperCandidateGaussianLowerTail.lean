import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Set

namespace Erdos.Problem1144

/-- The standard normal density decreases on the nonnegative half-line. -/
theorem candidate_gaussianPDFReal_antitone_nonneg {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) : gaussianPDFReal 0 1 y ≤ gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Integrating the standard normal density over `(x,x+1]` gives a concrete
positive lower bound for the upper tail at every nonnegative threshold. -/
theorem candidate_gaussianReal_tail_ge_pdf (x : ℝ) (hx : 0 ≤ x) :
    gaussianPDFReal 0 1 (x + 1) ≤ (gaussianReal 0 1).real (Ioi x) := by
  have hi : IntegrableOn (gaussianPDFReal 0 1) (Ioc x (x + 1)) :=
    (integrable_gaussianPDFReal 0 1).restrict
  calc
    gaussianPDFReal 0 1 (x + 1) =
        ∫ y in Ioc x (x + 1), gaussianPDFReal 0 1 (x + 1) := by
      rw [integral_const, measureReal_restrict_apply_univ,
        Real.volume_real_Ioc_of_le (by linarith)]
      simp
    _ ≤ ∫ y in Ioc x (x + 1), gaussianPDFReal 0 1 y := by
      apply integral_mono_ae (integrable_const _) hi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact candidate_gaussianPDFReal_antitone_nonneg (hx.trans hy.1.le) hy.2
    _ = (gaussianReal 0 1).real (Ioc x (x + 1)) := by
      rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num),
        ENNReal.toReal_ofReal (integral_nonneg fun y ↦ gaussianPDFReal_nonneg 0 1 y)]
    _ ≤ (gaussianReal 0 1).real (Ioi x) := measureReal_mono fun _ hy ↦ hy.1

/-- The scalar normal lower-box probability, raised to a finite power,
has the explicit exponential upper bound used for independent maxima. -/
theorem candidate_gaussianReal_Iic_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    ((gaussianReal 0 1).real (Iic x)) ^ m ≤
      Real.exp (-(m : ℝ) * gaussianPDFReal 0 1 (x + 1)) := by
  have hsum : (gaussianReal 0 1).real (Iic x) + (gaussianReal 0 1).real (Ioi x) = 1 := by
    simpa only [compl_Iic, probReal_univ] using
      (measureReal_add_measureReal_compl (μ := gaussianReal 0 1) (s := Iic x) measurableSet_Iic)
  have hbase : (gaussianReal 0 1).real (Iic x) ≤
      Real.exp (-gaussianPDFReal 0 1 (x + 1)) := by
    have ht := candidate_gaussianReal_tail_ge_pdf x hx
    have he := Real.add_one_le_exp (-gaussianPDFReal 0 1 (x + 1))
    linarith
  have h := pow_le_pow_left₀ (show 0 ≤ (gaussianReal 0 1).real (Iic x) from measureReal_nonneg)
    hbase m
  simpa only [← Real.exp_nat_mul, mul_neg, neg_mul] using h

end Erdos.Problem1144
