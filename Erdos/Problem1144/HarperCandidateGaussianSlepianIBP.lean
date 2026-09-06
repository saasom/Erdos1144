import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- The derivative of the standard Gaussian density, with its exact
normalization retained. -/
theorem candidate_hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, sub_zero, mul_one]
  have h := ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  convert h using 1 <;> simp [Pi.pow_apply, Pi.neg_apply] <;> ring

private theorem candidate_integrable_id_mul_standardGaussianPDF :
    Integrable (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).const_mul
    ((Real.sqrt (2 * Real.pi))⁻¹)
  convert h using 1
  ext x
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
  ring

/-- Gaussian integration by parts for a bounded differentiable test with
bounded measurable derivative. All integrability is established here from
Gaussian density estimates. -/
theorem candidate_standardGaussian_integration_by_parts
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hm : Measurable f')
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |f' x| ≤ C) :
    (∫ x : ℝ, x * f x ∂gaussianReal 0 1) =
      ∫ x : ℝ, f' x ∂gaussianReal 0 1 := by
  have hfm : AEStronglyMeasurable f volume :=
    (continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)).aestronglyMeasurable
  have hbf : ∀ᵐ x : ℝ, ‖f x‖ ≤ B := ae_of_all _ fun x => by simpa using hB x
  have hbd : ∀ᵐ x : ℝ, ‖f' x‖ ≤ C := ae_of_all _ fun x => by simpa using hC x
  have h0 : Integrable (fun x => f x * gaussianPDFReal 0 1 x) :=
    (integrable_gaussianPDFReal 0 1).bdd_mul hfm hbf
  have h1 : Integrable (fun x => f' x * gaussianPDFReal 0 1 x) :=
    (integrable_gaussianPDFReal 0 1).bdd_mul hm.aestronglyMeasurable hbd
  have h2 : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) := by
    have h := candidate_integrable_id_mul_standardGaussianPDF.neg.bdd_mul hfm hbf
    simpa only [neg_mul] using h
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hf x) (fun x _ => candidate_hasDerivAt_standardGaussianPDF x) h2 h1 h0
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  simp only [smul_eq_mul]
  have he : (fun x => f x * (-x * gaussianPDFReal 0 1 x)) =
      (fun x => -(gaussianPDFReal 0 1 x * (x * f x))) := by ext x; ring
  rw [he, integral_neg] at h
  have he' : (fun x => f' x * gaussianPDFReal 0 1 x) =
      (fun x => gaussianPDFReal 0 1 x * f' x) := by ext x; ring
  rw [he'] at h
  linarith

/-- The usual bounded `C¹` form of the standard Gaussian Stein identity. -/
theorem candidate_standardGaussian_integration_by_parts_contDiff
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {B C : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |deriv f x| ≤ C) :
    (∫ x : ℝ, x * f x ∂gaussianReal 0 1) =
      ∫ x : ℝ, deriv f x ∂gaussianReal 0 1 :=
  candidate_standardGaussian_integration_by_parts
    (fun x => (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt)
    hf.continuous_deriv_one.measurable hB hC

end Erdos.Problem1144
