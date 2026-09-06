import Erdos.Problem1144.HarperCandidateSpectralConvolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.RiemannZeta

open MeasureTheory
open scoped BigOperators

namespace Erdos.Problem1144

/-- Absolute summability of translate weights permits Fourier transformation
term by term. The phase records the actual displacement of each translate. -/
theorem candidate_fourier_tsum_translates
    {f : ℝ → ℂ} (hf : Integrable f) {c : ℕ → ℂ}
    (hc : Summable fun r => ‖c r‖) (d : ℕ → ℝ) (ξ : ℝ) :
    Fourier.fourierIntegral Real.fourierChar volume
      (fun t => ∑' r, c r * f (t - d r)) ξ =
      (∑' r, c r * (Real.fourierChar (-(d r * ξ)) : ℂ)) *
        Fourier.fourierIntegral Real.fourierChar volume f ξ := by
  have hshift (r : ℕ) : Integrable fun t => c r * f (t - d r) := by
    simpa only [sub_eq_add_neg] using (hf.comp_add_right (-d r)).const_mul (c r)
  have hphase (r : ℕ) : Integrable fun t =>
      Real.fourierChar (-(t * ξ)) • (c r * f (t - d r)) := by
    exact (VectorFourier.fourierIntegral_convergent_iff
      (L := LinearMap.mul ℝ ℝ) Real.continuous_fourierChar continuous_mul ξ).mpr
        (hshift r)
  have hnorm (r : ℕ) :
      (∫ t, ‖Real.fourierChar (-(t * ξ)) • (c r * f (t - d r))‖) =
        ‖c r‖ * ∫ t, ‖f t‖ := by
    simp only [Circle.norm_smul, norm_mul, integral_const_mul]
    congr 1
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self (fun t => ‖f t‖) (-d r)
  rw [Fourier.fourierIntegral_def]
  simp_rw [← tsum_const_smul']
  rw [← integral_tsum_of_summable_integral_norm hphase
    (by simpa only [hnorm] using hc.mul_right (∫ t, ‖f t‖))]
  calc
    _ = ∑' r, (c r * (Real.fourierChar (-(d r * ξ)) : ℂ)) *
        Fourier.fourierIntegral Real.fourierChar volume f ξ := by
      apply tsum_congr
      intro r
      change Fourier.fourierIntegral Real.fourierChar volume
        (c r • (f ∘ fun t => t + -d r)) ξ = _
      rw [Fourier.fourierIntegral_const_smul,
        Fourier.fourierIntegral_comp_add_right]
      simp only [Pi.smul_apply, Circle.smul_def, smul_eq_mul, neg_mul]
      ring
    _ = _ := tsum_mul_right

/-- Each damped square-translation phase is exactly a Dirichlet-series term.
The factor `4πξ` comes from the displacement `2 log r` and the Fourier convention. -/
theorem candidate_square_translation_phase_eq_cpow
    {σ : ℝ} (hσ : 0 < σ) (ξ : ℝ) (r : ℕ) :
    (candidateSquareTranslationWeight σ r : ℂ) *
        (Real.fourierChar (-(2 * Real.log r * ξ)) : ℂ) =
      1 / (r : ℂ) ^ (((1 + 2 * σ : ℝ) : ℂ) +
        ((4 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) := by
  by_cases hr : r = 0
  · subst r
    have hs : (((1 + 2 * σ : ℝ) : ℂ) +
        ((4 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      intro he
      have hh := congrArg Complex.re he
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_mul, sub_self, add_zero, Complex.zero_re] at hh
      linarith
    simp only [candidateSquareTranslationWeight, Nat.cast_zero, div_zero,
      zero_mul, Complex.ofReal_zero]
    rw [Complex.zero_cpow hs]
    simp
  · have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
    rw [candidateSquareTranslationWeight_eq_rpow hσ,
      Real.rpow_def_of_pos hrpos, Complex.ofReal_exp, Real.fourierChar_apply,
      ← Complex.exp_add, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hr),
      ← Complex.natCast_log, one_div, ← Complex.exp_neg]
    congr 1
    push_cast
    ring

/-- The actual damped translation multiplier is the zeta function, in its
absolutely convergent half-plane. -/
theorem candidate_square_translation_multiplier_eq_zeta
    {σ : ℝ} (hσ : 0 < σ) (ξ : ℝ) :
    (∑' r : ℕ, (candidateSquareTranslationWeight σ r : ℂ) *
      (Real.fourierChar (-(2 * Real.log r * ξ)) : ℂ)) =
      riemannZeta (((1 + 2 * σ : ℝ) : ℂ) +
        ((4 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) := by
  simp_rw [candidate_square_translation_phase_eq_cpow hσ]
  symm
  apply zeta_eq_tsum_one_div_nat_cpow
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_self, add_zero]
  linarith

/-- Fourier factorization of the actual complete process follows from its
exact square convolution. The only analytic input is integrability of the
damped squarefree path. -/
theorem harperCandidateLogProcess_fourier_eq_zeta_mul
    (ω : Omega) {σ : ℝ} (hσ : 0 < σ)
    (hm : Integrable fun t : ℝ =>
      ((Real.exp (-σ * t) * harperCandidateSquarefreeLogProcess ω t : ℝ) : ℂ))
    (ξ : ℝ) :
    Fourier.fourierIntegral Real.fourierChar volume
      (fun t => ((Real.exp (-σ * t) * harperCandidateLogProcess ω t : ℝ) : ℂ)) ξ =
      riemannZeta (((1 + 2 * σ : ℝ) : ℂ) +
        ((4 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) *
      Fourier.fourierIntegral Real.fourierChar volume
        (fun t => ((Real.exp (-σ * t) *
          harperCandidateSquarefreeLogProcess ω t : ℝ) : ℂ)) ξ := by
  have hc : Summable fun r : ℕ => ‖(candidateSquareTranslationWeight σ r : ℂ)‖ := by
    simpa only [Complex.norm_real] using
      (summable_candidateSquareTranslationWeight hσ).norm
  have hid : (fun t => ((Real.exp (-σ * t) *
      harperCandidateLogProcess ω t : ℝ) : ℂ)) =
      (fun t => ∑' r : ℕ, (candidateSquareTranslationWeight σ r : ℂ) *
        ((Real.exp (-σ * (t - 2 * Real.log r)) *
          harperCandidateSquarefreeLogProcess ω (t - 2 * Real.log r) : ℝ) : ℂ)) := by
    funext t
    rw [harperCandidateLogProcess_damped_eq_tsum_translates,
      Complex.ofReal_tsum]
    apply tsum_congr
    intro r
    exact Complex.ofReal_mul _ _
  rw [hid, candidate_fourier_tsum_translates hm hc
    (fun r => 2 * Real.log r) ξ,
    candidate_square_translation_multiplier_eq_zeta hσ]

/-- The candidate's angular-frequency convention gives precisely
`ζ(1+2σ+2iτ)`; no denominator rounding or analytic continuation is used. -/
theorem harperCandidateLogProcess_fourier_angular_eq_zeta_mul
    (ω : Omega) {σ : ℝ} (hσ : 0 < σ)
    (hm : Integrable fun t : ℝ =>
      ((Real.exp (-σ * t) * harperCandidateSquarefreeLogProcess ω t : ℝ) : ℂ))
    (τ : ℝ) :
    Fourier.fourierIntegral Real.fourierChar volume
      (fun t => ((Real.exp (-σ * t) * harperCandidateLogProcess ω t : ℝ) : ℂ))
      (τ / (2 * Real.pi)) =
      riemannZeta (((1 + 2 * σ : ℝ) : ℂ) + ((2 * τ : ℝ) : ℂ) * Complex.I) *
      Fourier.fourierIntegral Real.fourierChar volume
        (fun t => ((Real.exp (-σ * t) *
          harperCandidateSquarefreeLogProcess ω t : ℝ) : ℂ)) (τ / (2 * Real.pi)) := by
  have hfreq : 4 * Real.pi * (τ / (2 * Real.pi)) = 2 * τ := by
    field_simp
    ring
  simpa only [hfreq] using
    harperCandidateLogProcess_fourier_eq_zeta_mul ω hσ hm (τ / (2 * Real.pi))

end Erdos.Problem1144

#print axioms Erdos.Problem1144.candidate_fourier_tsum_translates
#print axioms Erdos.Problem1144.candidate_square_translation_multiplier_eq_zeta
#print axioms Erdos.Problem1144.harperCandidateLogProcess_fourier_eq_zeta_mul
#print axioms Erdos.Problem1144.harperCandidateLogProcess_fourier_angular_eq_zeta_mul
