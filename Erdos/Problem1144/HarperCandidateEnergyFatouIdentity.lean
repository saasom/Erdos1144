import Erdos.Problem1144.HarperCandidateEulerLimit
import Erdos.Problem1144.HarperCandidateFiniteSpectralEnergy
import Erdos.Problem1144.HarperCandidateDampedCompleteEnergy

open Finset MeasureTheory Set Filter FourierTransform
open scoped BigOperators Topology

namespace Erdos.Problem1144
noncomputable section

/-- The finite real-sign Euler density is even in angular frequency. -/
theorem candidate_shifted_euler_density_neg (Y : ℕ) (a : ℝ) (ω : Omega) (τ : ℝ) :
    harperRankinEulerDensity Y a ω (-τ) = harperRankinEulerDensity Y a ω τ := by
  simp only [harperRankinEulerDensity, harperRankinEulerFactor, neg_mul,
    Real.cos_neg, Real.sin_neg, mul_neg, neg_sq]

/-- The full zeta weight times the finite squarefree Euler density is exactly
the squared norm of the corresponding finite approximation to the complete
angular Fourier transform. Zeta is never truncated. -/
theorem candidate_euler_weight_eq_norm (Y : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (ω : Omega) (τ : ℝ) :
    candidateCompleteZetaWeight σ τ * harperRankinEulerDensity Y (2 * σ) ω τ =
      ‖riemannZeta ((1 + 2 * σ : ℝ) + (2 * τ : ℝ) * Complex.I) *
        candidateEulerAngularApprox Y σ ω τ‖ ^ 2 := by
  have he : harperRankinEulerDensity Y (2 * σ) ω τ =
      ‖harperRankinDirichletPolynomial Y (2 * σ) ω (-τ)‖ ^ 2 := by
    rw [← candidate_shifted_euler_density_neg Y (2 * σ) ω τ,
      harperRankinEulerDensity_eq_normSq_dirichletPolynomial _ _ _ _ (by positivity),
      Complex.sq_norm]
  have hd : ‖(((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 =
      (1 / 2 + σ) ^ 2 + τ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_I_re, Complex.mul_I_im, neg_zero, add_zero, zero_add]
    ring
  rw [candidateCompleteZetaWeight, he, norm_mul, mul_pow,
    candidateEulerAngularApprox, norm_div, div_pow, hd]
  ring

/-- Exact almost-sure Parseval identification of the actual damped complete
energy with the full zeta-weighted squarefree Fourier energy. -/
theorem candidate_ae_dampedEnergy_fourier_identity {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂mu,
      Integrable (fun τ => ‖riemannZeta ((1 + 2 * σ : ℝ) +
        (2 * τ : ℝ) * Complex.I) * candidateSquarefreeAngularFourier ω σ τ‖ ^ 2) ∧
      2 * Real.pi * candidateDampedCompleteEnergy σ ω =
        σ * ∫ τ, ‖riemannZeta ((1 + 2 * σ : ℝ) + (2 * τ : ℝ) * Complex.I) *
          candidateSquarefreeAngularFourier ω σ τ‖ ^ 2 := by
  filter_upwards [candidate_ae_integrable_complete_damped hσ,
    candidate_ae_memLp_complete_damped hσ, candidate_ae_fourier_angular_eq_zeta_mul hσ]
    with ω h₁ h₂ he
  let f : ℝ → ℂ := fun t => ((Real.exp (-σ * t) * harperCandidateLogProcess ω t : ℝ) : ℂ)
  let H : ℝ → ℂ := fun ξ => Fourier.fourierIntegral Real.fourierChar volume f ξ
  have hf₁ : Integrable f := h₁.ofReal
  have hf₂ : MemLp f 2 := h₂.ofReal
  have hH : Integrable (fun ξ => ‖H ξ‖ ^ 2) := by
    simpa only [H, Real.fourier_real_eq, Fourier.fourierIntegral_def] using
      (candidate_literal_fourier_memLp_two hf₁ hf₂).integrable_norm_pow (by decide : 2 ≠ 0)
  have hParseval : (∫ ξ, ‖H ξ‖ ^ 2) = ∫ t, ‖f t‖ ^ 2 := by
    simpa only [H, Real.fourier_real_eq, Fourier.fourierIntegral_def] using
      candidate_literal_fourier_norm_sq_integral_eq hf₁ hf₂
  have hfull (τ : ℝ) : H (τ / (2 * Real.pi)) =
      riemannZeta ((1 + 2 * σ : ℝ) + (2 * τ : ℝ) * Complex.I) *
        candidateSquarefreeAngularFourier ω σ τ := he τ
  have htime : (∫ t, ‖f t‖ ^ 2) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-2 * σ * t) * harperCandidateLogProcess ω t ^ 2 := by
    have ht (t : ℝ) : ‖f t‖ ^ 2 =
        (Ici (0 : ℝ)).indicator
          (fun t => Real.exp (-2 * σ * t) * harperCandidateLogProcess ω t ^ 2) t := by
      by_cases ht : 0 ≤ t
      · rw [Set.indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht)]
        simp only [f, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
        rw [← Real.exp_nat_mul]
        congr 2
        ring
      · simp [f, harperCandidateLogProcess, ht]
    simp_rw [ht]
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  constructor
  · have h := hH.comp_div (by positivity : 2 * Real.pi ≠ 0)
    simpa only [hfull] using h
  · simp_rw [← hfull]
    change 2 * Real.pi * candidateDampedCompleteEnergy σ ω =
      σ * ∫ τ, ‖H (τ / (2 * Real.pi))‖ ^ 2
    rw [Measure.integral_comp_div (g := fun ξ => ‖H ξ‖ ^ 2), abs_of_pos (by positivity : 0 < 2 * Real.pi),
      smul_eq_mul, hParseval, htime, candidateDampedCompleteEnergy]
    ring

end
end Erdos.Problem1144
