import Erdos.Problem1144.HarperCandidateSpectralIntegrability
import Erdos.Problem1144.HarperCandidateZetaWindow

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144

/-- The angular Fourier density of a damped log-time kernel. Identifying its
Gram matrix with the time-domain covariance additionally requires Plancherel. -/
noncomputable def candidateLogSpectralDensity
    (a : ℝ → ℝ) (σ L τ : ℝ) : ℝ :=
  ‖Fourier.fourierIntegral Real.fourierChar volume
    (fun t => ((Real.exp (-σ * t) * a t : ℝ) : ℂ)) (τ / (2 * Real.pi))‖ ^ 2 /
      (2 * Real.pi * L)

/-- The exact Fourier identity and a reciprocal-zeta bound give pointwise
spectral domination, with the two normalization scales kept explicit. -/
theorem candidate_complete_spectralDensity_ge_squarefree
    (ω : Omega) {σ T V B τ : ℝ} (hσ : 0 < σ) (hT : 0 < T) (hV : 0 < V)
    (hm : Integrable fun t => Real.exp (-σ * t) *
      harperCandidateSquarefreeLogProcess ω t)
    (hB : 1 / ‖riemannZeta (((1 + 2 * σ : ℝ) : ℂ) +
      ((2 * τ : ℝ) : ℂ) * Complex.I)‖ ≤ B) :
    V / (T * B ^ 2) *
        candidateLogSpectralDensity (harperCandidateSquarefreeLogProcess ω) σ V τ ≤
      candidateLogSpectralDensity (harperCandidateLogProcess ω) σ T τ := by
  let z : ℂ := riemannZeta (((1 + 2 * σ : ℝ) : ℂ) +
    ((2 * τ : ℝ) : ℂ) * Complex.I)
  have hz : z ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    dsimp
    simp only [Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_self, add_zero]
    linarith
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hBpos : 0 < B := (one_div_pos.mpr hzn).trans_le hB
  have hnorm := congrArg norm
    (harperCandidateLogProcess_fourier_angular_eq_zeta_mul ω hσ hm.ofReal τ)
  rw [norm_mul] at hnorm
  have hrec : 1 ≤ B * ‖z‖ := (div_le_iff₀ hzn).mp hB
  have hsq : 1 ≤ B ^ 2 * ‖z‖ ^ 2 := by nlinarith [sq_nonneg (B * ‖z‖ - 1)]
  unfold candidateLogSpectralDensity
  rw [hnorm, mul_pow]
  change V / (T * B ^ 2) * (_ / (2 * Real.pi * V)) ≤
    ‖z‖ ^ 2 * _ / (2 * Real.pi * T)
  have hpi : 0 < Real.pi := Real.pi_pos
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi * T)).mpr
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right hsq
    (sq_nonneg ‖Fourier.fourierIntegral Real.fourierChar volume
      (fun t => ((Real.exp (-σ * t) *
        harperCandidateSquarefreeLogProcess ω t : ℝ) : ℂ)) (τ / (2 * Real.pi))‖)]

/-- The candidate's actual spectral window admits a uniform pointwise
comparison under every fixed cylinder. The seventh-log reciprocal-zeta bound
already proved in the project gives the fourteenth-log squared loss. -/
theorem exists_candidate_complete_spectralDensity_window_domination :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : ℝ), 0 < κ →
      ∀ᶠ T : ℝ in atTop, ∀ (s : Finset ℕ) (η : s → Bool),
        ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ τ : ℝ, |τ| ≤ Real.log T ^ 2 →
          1 / ((κ * Real.log (Real.log T)) *
              (C * Real.log (2 * Real.log T ^ 2 + 4) ^ 7) ^ 2) *
            candidateLogSpectralDensity (harperCandidateSquarefreeLogProcess ω)
              (κ * Real.log (Real.log T) / T)
              (T / (κ * Real.log (Real.log T))) τ ≤
          candidateLogSpectralDensity (harperCandidateLogProcess ω)
            (κ * Real.log (Real.log T) / T) T τ := by
  obtain ⟨C, hC, hwindow⟩ := exists_harperZetaInv_candidateWindow
  refine ⟨C, hC, fun κ hκ => ?_⟩
  filter_upwards [hwindow κ hκ.le, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop 1] with T hwin hT hlog
  have hW : 0 < κ * Real.log (Real.log T) :=
    mul_pos hκ (Real.log_pos hlog)
  have hσ : 0 < κ * Real.log (Real.log T) / T := div_pos hW hT
  intro s η
  filter_upwards [candidateCylinderLaw_ae_integrable_squarefree_damped s η hσ] with ω hω
  intro τ hτ
  have hscale : 1 / ((κ * Real.log (Real.log T)) *
        (C * Real.log (2 * Real.log T ^ 2 + 4) ^ 7) ^ 2) =
      (T / (κ * Real.log (Real.log T))) /
        (T * (C * Real.log (2 * Real.log T ^ 2 + 4) ^ 7) ^ 2) := by
    field_simp
  rw [hscale]
  apply candidate_complete_spectralDensity_ge_squarefree ω hσ hT (div_pos hT hW) hω
  apply hwin
  · constructor
    · linarith [hσ]
    · dsimp
      ring_nf
      exact le_rfl
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

end Erdos.Problem1144

#print axioms Erdos.Problem1144.candidate_complete_spectralDensity_ge_squarefree
#print axioms Erdos.Problem1144.exists_candidate_complete_spectralDensity_window_domination
