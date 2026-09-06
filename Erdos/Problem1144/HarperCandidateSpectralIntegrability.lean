import Erdos.Problem1144.HarperCandidateSpectralTransform
import Erdos.Problem1144.HarperCandidateGaussianVariance
import Erdos.Problem1144.HarperCandidateLaplaceIntegrability
import Erdos.Problem520.CaichWoverX

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-- Squarefree orthogonality bounds the second moment by the literal cutoff. -/
theorem candidate_integral_GSquarefree_sq_le (N : ℕ) :
    (∫ ω, GSquarefree ω N ^ 2 ∂mu) ≤ (N : ℝ) := by
  simpa only [GSquarefree, candidate_gSquarefree_eq_problem520,
    Nat.card_Icc, Nat.add_sub_cancel] using
      Problem520.integral_sq_sum_f_finset_le_card (Finset.Icc 1 N)

/-- All fixed-time squarefree powers are integrable under the sign law. -/
theorem candidate_integrable_squarefreeLog_pow (t : ℝ) (k : ℕ) :
    Integrable (fun ω => harperCandidateSquarefreeLogProcess ω t ^ k) mu := by
  apply Integrable.of_bound
    ((measurable_harperCandidateSquarefreeLogProcess.comp
      measurable_prodMk_right).pow_const k).aestronglyMeasurable
    (Real.exp (t / 2) ^ k)
  filter_upwards [] with ω
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (candidate_squarefree_log_abs_le_exp_half ω le_rfl) _

/-- Normalization converts squarefree orthogonality into a uniform second
moment bound, with no asymptotic error from the floor. -/
theorem candidate_integral_squarefreeLog_sq_le_one (t : ℝ) :
    (∫ ω, harperCandidateSquarefreeLogProcess ω t ^ 2 ∂mu) ≤ 1 := by
  simp_rw [harperCandidateSquarefreeLogProcess_eq_quotient, div_pow]
  rw [integral_div]
  have hexp : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp, div_le_one (Real.exp_pos t)]
  exact (candidate_integral_GSquarefree_sq_le _).trans
    (Nat.floor_le (Real.exp_pos t).le)

/-- A uniform absolute first moment follows directly from the second moment. -/
theorem candidate_integral_abs_squarefreeLog_le_two (t : ℝ) :
    (∫ ω, |harperCandidateSquarefreeLogProcess ω t| ∂mu) ≤ 2 := by
  have hfirst : Integrable (fun ω => harperCandidateSquarefreeLogProcess ω t) mu := by
    simpa only [pow_one] using candidate_integrable_squarefreeLog_pow t 1
  have hsecond := candidate_integrable_squarefreeLog_pow t 2
  have h := integral_mono hfirst.abs (hsecond.add (integrable_const (1 : ℝ)))
    (fun ω => show |harperCandidateSquarefreeLogProcess ω t| ≤
        harperCandidateSquarefreeLogProcess ω t ^ 2 + 1 by
      nlinarith [sq_nonneg (|harperCandidateSquarefreeLogProcess ω t| - 1),
        sq_abs (harperCandidateSquarefreeLogProcess ω t)])
  simp only [Pi.add_apply] at h
  rw [integral_add hsecond (integrable_const (1 : ℝ))] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  linarith [candidate_integral_squarefreeLog_sq_le_one t]

/-- Joint L1 integrability of each positively damped squarefree path follows
from the uniform squarefree first moment and Fubini. -/
theorem candidate_integrable_squarefree_damped_product {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun z : ℝ × Omega => Real.exp (-σ * z.1) *
      harperCandidateSquarefreeLogProcess z.2 z.1) ((volume.restrict (Ioi 0)).prod mu) := by
  let F : ℝ × Omega → ℝ := fun z => Real.exp (-σ * z.1) *
    harperCandidateSquarefreeLogProcess z.2 z.1
  have hF : Measurable F :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
      (measurable_harperCandidateSquarefreeLogProcess.comp measurable_swap)
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-σ * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hσ) 0
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  constructor
  · apply ae_of_all
    intro t
    have hi : Integrable (fun ω => harperCandidateSquarefreeLogProcess ω t) mu := by
      simpa only [pow_one] using candidate_integrable_squarefreeLog_pow t 1
    exact hi.const_mul (Real.exp (-σ * t))
  · apply (hexp.mul_const 2).mono'
      hF.norm.aestronglyMeasurable.integral_prod_right'
    filter_upwards [] with t
    change ‖∫ ω, ‖Real.exp (-σ * t) * harperCandidateSquarefreeLogProcess ω t‖ ∂mu‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp_rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (candidate_integral_abs_squarefreeLog_le_two t)
      (Real.exp_pos _).le

/-- Extending a squarefree path by zero at negative times preserves the L1
conclusion; the single endpoint at zero has no effect. -/
theorem candidate_squarefree_damped_integrable_of_integrableOn
    (ω : Omega) (σ : ℝ)
    (h : IntegrableOn (fun t => Real.exp (-σ * t) *
      harperCandidateSquarefreeLogProcess ω t) (Ioi 0)) :
    Integrable (fun t => Real.exp (-σ * t) * harperCandidateSquarefreeLogProcess ω t) := by
  have hneg : IntegrableOn (fun t => Real.exp (-σ * t) *
      harperCandidateSquarefreeLogProcess ω t) (Iio 0) := by
    apply (integrableOn_zero (μ := volume) (s := Iio (0 : ℝ))).congr_fun
      _ measurableSet_Iio
    intro t ht
    change t < 0 at ht
    simp [harperCandidateSquarefreeLogProcess, not_le.mpr ht]
  have hpos : IntegrableOn (fun t => Real.exp (-σ * t) *
      harperCandidateSquarefreeLogProcess ω t) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi'
      (by simp : volume ({(0 : ℝ)} : Set ℝ) ≠ ⊤)).mpr h
  simpa only [Iio_union_Ici, integrableOn_univ] using hneg.union hpos

/-- Every positive damping rate gives an integrable squarefree path almost
surely; this is proved from orthogonality, without a spectral assumption. -/
theorem candidate_ae_integrable_squarefree_damped {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂mu, Integrable (fun t => Real.exp (-σ * t) *
      harperCandidateSquarefreeLogProcess ω t) := by
  filter_upwards [(candidate_integrable_squarefree_damped_product hσ).prod_left_ae] with ω hω
  exact candidate_squarefree_damped_integrable_of_integrableOn ω σ hω

/-- Every finite-cylinder conditional law inherits squarefree L1
integrability, since it is absolutely continuous with respect to the sign law. -/
theorem candidateCylinderLaw_ae_integrable_squarefree_damped
    (s : Finset ℕ) (η : s → Bool) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂candidateCylinderLaw s η, Integrable (fun t => Real.exp (-σ * t) *
      harperCandidateSquarefreeLogProcess ω t) :=
  ProbabilityTheory.cond_absolutelyContinuous.ae_le
    (candidate_ae_integrable_squarefree_damped hσ)

/-- The literal angular Fourier/zeta factorization holds almost surely,
simultaneously at every frequency, at each fixed positive damping rate. -/
theorem candidate_ae_fourier_angular_eq_zeta_mul {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂mu, ∀ τ : ℝ,
      Fourier.fourierIntegral Real.fourierChar volume
        (fun t => ((Real.exp (-σ * t) * harperCandidateLogProcess ω t : ℝ) : ℂ))
        (τ / (2 * Real.pi)) =
      riemannZeta (((1 + 2 * σ : ℝ) : ℂ) + ((2 * τ : ℝ) : ℂ) * Complex.I) *
      Fourier.fourierIntegral Real.fourierChar volume
        (fun t => ((Real.exp (-σ * t) *
          harperCandidateSquarefreeLogProcess ω t : ℝ) : ℂ)) (τ / (2 * Real.pi)) := by
  filter_upwards [candidate_ae_integrable_squarefree_damped hσ] with ω hω
  exact harperCandidateLogProcess_fourier_angular_eq_zeta_mul ω hσ hω.ofReal

/-- The actual spectral factorization is valid under every finite-prefix
conditioning, with no remaining integrability or factorization premise. -/
theorem candidateCylinderLaw_ae_fourier_angular_eq_zeta_mul
    (s : Finset ℕ) (η : s → Bool) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ τ : ℝ,
      Fourier.fourierIntegral Real.fourierChar volume
        (fun t => ((Real.exp (-σ * t) * harperCandidateLogProcess ω t : ℝ) : ℂ))
        (τ / (2 * Real.pi)) =
      riemannZeta (((1 + 2 * σ : ℝ) : ℂ) + ((2 * τ : ℝ) : ℂ) * Complex.I) *
      Fourier.fourierIntegral Real.fourierChar volume
        (fun t => ((Real.exp (-σ * t) *
          harperCandidateSquarefreeLogProcess ω t : ℝ) : ℂ)) (τ / (2 * Real.pi)) :=
  ProbabilityTheory.cond_absolutelyContinuous.ae_le
    (candidate_ae_fourier_angular_eq_zeta_mul hσ)

end Erdos.Problem1144

#print axioms Erdos.Problem1144.candidate_integral_GSquarefree_sq_le
#print axioms Erdos.Problem1144.candidate_integral_squarefreeLog_sq_le_one
#print axioms Erdos.Problem1144.candidate_ae_integrable_squarefree_damped
#print axioms Erdos.Problem1144.candidate_ae_fourier_angular_eq_zeta_mul
#print axioms Erdos.Problem1144.candidateCylinderLaw_ae_fourier_angular_eq_zeta_mul
