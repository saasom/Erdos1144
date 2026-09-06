import Erdos.Problem1144.HarperCandidateSpectralParseval

open MeasureTheory Set
open scoped ENNReal

namespace Erdos.Problem1144

private theorem candidate_integrable_damped_linear_moment
    (a : Omega → ℝ → ℝ)
    (ha : Measurable fun z : Omega × ℝ => a z.1 z.2)
    (hi : ∀ t, Integrable (fun ω => a ω t) mu)
    (hb : ∀ t, 0 ≤ t → (∫ ω, |a ω t| ∂mu) ≤ 2 + t)
    (hz : ∀ ω t, t < 0 → a ω t = 0)
    {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun z : ℝ × Omega => Real.exp (-σ * z.1) * a z.2 z.1)
      (volume.prod mu) := by
  let B : ℝ → ℝ := (Ici 0).indicator (fun t => Real.exp (-σ * t) * (2 + t))
  have hB : Integrable B := by
    apply (integrable_indicator_iff measurableSet_Ici).mpr
    apply (integrableOn_Ici_iff_integrableOn_Ioi (μ := volume)).mpr
    simpa only [div_inv_eq_mul, mul_neg, neg_mul, mul_comm] using
      candidate_integrable_laplace_majorant (inv_pos.mpr hσ)
  have hF : Measurable fun z : ℝ × Omega => Real.exp (-σ * z.1) * a z.2 z.1 :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
      (ha.comp measurable_swap)
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun t => (hi t).const_mul (Real.exp (-σ * t))
  · apply hB.mono' hF.norm.aestronglyMeasurable.integral_prod_right'
    filter_upwards [] with t
    by_cases ht : 0 ≤ t
    · simp only [B, indicator, mem_Ici, if_pos ht]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simp_rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos _).le
    · simp only [hz _ _ (lt_of_not_ge ht), mul_zero, norm_zero, integral_zero]
      simp [B, ht]

/-- The literal complete damped paths are integrable on the whole time line. -/
theorem candidate_ae_integrable_complete_damped {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂mu, Integrable (fun t => Real.exp (-σ * t) *
      harperCandidateLogProcess ω t) := by
  apply (candidate_integrable_damped_linear_moment harperCandidateLogProcess
    measurable_harperCandidateLogProcess candidate_integrable_logProcess
    (fun _ ht => candidate_integral_abs_logProcess_le ht) _ hσ).prod_left_ae
  intro ω t ht
  simp [harperCandidateLogProcess, not_le.mpr ht]

private theorem candidate_ae_memLp_damped_of_second_moment
    (a : Omega → ℝ → ℝ)
    (ha : Measurable fun z : Omega × ℝ => a z.1 z.2)
    (hi : ∀ t, Integrable (fun ω => a ω t ^ 2) mu)
    (hb : ∀ t, 0 ≤ t → (∫ ω, a ω t ^ 2 ∂mu) ≤ 2 + t)
    (hz : ∀ ω t, t < 0 → a ω t = 0)
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂mu, MemLp (fun t => Real.exp (-σ * t) * a ω t) 2 := by
  have hp := candidate_integrable_damped_linear_moment
    (fun ω t => a ω t ^ 2) (ha.pow_const 2) hi
    (fun t ht => by simpa only [abs_sq] using hb t ht)
    (fun ω t ht => by simp [hz ω t ht]) (by positivity : 0 < 2 * σ)
  filter_upwards [hp.prod_left_ae] with ω hω
  have hm : Measurable fun t => Real.exp (-σ * t) * a ω t :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (ha.comp measurable_prodMk_left)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  convert hω using 1
  funext t
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

/-- Squarefree orthogonality gives actual `L²` damped paths almost surely. -/
theorem candidate_ae_memLp_squarefree_damped {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂mu, MemLp (fun t => Real.exp (-σ * t) *
      harperCandidateSquarefreeLogProcess ω t) 2 := by
  apply candidate_ae_memLp_damped_of_second_moment
    harperCandidateSquarefreeLogProcess measurable_harperCandidateSquarefreeLogProcess
    (fun t => candidate_integrable_squarefreeLog_pow t 2) _ _ hσ
  · intro t ht
    exact (candidate_integral_squarefreeLog_sq_le_one t).trans (by linarith)
  · intro ω t ht
    simp [harperCandidateSquarefreeLogProcess, not_le.mpr ht]

/-- The complete-model second moment gives actual `L²` damped paths. -/
theorem candidate_ae_memLp_complete_damped {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂mu, MemLp (fun t => Real.exp (-σ * t) *
      harperCandidateLogProcess ω t) 2 := by
  apply candidate_ae_memLp_damped_of_second_moment
    harperCandidateLogProcess measurable_harperCandidateLogProcess
    candidate_integrable_logProcess_sq _ _ hσ
  · intro t ht
    exact (candidate_integral_logProcess_sq_le ht).trans (by linarith)
  · intro ω t ht
    simp [harperCandidateLogProcess, not_le.mpr ht]

/-- Both literal paths satisfy the hypotheses of Parseval under every finite
cylinder. There is no pathwise or spectral regularity premise. -/
theorem candidateCylinderLaw_ae_damped_L1_L2
    (s : Finset ℕ) (η : s → Bool) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂candidateCylinderLaw s η,
      (Integrable (fun t => Real.exp (-σ * t) * harperCandidateLogProcess ω t) ∧
       MemLp (fun t => Real.exp (-σ * t) * harperCandidateLogProcess ω t) 2) ∧
      (Integrable (fun t => Real.exp (-σ * t) * harperCandidateSquarefreeLogProcess ω t) ∧
       MemLp (fun t => Real.exp (-σ * t) * harperCandidateSquarefreeLogProcess ω t) 2) := by
  apply ProbabilityTheory.cond_absolutelyContinuous.ae_le
  filter_upwards [candidate_ae_integrable_complete_damped hσ,
    candidate_ae_memLp_complete_damped hσ, candidate_ae_integrable_squarefree_damped hσ,
    candidate_ae_memLp_squarefree_damped hσ] with ω ha₁ ha₂ hm₁ hm₂
  exact ⟨⟨ha₁, ha₂⟩, ⟨hm₁, hm₂⟩⟩

end Erdos.Problem1144
