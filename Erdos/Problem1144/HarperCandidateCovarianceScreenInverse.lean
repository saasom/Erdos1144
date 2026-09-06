import Erdos.Problem1144.HarperCandidateCovariancePerronErrorWhite

open MeasureTheory Set FourierTransform
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- Literal inverse angular transform over a measurable frequency screen. -/
def candidateCovarianceScreenInverse (A : ℝ → ℂ) (S : Set ℝ) (u : ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ τ in S, A τ * candidateCovariancePhase (u * τ)

/-- Restricting the integrand inside a containing band gives precisely the
literal screened inverse, with no extra cutoff or normalization. -/
theorem candidate_screenInverse_eq_bandInverse (A : ℝ → ℂ) {S : Set ℝ}
    (hS : MeasurableSet S) (H : ℝ) (hsub : S ⊆ Icc (-H) H) (u : ℝ) :
    candidateCovarianceScreenInverse A S u = candidateCovarianceBandInverse (S.indicator A) H u := by
  unfold candidateCovarianceScreenInverse candidateCovarianceBandInverse
  congr 1
  have he (τ : ℝ) : S.indicator A τ * candidateCovariancePhase (u * τ) =
      S.indicator (fun τ => A τ * candidateCovariancePhase (u * τ)) τ := by
    by_cases hτ : τ ∈ S <;> simp [hτ]
  simp_rw [he]
  rw [integral_indicator hS, Measure.restrict_restrict hS, inter_eq_left.mpr hsub]

/-- Exact conversion between the angular screen and the standard Fourier
frequency, including its factor `1/(2π)`. -/
theorem candidate_screenInverse_eq_fourierInv (A : ℝ → ℂ) {S : Set ℝ}
    (hS : MeasurableSet S) (u : ℝ) :
    candidateCovarianceScreenInverse A S u =
      (𝓕⁻ (fun ξ => S.indicator A (2 * Real.pi * ξ))) u := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq]
  simp only [mul_neg, neg_neg, Circle.smul_def, smul_eq_mul]
  let g : ℝ → ℂ := S.indicator (fun τ => A τ * candidateCovariancePhase (u * τ))
  have he (ξ : ℝ) :
      (Real.fourierChar (ξ * u) : ℂ) * S.indicator A (2 * Real.pi * ξ) =
        g (2 * Real.pi * ξ) := by
    by_cases hξ : 2 * Real.pi * ξ ∈ S
    · simp only [g, indicator_of_mem hξ, Real.fourierChar_apply, candidateCovariancePhase]
      have hp : 2 * Real.pi * (ξ * u) = u * (2 * Real.pi * ξ) := by ring
      rw [hp]
      ring
    · simp [g, hξ]
  simp_rw [he]
  rw [Measure.integral_comp_mul_left,
    abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)]
  simp only [g, integral_indicator hS, candidateCovarianceScreenInverse]
  change (2 * Real.pi : ℂ)⁻¹ * _ = ((2 * Real.pi)⁻¹ : ℝ) • _
  rw [Complex.real_smul]
  simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- The actual screened inverse is measurable in its time endpoint. -/
theorem candidate_measurable_screenInverse {A : ℝ → ℂ} (hA : Measurable A)
    (S : Set ℝ) : Measurable (candidateCovarianceScreenInverse A S) := by
  have hm : Measurable (fun z : ℝ × ℝ => A z.2 * candidateCovariancePhase (z.1 * z.2)) := by
    have h : Measurable (fun z : ℝ × ℝ => A z.2) := hA.comp measurable_snd
    unfold candidateCovariancePhase
    fun_prop
  exact (StronglyMeasurable.integral_prod_right
    (f := fun u τ => A τ * candidateCovariancePhase (u * τ))
    (ν := volume.restrict S) hm.stronglyMeasurable).measurable.const_mul _

private theorem scaled_screen_integrable {A : ℝ → ℂ} (hA : Continuous A) {S : Set ℝ}
    (hS : MeasurableSet S) (H : ℝ) (hsub : S ⊆ Icc (-H) H) :
    Integrable (fun ξ => S.indicator A (2 * Real.pi * ξ)) ∧
      MemLp (fun ξ => S.indicator A (2 * Real.pi * ξ)) 2 := by
  have hi : Integrable (S.indicator A) :=
    (hA.integrableOn_Icc.mono_set hsub).integrable_indicator hS
  have hn : Integrable (S.indicator (fun τ => ‖A τ‖ ^ 2)) :=
    ((hA.norm.pow 2).integrableOn_Icc.mono_set hsub).integrable_indicator hS
  have he : (fun τ => ‖S.indicator A τ‖ ^ 2) = S.indicator (fun τ => ‖A τ‖ ^ 2) := by
    funext τ
    by_cases hτ : τ ∈ S <;> simp [hτ]
  have h2 : Integrable (fun τ => ‖S.indicator A τ‖ ^ 2) := he ▸ hn
  have hscale : 2 * Real.pi ≠ 0 := by positivity
  refine ⟨hi.comp_mul_left' hscale, ?_⟩
  apply (memLp_two_iff_integrable_sq_norm (hi.comp_mul_left' hscale).aestronglyMeasurable).mpr
  exact h2.comp_mul_left' hscale

/-- Every bounded measurable frequency screen of the literal continuous
Euler transform has a square-integrable inverse. -/
theorem candidate_memLp_two_screenInverse {A : ℝ → ℂ} (hA : Continuous A) {S : Set ℝ}
    (hS : MeasurableSet S) (H : ℝ) (hsub : S ⊆ Icc (-H) H) :
    MemLp (candidateCovarianceScreenInverse A S) 2 := by
  obtain ⟨hi, h2⟩ := scaled_screen_integrable hA hS H hsub
  have he : candidateCovarianceScreenInverse A S =
      𝓕⁻ (fun ξ => S.indicator A (2 * Real.pi * ξ)) :=
    funext (candidate_screenInverse_eq_fourierInv A hS)
  rw [he]
  exact (memLp_congr_ae (candidate_literal_fourierInv_eq_L2_ae hi h2)).mpr
    (Lp.memLp (𝓕⁻ h2.toLp))

/-- Parseval for a literal measurable angular screen. The output is the
actual time integral, with exact normalization and no Plancherel premise. -/
theorem candidate_screenInverse_norm_sq_integral_eq {A : ℝ → ℂ} (hA : Continuous A)
    {S : Set ℝ} (hS : MeasurableSet S) (H : ℝ) (hsub : S ⊆ Icc (-H) H) :
    (∫ u, ‖candidateCovarianceScreenInverse A S u‖ ^ 2) =
      (2 * Real.pi)⁻¹ * ∫ τ in S, ‖A τ‖ ^ 2 := by
  obtain ⟨hi, h2⟩ := scaled_screen_integrable hA hS H hsub
  simp_rw [candidate_screenInverse_eq_fourierInv A hS, Real.fourierInv_eq_fourier_neg]
  have hn : (∫ u, ‖(𝓕 (fun ξ => S.indicator A (2 * Real.pi * ξ))) (-u)‖ ^ 2) =
      ∫ u, ‖(𝓕 (fun ξ => S.indicator A (2 * Real.pi * ξ))) u‖ ^ 2 :=
    integral_neg_eq_self (fun x => ‖(𝓕 (fun ξ => S.indicator A (2 * Real.pi * ξ))) x‖ ^ 2) volume
  rw [hn, candidate_literal_fourier_norm_sq_integral_eq hi h2]
  have he (ξ : ℝ) : ‖S.indicator A (2 * Real.pi * ξ)‖ ^ 2 =
      S.indicator (fun τ => ‖A τ‖ ^ 2) (2 * Real.pi * ξ) := by
    by_cases hξ : 2 * Real.pi * ξ ∈ S <;> simp [hξ]
  simp_rw [he]
  rw [Measure.integral_comp_mul_left, abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹),
    smul_eq_mul, integral_indicator hS]

/-- Deleting frequencies from the full band is exactly inverse-transforming
the deleted frequencies. This is an equality of the literal integrals. -/
theorem candidate_bandInverse_sub_screenInverse {A : ℝ → ℂ} (hA : Continuous A)
    {S : Set ℝ} (hS : MeasurableSet S) (H : ℝ) (hsub : S ⊆ Icc (-H) H) (u : ℝ) :
    candidateCovarianceBandInverse A H u - candidateCovarianceScreenInverse A S u =
      candidateCovarianceScreenInverse A (Icc (-H) H \ S) u := by
  let f : ℝ → ℂ := fun τ => A τ * candidateCovariancePhase (u * τ)
  have hf : Continuous f := by unfold f candidateCovariancePhase; fun_prop
  have hB : Integrable ((Icc (-H) H).indicator f) := hf.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hSi : Integrable (S.indicator f) := (hf.integrableOn_Icc.mono_set hsub).integrable_indicator hS
  unfold candidateCovarianceBandInverse candidateCovarianceScreenInverse
  rw [← mul_sub, ← integral_indicator measurableSet_Icc, ← integral_indicator hS,
    ← integral_indicator (measurableSet_Icc.diff hS)]
  change _ * ((∫ τ, (Icc (-H) H).indicator f τ) - ∫ τ, S.indicator f τ) =
    _ * ∫ τ, (Icc (-H) H \ S).indicator f τ
  rw [← integral_sub hB hSi]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun τ => by
    by_cases hτ : τ ∈ S
    · simp [hτ, hsub hτ]
    · by_cases hBτ : τ ∈ Icc (-H) H <;> simp [hτ, hBτ]

/-- Exact global deletion energy, uniform in subsequent time translations. -/
theorem candidate_screenInverse_deletion_energy_eq {A : ℝ → ℂ} (hA : Continuous A)
    {S : Set ℝ} (hS : MeasurableSet S) (H : ℝ) (hsub : S ⊆ Icc (-H) H) :
    (∫ u, ‖candidateCovarianceBandInverse A H u - candidateCovarianceScreenInverse A S u‖ ^ 2) =
      (2 * Real.pi)⁻¹ * ∫ τ in Icc (-H) H \ S, ‖A τ‖ ^ 2 := by
  simp_rw [candidate_bandInverse_sub_screenInverse hA hS H hsub]
  exact candidate_screenInverse_norm_sq_integral_eq hA (measurableSet_Icc.diff hS) H
    (fun _ hx => hx.1)

/-- Conjugation symmetry is preserved by a symmetric measurable screen. -/
theorem candidate_screenInverse_conj {A : ℝ → ℂ} (hA : ∀ τ, starRingEnd ℂ (A τ) = A (-τ))
    {S : Set ℝ} (hS : MeasurableSet S) (hSym : ∀ τ, τ ∈ S ↔ -τ ∈ S) (u : ℝ) :
    starRingEnd ℂ (candidateCovarianceScreenInverse A S u) = candidateCovarianceScreenInverse A S u := by
  have hi (f : ℝ → ℂ) : (∫ τ in S, f (-τ)) = ∫ τ in S, f τ := by
    rw [← integral_indicator hS, ← integral_indicator hS]
    have he (τ : ℝ) : S.indicator (fun τ => f (-τ)) τ = S.indicator f (-τ) := by
      by_cases hτ : τ ∈ S <;> simp [hτ, (hSym τ).mp, (hSym τ).not.mp]
    simp_rw [he]
    exact integral_neg_eq_self _ volume
  unfold candidateCovarianceScreenInverse
  rw [map_mul]
  have hc : starRingEnd ℂ (2 * Real.pi : ℂ)⁻¹ = (2 * Real.pi : ℂ)⁻¹ := by
    rw [map_inv₀, map_mul, (show starRingEnd ℂ (2 : ℂ) = 2 from Complex.conj_ofReal 2),
      Complex.conj_ofReal]
  rw [hc]
  have hic : starRingEnd ℂ (∫ τ in S, A τ * candidateCovariancePhase (u * τ)) =
      ∫ τ in S, starRingEnd ℂ (A τ * candidateCovariancePhase (u * τ)) := integral_conj.symm
  rw [hic]
  have he (τ : ℝ) : starRingEnd ℂ (A τ * candidateCovariancePhase (u * τ)) =
      A (-τ) * candidateCovariancePhase (u * (-τ)) := by
    rw [map_mul, hA]
    congr 1
    simp [candidateCovariancePhase, ← Complex.exp_conj]
  simp_rw [he]
  rw [hi (fun τ => A τ * candidateCovariancePhase (u * τ))]

end
end Erdos.Problem1144
