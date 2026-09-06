import Erdos.Problem1144.HarperCandidateCovariancePerronFinite

open MeasureTheory Set FourierTransform
open scoped Topology

namespace Erdos.Problem1144

private theorem scaled_band_mem (H ξ : ℝ) :
    ξ ∈ Icc (-(H / (2 * Real.pi))) (H / (2 * Real.pi)) ↔
      2 * Real.pi * ξ ∈ Icc (-H) H := by
  simp only [mem_Icc, ← neg_div, div_le_iff₀ (by positivity : 0 < 2 * Real.pi),
    le_div_iff₀ (by positivity : 0 < 2 * Real.pi), mul_comm ξ]

/-- The normalized inverse angular integral is exactly the literal inverse
Fourier transform with the angular cutoff pulled back by `τ=2πξ`. -/
theorem candidate_bandInverse_eq_fourierInv (A : ℝ → ℂ) (H u : ℝ) :
    candidateCovarianceBandInverse A H u =
      (𝓕⁻ (fun ξ => (Icc (-H) H).indicator A (2 * Real.pi * ξ))) u := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq]
  simp only [mul_neg, neg_neg, Circle.smul_def, smul_eq_mul]
  let g : ℝ → ℂ := fun τ =>
    (Icc (-H) H).indicator (fun τ => A τ * candidateCovariancePhase (u * τ)) τ
  have he (ξ : ℝ) :
      (Real.fourierChar (ξ * u) : ℂ) * (Icc (-H) H).indicator A (2 * Real.pi * ξ) =
        g (2 * Real.pi * ξ) := by
    by_cases hξ : 2 * Real.pi * ξ ∈ Icc (-H) H
    · simp only [g, indicator_of_mem hξ, Real.fourierChar_apply, candidateCovariancePhase]
      have hp : 2 * Real.pi * (ξ * u) = u * (2 * Real.pi * ξ) := by ring
      rw [hp]
      ring
    · simp [g, hξ]
  simp_rw [he]
  rw [Measure.integral_comp_mul_left,
    abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)]
  simp only [g, integral_indicator measurableSet_Icc]
  change (2 * Real.pi : ℂ)⁻¹ * _ = ((2 * Real.pi)⁻¹ : ℝ) • _
  rw [Complex.real_smul]
  simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- The standard frequency tail and angular tail differ by exactly `1/(2π)`. -/
theorem candidate_angular_tail_integral (F : ℝ → ℝ) (H : ℝ) :
    (∫ ξ in (Icc (-(H / (2 * Real.pi))) (H / (2 * Real.pi)))ᶜ,
      F (2 * Real.pi * ξ)) =
      (2 * Real.pi)⁻¹ * ∫ τ in (Icc (-H) H)ᶜ, F τ := by
  rw [← integral_indicator measurableSet_Icc.compl,
    ← integral_indicator measurableSet_Icc.compl]
  have he (ξ : ℝ) :
      (Icc (-(H / (2 * Real.pi))) (H / (2 * Real.pi)))ᶜ.indicator
        (fun ξ => F (2 * Real.pi * ξ)) ξ =
      (Icc (-H) H)ᶜ.indicator F (2 * Real.pi * ξ) := by
    by_cases hξ : ξ ∈ Icc (-(H / (2 * Real.pi))) (H / (2 * Real.pi))
    · simp [hξ, (scaled_band_mem H ξ).mp hξ]
    · simp [hξ, (scaled_band_mem H ξ).not.mp hξ]
  simp_rw [he]
  rw [Measure.integral_comp_mul_left,
    abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹), smul_eq_mul]

/-- Exact angular-frequency truncation error for the literal finite squarefree
Euler-support process, with the Parseval normalization made explicit. -/
theorem candidate_finiteEuler_angular_cutoff_error_eq (Y : ℕ) (ω : Omega) (H : ℝ) :
    (∫ x, ‖candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H x -
      candidateEulerLogProcess Y ω x‖ ^ 2) =
      (2 * Real.pi)⁻¹ * ∫ τ in (Icc (-H) H)ᶜ,
        ‖candidateEulerAngularApprox Y 0 ω τ‖ ^ 2 := by
  have he : (fun x => candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H x) =
      𝓕⁻ ((Icc (-(H / (2 * Real.pi))) (H / (2 * Real.pi))).indicator
        (fun ξ => candidateEulerAngularApprox Y 0 ω (2 * Real.pi * ξ))) := by
    funext x
    rw [candidate_bandInverse_eq_fourierInv]
    have hg : (fun ξ => (Icc (-H) H).indicator
        (candidateEulerAngularApprox Y 0 ω) (2 * Real.pi * ξ)) =
        (Icc (-(H / (2 * Real.pi))) (H / (2 * Real.pi))).indicator
          (fun ξ => candidateEulerAngularApprox Y 0 ω (2 * Real.pi * ξ)) := by
      funext ξ
      by_cases hξ : ξ ∈ Icc (-(H / (2 * Real.pi))) (H / (2 * Real.pi))
      · simp [hξ, (scaled_band_mem H ξ).mp hξ]
      · simp [hξ, (scaled_band_mem H ξ).not.mp hξ]
    rw [hg]
  simp_rw [congrFun he]
  rw [candidate_finiteEuler_hard_cutoff_error_eq]
  exact candidate_angular_tail_integral (fun τ => ‖candidateEulerAngularApprox Y 0 ω τ‖ ^ 2) H

/-- The finite angular inverse is square integrable, despite a hard spectral
cutoff; this follows from the inverse Fourier isometry. -/
theorem candidate_memLp_two_finiteEuler_bandInverse (Y : ℕ) (ω : Omega) (H : ℝ) :
    MemLp (candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H) 2 := by
  let f := candidateEulerLogProcess Y ω
  let S := Icc (-(H / (2 * Real.pi))) (H / (2 * Real.pi))
  have hf := candidate_integrable_eulerLogProcess Y ω
  have hf₂ := candidate_memLp_two_eulerLogProcess Y ω
  have hc : Continuous (𝓕 f) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hf
  have hgi : Integrable (S.indicator (𝓕 f)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hc.integrableOn_Icc
  have hg₂ : MemLp (S.indicator (𝓕 f)) 2 :=
    (candidate_literal_fourier_memLp_two hf hf₂).indicator measurableSet_Icc
  have he : candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H =
      (𝓕⁻ (S.indicator (𝓕 f)) : ℝ → ℂ) := by
    funext x
    rw [candidate_bandInverse_eq_fourierInv]
    have hg : (fun ξ => (Icc (-H) H).indicator
        (candidateEulerAngularApprox Y 0 ω) (2 * Real.pi * ξ)) = S.indicator (𝓕 f) := by
      funext ξ
      have hF := candidate_eulerLogProcess_fourier_eq Y ω (2 * Real.pi * ξ)
      have hF' : (𝓕 f) ξ = candidateEulerAngularApprox Y 0 ω (2 * Real.pi * ξ) := by
        simpa only [mul_div_cancel_left₀ ξ (by positivity : 2 * Real.pi ≠ 0)] using hF
      by_cases hξ : ξ ∈ S
      · have hξ' := (scaled_band_mem H ξ).mp hξ
        simp [hξ, hξ', hF']
      · have hξ' := (scaled_band_mem H ξ).not.mp hξ
        simp [hξ, hξ']
    rw [hg]
  rw [he]
  exact (memLp_congr_ae (candidate_literal_fourierInv_eq_L2_ae hgi hg₂)).mpr
    (Lp.memLp (𝓕⁻ hg₂.toLp))

/-- Every literal finite Euler cutoff error has an integrable square. -/
theorem candidate_integrable_finiteEuler_cutoff_error_sq (Y : ℕ) (ω : Omega) (H : ℝ) :
    Integrable (fun x =>
      ‖candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H x -
        candidateEulerLogProcess Y ω x‖ ^ 2) := by
  change Integrable (fun x =>
    ‖(candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H -
      candidateEulerLogProcess Y ω) x‖ ^ 2)
  exact ((candidate_memLp_two_finiteEuler_bandInverse Y ω H).sub
    (candidate_memLp_two_eulerLogProcess Y ω)).integrable_norm_pow (by decide : 2 ≠ 0)

/-- The finite-band inverse is jointly measurable in the signs and time. -/
theorem candidate_measurable_finiteEuler_bandInverse (Y : ℕ) (H : ℝ) :
    Measurable (fun z : Omega × ℝ =>
      candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 z.1) H z.2) := by
  have hA : Measurable (fun z : (Omega × ℝ) × ℝ =>
      candidateEulerAngularApprox Y 0 z.1.1 z.2) := by
    simp_rw [candidateEulerAngularApprox_eq_sum]
    apply Finset.measurable_sum
    intro n hn
    have hg : Measurable (fun z : (Omega × ℝ) × ℝ => gSquarefree z.1.1 n) :=
      (measurable_gSquarefree n).comp measurable_fst.fst
    unfold candidateEulerDirichletCoefficient
    fun_prop
  have hp : Measurable (fun z : (Omega × ℝ) × ℝ =>
      candidateCovariancePhase (z.1.2 * z.2)) := by
    unfold candidateCovariancePhase
    fun_prop
  have hi := StronglyMeasurable.integral_prod_right
    (f := fun (z : Omega × ℝ) τ =>
      candidateEulerAngularApprox Y 0 z.1 τ * candidateCovariancePhase (z.2 * τ))
    (ν := volume.restrict (Icc (-H) H)) (hA.mul hp).stronglyMeasurable
  change Measurable (fun z : Omega × ℝ => (2 * Real.pi : ℂ)⁻¹ *
    ∫ τ in Icc (-H) H,
      candidateEulerAngularApprox Y 0 z.1 τ * candidateCovariancePhase (z.2 * τ))
  exact hi.measurable.const_mul _

end Erdos.Problem1144
