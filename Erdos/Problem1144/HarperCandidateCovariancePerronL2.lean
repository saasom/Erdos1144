import Erdos.Problem1144.HarperCandidateCovariancePerronKernel
import Erdos.Problem1144.HarperCandidateSpectralParseval

open MeasureTheory FourierTransform
open scoped ComplexInnerProductSpace Topology

namespace Erdos.Problem1144

/-- The literal inverse Fourier integral represents the inverse Fourier
isometry on `L²`, even when the resulting time function is not in `L¹`. -/
theorem candidate_literal_fourierInv_eq_L2_ae {f : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : MemLp f 2) :
    (𝓕⁻ f) =ᵐ[volume] ((𝓕⁻ hf₂.toLp : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
  have hcont : Continuous (𝓕⁻ f) := by
    have hc : Continuous (𝓕 f) := by
      change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume
        (innerₗ ℝ) f)
      exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        continuous_inner hf
    simpa only [Function.comp_def, ← Real.fourierInv_eq_fourier_neg] using hc.comp continuous_neg
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp (𝓕⁻ hf₂.toLp)).locallyIntegrable (by norm_num))
  intro g hg hc
  let φ : SchwartzMap ℝ ℂ :=
    (hc.comp_left (show Complex.ofRealCLM 0 = 0 by simp)).toSchwartzMap
      (show ContDiff ℝ (↑(⊤ : ℕ∞)) (Complex.ofRealCLM ∘ g) by fun_prop)
  have h := congrArg (fun d : TemperedDistribution ℝ ℂ => d φ)
    (Lp.fourierInv_toTemperedDistribution_eq hf₂.toLp)
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply] at h
  have hp := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := -LinearMap.mul ℝ ℝ) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_mul.neg φ.integrable hf
  change (∫ ξ, (∫ v, Real.fourierChar (-(-(v * ξ))) • φ v) • f ξ) =
    ∫ x, φ x • (∫ v, Real.fourierChar (-(-(x * v))) • f v) at hp
  have hp' : (∫ ξ, (𝓕⁻ φ) ξ • f ξ) = ∫ x, φ x • (𝓕⁻ f) x := by
    simpa only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq,
      neg_mul, mul_neg, neg_neg, mul_comm] using hp
  have he : (∫ ξ, (𝓕⁻ φ) ξ • (hf₂.toLp : ℝ → ℂ) ξ) =
      ∫ ξ, (𝓕⁻ φ) ξ • f ξ := by
    apply integral_congr_ae
    filter_upwards [hf₂.coeFn_toLp] with x hx
    rw [hx]
  rw [he, hp'] at h
  simpa only [φ, Function.comp_apply,
    Complex.ofRealCLM_apply, Complex.real_smul] using h

/-- Squared integral norm of an actual `L²` function equals the Hilbert norm. -/
theorem candidate_integral_norm_sq_eq_toLp_norm_sq {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫ x, ‖f x‖ ^ 2) = ‖hf.toLp‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow, ← integral_complex_ofReal]
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) hf.toLp
  rw [L2.inner_def] at h
  calc
    _ = ∫ x, ⟪(hf.toLp : ℝ → ℂ) x, (hf.toLp : ℝ → ℂ) x⟫ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      simp [hx, inner_self_eq_norm_sq_to_K]
    _ = _ := h

/-- Parseval's exact error identity for a literal inverse transform and an
arbitrary `L¹ ∩ L²` time function. This includes hard frequency cutoffs. -/
theorem candidate_inverse_fourier_error_integral_eq {f g : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : MemLp f 2) (hg : Integrable g) (hg₂ : MemLp g 2) :
    (∫ x, ‖(𝓕⁻ g) x - f x‖ ^ 2) = ∫ ξ, ‖g ξ - (𝓕 f) ξ‖ ^ 2 := by
  let U : Lp ℂ 2 (volume : Measure ℝ) := 𝓕⁻ hg₂.toLp - hf₂.toLp
  let V : Lp ℂ 2 (volume : Measure ℝ) := hg₂.toLp - 𝓕 hf₂.toLp
  have hU : (fun x => (𝓕⁻ g) x - f x) =ᵐ[volume] (U : ℝ → ℂ) := by
    filter_upwards [candidate_literal_fourierInv_eq_L2_ae hg hg₂,
      hf₂.coeFn_toLp, Lp.coeFn_sub (𝓕⁻ hg₂.toLp) hf₂.toLp] with x hx hy hz
    exact (congrArg₂ (· - ·) hx hy.symm).trans hz.symm
  have hV : (fun x => g x - (𝓕 f) x) =ᵐ[volume] (V : ℝ → ℂ) := by
    filter_upwards [hg₂.coeFn_toLp, candidate_literal_fourier_eq_L2_ae hf hf₂,
      Lp.coeFn_sub hg₂.toLp (𝓕 hf₂.toLp)] with x hx hy hz
    exact (congrArg₂ (· - ·) hx.symm hy).trans hz.symm
  have hnorm (W : Lp ℂ 2 (volume : Measure ℝ)) :
      (∫ x, ‖W x‖ ^ 2) = ‖W‖ ^ 2 := by
    have h := candidate_integral_norm_sq_eq_toLp_norm_sq (Lp.memLp W)
    simpa only [Lp.toLp_coeFn] using h
  calc
    _ = ∫ x, ‖U x‖ ^ 2 := integral_congr_ae (hU.fun_comp fun z => ‖z‖ ^ 2)
    _ = ‖U‖ ^ 2 := hnorm U
    _ = ‖V‖ ^ 2 := by
      have he : 𝓕 U = V := by
        change (Lp.fourierTransformₗᵢ ℝ ℂ) (𝓕⁻ hg₂.toLp - hf₂.toLp) = V
        rw [map_sub]
        change 𝓕 (𝓕⁻ hg₂.toLp) - 𝓕 hf₂.toLp = V
        rw [fourier_fourierInv_eq]
      rw [← he, Lp.norm_fourier_eq]
    _ = ∫ x, ‖V x‖ ^ 2 := (hnorm V).symm
    _ = _ := integral_congr_ae (hV.symm.fun_comp fun z => ‖z‖ ^ 2)

/-- Hard frequency truncation has exactly the omitted Fourier energy as its
mean-square time error; no pointwise Fourier inversion is assumed. -/
theorem candidate_hard_fourier_cutoff_error_eq {f : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : MemLp f 2) (H : ℝ) :
    (∫ x, ‖(𝓕⁻ ((Set.Icc (-H) H).indicator (𝓕 f))) x - f x‖ ^ 2) =
      ∫ ξ in (Set.Icc (-H) H)ᶜ, ‖(𝓕 f) ξ‖ ^ 2 := by
  have hF : Continuous (𝓕 f) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume
      (innerₗ ℝ) f)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hf
  have hi : Integrable ((Set.Icc (-H) H).indicator (𝓕 f)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
    (hF.continuousOn.integrableOn_compact isCompact_Icc)
  have h₂ : MemLp ((Set.Icc (-H) H).indicator (𝓕 f)) 2 :=
    (candidate_literal_fourier_memLp_two hf hf₂).indicator measurableSet_Icc
  rw [candidate_inverse_fourier_error_integral_eq hf hf₂ hi h₂,
    ← integral_indicator measurableSet_Icc.compl]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    by_cases hξ : ξ ∈ Set.Icc (-H) H
    · simp [hξ]
    · simp [hξ]

end Erdos.Problem1144
