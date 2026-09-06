import Erdos.Problem1144.HarperCandidateSpectralTail
import Mathlib.Analysis.Fourier.LpSpace

open MeasureTheory FourierTransform
open scoped ComplexInnerProductSpace Topology

namespace Erdos.Problem1144

/-- The literal Fourier integral represents the `L²` Fourier transform.
Only integrability and square integrability of the input are needed. -/
theorem candidate_literal_fourier_eq_L2_ae {f : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : MemLp f 2) :
    (𝓕 f) =ᵐ[volume] ((𝓕 hf₂.toLp : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
  have hcont : Continuous (𝓕 f) := by
    change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume
      (innerₗ ℝ) f)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hf
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    ((Lp.memLp (𝓕 hf₂.toLp)).locallyIntegrable (by norm_num))
  intro g hg hc
  let φ : SchwartzMap ℝ ℂ :=
    (hc.comp_left (show Complex.ofRealCLM 0 = 0 by simp)).toSchwartzMap
      (show ContDiff ℝ (↑(⊤ : ℕ∞)) (Complex.ofRealCLM ∘ g) by fun_prop)
  have h := congrArg (fun d : TemperedDistribution ℝ ℂ => d φ)
    (Lp.fourier_toTemperedDistribution_eq hf₂.toLp)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h
  have hp := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := LinearMap.mul ℝ ℝ) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_mul φ.integrable hf
  change (∫ ξ, (∫ v, Real.fourierChar (-(v * ξ)) • φ v) • f ξ) =
    ∫ x, φ x • (∫ v, Real.fourierChar (-(x * v)) • f v) at hp
  have hp' : (∫ ξ, (𝓕 φ) ξ • f ξ) = ∫ x, φ x • (𝓕 f) x := by
    simpa only [SchwartzMap.fourier_coe, Real.fourier_real_eq, mul_comm] using hp
  have he : (∫ ξ, (𝓕 φ) ξ • (hf₂.toLp : ℝ → ℂ) ξ) =
      ∫ ξ, (𝓕 φ) ξ • f ξ := by
    apply integral_congr_ae
    filter_upwards [hf₂.coeFn_toLp] with x hx
    rw [hx]
  rw [he, hp'] at h
  simpa only [φ, Function.comp_apply,
    Complex.ofRealCLM_apply, Complex.real_smul] using h

/-- An `L¹ ∩ L²` function has a square-integrable literal Fourier transform. -/
theorem candidate_literal_fourier_memLp_two {f : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : MemLp f 2) : MemLp (𝓕 f) 2 :=
  (memLp_congr_ae (candidate_literal_fourier_eq_L2_ae hf hf₂)).mpr
    (Lp.memLp (𝓕 hf₂.toLp))

/-- The literal Fourier integral agrees with the Hilbert-space Fourier transform
whenever both functions lie in `L²` and the original function lies in `L¹`.
The identification is proved by testing against Schwartz functions; it is not
an additional Parseval hypothesis. -/
theorem candidate_literal_fourier_toL2_eq {f : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : MemLp f 2) (hF₂ : MemLp (𝓕 f) 2) :
    𝓕 hf₂.toLp = hF₂.toLp := by
  apply (LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot
      (E := ℝ) (F := ℂ) (μ := volume) (p := 2)))
  change Lp.toTemperedDistribution (𝓕 hf₂.toLp) =
    Lp.toTemperedDistribution hF₂.toLp
  rw [← Lp.fourier_toTemperedDistribution_eq]
  ext g
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
  calc
    (∫ x, (𝓕 g) x • (hf₂.toLp : ℝ → ℂ) x) = ∫ x, (𝓕 g) x • f x := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, g x • (𝓕 f) x := by
      have hp := VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := LinearMap.mul ℝ ℝ) (μ := volume) (ν := volume)
        Real.continuous_fourierChar continuous_mul g.integrable hf
      change (∫ ξ, (∫ v, Real.fourierChar (-(v * ξ)) • g v) • f ξ) =
        ∫ x, g x • (∫ v, Real.fourierChar (-(x * v)) • f v) at hp
      simpa only [SchwartzMap.fourier_coe, Real.fourier_real_eq, mul_comm] using hp
    _ = ∫ x, g x • (hF₂.toLp : ℝ → ℂ) x := by
      apply integral_congr_ae
      filter_upwards [hF₂.coeFn_toLp] with x hx
      rw [hx]

/-- Parseval for literal `L¹` Fourier integrals, including cross terms. -/
theorem candidate_literal_fourier_inner_integral_eq {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g)
    (hf₂ : MemLp f 2) (hg₂ : MemLp g 2) :
    (∫ ξ, ⟪(𝓕 f) ξ, (𝓕 g) ξ⟫) = ∫ t, ⟪f t, g t⟫ := by
  have hF₂ := candidate_literal_fourier_memLp_two hf hf₂
  have hG₂ := candidate_literal_fourier_memLp_two hg hg₂
  have h := Lp.inner_fourier_eq hf₂.toLp hg₂.toLp
  rw [candidate_literal_fourier_toL2_eq hf hf₂ hF₂,
    candidate_literal_fourier_toL2_eq hg hg₂ hG₂,
    L2.inner_def, L2.inner_def] at h
  calc
    _ = ∫ ξ, ⟪(hF₂.toLp : ℝ → ℂ) ξ, (hG₂.toLp : ℝ → ℂ) ξ⟫ := by
      apply integral_congr_ae
      filter_upwards [hF₂.coeFn_toLp, hG₂.coeFn_toLp] with x hx hy
      rw [hx, hy]
    _ = ∫ t, ⟪(hf₂.toLp : ℝ → ℂ) t, (hg₂.toLp : ℝ → ℂ) t⟫ := h
    _ = ∫ t, ⟪f t, g t⟫ := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp, hg₂.coeFn_toLp] with x hx hy
      rw [hx, hy]

/-- The literal Parseval norm identity has no spectral integrability premise. -/
theorem candidate_literal_fourier_norm_sq_integral_eq {f : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : MemLp f 2) :
    (∫ ξ, ‖(𝓕 f) ξ‖ ^ 2) = ∫ t, ‖f t‖ ^ 2 := by
  have h := candidate_literal_fourier_inner_integral_eq hf hf hf₂ hf₂
  simp only [inner_self_eq_norm_sq_to_K] at h
  change (∫ ξ, ((‖(𝓕 f) ξ‖ : ℝ) : ℂ) ^ 2) =
    ∫ t, ((‖f t‖ : ℝ) : ℂ) ^ 2 at h
  simp_rw [← Complex.ofReal_pow, integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

end Erdos.Problem1144
