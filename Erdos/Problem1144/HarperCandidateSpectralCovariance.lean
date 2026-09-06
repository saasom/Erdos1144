import Erdos.Problem1144.HarperCandidateSpectralCovarianceIntegrability
import Erdos.Problem1144.HarperCandidateCovariance

open MeasureTheory Set FourierTransform
open scoped BigOperators ComplexInnerProductSpace

namespace Erdos.Problem1144

/-- The real covariance matrix associated with an angular spectral density.
Both cosine and sine features are included, so this definition also applies
to nonsymmetric integration domains. -/
noncomputable def candidateSpectralCovariance {ι : Type*}
    (μ : Measure ℝ) (u : ι → ℝ) (w : ℝ → ℝ) : Matrix ι ι ℝ :=
  candidateWeightedGram μ (fun i τ => Real.cos (u i * τ)) w +
    candidateWeightedGram μ (fun i τ => Real.sin (u i * τ)) w

private theorem candidate_integrable_trig_product
    {μ : Measure ℝ} {w : ℝ → ℝ} (hw : Integrable w μ)
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf₁ : ∀ x, ‖f x‖ ≤ 1) (hg₁ : ∀ x, ‖g x‖ ≤ 1) :
    Integrable (fun x => w x * f x * g x) μ := by
  exact (hw.mul_bdd hf.aestronglyMeasurable (ae_of_all _ hf₁)).mul_bdd
    hg.aestronglyMeasurable (ae_of_all _ hg₁)

private theorem candidate_integrable_cos_product
    {μ : Measure ℝ} {w : ℝ → ℝ} (hw : Integrable w μ) (u v : ℝ) :
    Integrable (fun τ => w τ * Real.cos (u * τ) * Real.cos (v * τ)) μ :=
  candidate_integrable_trig_product hw _ _ (by fun_prop) (by fun_prop)
    (fun _ => Real.abs_cos_le_one _) (fun _ => Real.abs_cos_le_one _)

private theorem candidate_integrable_sin_product
    {μ : Measure ℝ} {w : ℝ → ℝ} (hw : Integrable w μ) (u v : ℝ) :
    Integrable (fun τ => w τ * Real.sin (u * τ) * Real.sin (v * τ)) μ :=
  candidate_integrable_trig_product hw _ _ (by fun_prop) (by fun_prop)
    (fun _ => Real.abs_sin_le_one _) (fun _ => Real.abs_sin_le_one _)

/-- Nonnegative angular density gives an actual positive-semidefinite matrix. -/
theorem candidateSpectralCovariance_posSemidef {ι : Type*} [Finite ι]
    (μ : Measure ℝ) (u : ι → ℝ) {w : ℝ → ℝ}
    (hw : Integrable w μ) (hn : ∀ᵐ τ ∂μ, 0 ≤ w τ) :
    (candidateSpectralCovariance μ u w).PosSemidef := by
  apply Matrix.PosSemidef.add
  · apply candidateWeightedGram_posSemidef
    · exact fun i j => candidate_integrable_cos_product hw (u i) (u j)
    · exact hn.mono fun _ h => Or.inl h
  · apply candidateWeightedGram_posSemidef
    · exact fun i j => candidate_integrable_sin_product hw (u i) (u j)
    · exact hn.mono fun _ h => Or.inl h

/-- Pointwise spectral comparison yields matrix comparison for the same grid. -/
theorem candidateSpectralCovariance_sub_posSemidef {ι : Type*} [Finite ι]
    (μ : Measure ℝ) (u : ι → ℝ) {w₀ w₁ : ℝ → ℝ}
    (h₀ : Integrable w₀ μ) (h₁ : Integrable w₁ μ)
    (hw : ∀ᵐ τ ∂μ, w₀ τ ≤ w₁ τ) :
    (candidateSpectralCovariance μ u w₁ - candidateSpectralCovariance μ u w₀).PosSemidef := by
  have hc := candidateWeightedGram_sub_posSemidef μ
    (fun i τ => Real.cos (u i * τ)) w₀ w₁
    (fun i j => candidate_integrable_cos_product h₀ (u i) (u j))
    (fun i j => candidate_integrable_cos_product h₁ (u i) (u j))
    (hw.mono fun _ h => Or.inl h)
  have hs := candidateWeightedGram_sub_posSemidef μ
    (fun i τ => Real.sin (u i * τ)) w₀ w₁
    (fun i j => candidate_integrable_sin_product h₀ (u i) (u j))
    (fun i j => candidate_integrable_sin_product h₁ (u i) (u j))
    (hw.mono fun _ h => Or.inl h)
  convert hc.add hs using 1
  ext i j
  simp only [candidateSpectralCovariance, Matrix.sub_apply, Matrix.add_apply]
  ring

/-- Restricting frequencies inserts the indicator into the spectral density. -/
theorem candidateSpectralCovariance_restrict {ι : Type*}
    (μ : Measure ℝ) (u : ι → ℝ) (w : ℝ → ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    candidateSpectralCovariance (μ.restrict S) u w =
      candidateSpectralCovariance μ u (S.indicator w) := by
  unfold candidateSpectralCovariance
  rw [candidateWeightedGram_restrict _ _ _ hS, candidateWeightedGram_restrict _ _ _ hS]

/-- A scalar factor in the density scales the entire covariance matrix. -/
theorem candidateSpectralCovariance_const_mul {ι : Type*}
    (μ : Measure ℝ) (u : ι → ℝ) (w : ℝ → ℝ) (c : ℝ) :
    candidateSpectralCovariance μ u (fun τ => c * w τ) =
      c • candidateSpectralCovariance μ u w := by
  simp only [candidateSpectralCovariance, candidateWeightedGram_const_mul, smul_add]

private theorem candidate_integrable_inner_memLp {f g : ℝ → ℂ}
    (hf : MemLp f 2) (hg : MemLp g 2) : Integrable fun x => ⟪f x, g x⟫ := by
  apply (L2.integrable_inner hf.toLp hg.toLp).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

private theorem candidate_inner_phases_re (α β : ℝ) (z : ℂ) :
    (⟪Real.fourierChar α • z, Real.fourierChar β • z⟫ : ℂ).re =
      ‖z‖ ^ 2 * (Real.cos (2 * Real.pi * α) * Real.cos (2 * Real.pi * β) +
        Real.sin (2 * Real.pi * α) * Real.sin (2 * Real.pi * β)) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Circle.smul_def, Real.fourierChar_apply, Complex.mul_re,
    Complex.mul_im, Complex.exp_re, Complex.exp_im]
  ring

/-- Parseval identifies the covariance of real translates with the literal
Fourier density in cycles per unit time. -/
theorem candidate_real_translate_covariance_fourier {f : ℝ → ℝ}
    (hf : Integrable f) (hf₂ : MemLp f 2) (u v : ℝ) :
    (∫ x, f (u - x) * f (v - x)) =
      ∫ ξ, ‖𝓕 (fun t => (f t : ℂ)) ξ‖ ^ 2 *
        (Real.cos (2 * Real.pi * (u * ξ)) * Real.cos (2 * Real.pi * (v * ξ)) +
         Real.sin (2 * Real.pi * (u * ξ)) * Real.sin (2 * Real.pi * (v * ξ))) := by
  let F : ℝ → ℂ := fun t => (f t : ℂ)
  have hu₂ : MemLp (fun x => F (x + u)) 2 :=
    hf₂.ofReal.comp_measurePreserving (measurePreserving_add_right volume u)
  have hv₂ : MemLp (fun x => F (x + v)) 2 :=
    hf₂.ofReal.comp_measurePreserving (measurePreserving_add_right volume v)
  have hu₁ : Integrable (fun x => F (x + u)) := hf.ofReal.comp_add_right u
  have hv₁ : Integrable (fun x => F (x + v)) := hf.ofReal.comp_add_right v
  have hP := candidate_literal_fourier_inner_integral_eq hu₁ hv₁ hu₂ hv₂
  have hi := candidate_integrable_inner_memLp
    (candidate_literal_fourier_memLp_two hu₁ hu₂)
    (candidate_literal_fourier_memLp_two hv₁ hv₂)
  have hshift (a ξ : ℝ) : 𝓕 (fun x => F (x + a)) ξ =
      Real.fourierChar (a * ξ) • 𝓕 F ξ := by
    have h := congrFun
      (Fourier.fourierIntegral_comp_add_right Real.fourierChar volume F a) ξ
    simpa only [Real.fourier_real_eq, Fourier.fourierIntegral_def,
      Function.comp_apply] using h
  have hre : (∫ ξ, ‖𝓕 F ξ‖ ^ 2 *
      (Real.cos (2 * Real.pi * (u * ξ)) * Real.cos (2 * Real.pi * (v * ξ)) +
       Real.sin (2 * Real.pi * (u * ξ)) * Real.sin (2 * Real.pi * (v * ξ)))) =
      ∫ x, f (x + u) * f (x + v) := by
    have hr := congrArg Complex.re hP
    have hir : (∫ ξ, (⟪𝓕 (fun x => F (x + u)) ξ,
        𝓕 (fun x => F (x + v)) ξ⟫ : ℂ).re) =
        (∫ ξ, ⟪𝓕 (fun x => F (x + u)) ξ, 𝓕 (fun x => F (x + v)) ξ⟫).re :=
      integral_re hi
    rw [← hir] at hr
    simp_rw [hshift, candidate_inner_phases_re] at hr
    have hc : (∫ x, ⟪F (x + u), F (x + v)⟫) =
        ((∫ x, f (x + u) * f (x + v) : ℝ) : ℂ) := by
      simp only [F, RCLike.inner_apply', Complex.conj_ofReal,
        ← Complex.ofReal_mul, integral_complex_ofReal]
    rw [hc, Complex.ofReal_re] at hr
    exact hr
  rw [hre]
  convert (integral_neg_eq_self (fun x => f (x + u) * f (x + v)) volume) using 1
  congr 1
  funext x
  simp only [sub_eq_add_neg, add_comm]

/-- Square integrability of the literal Fourier transform makes the candidate
angular density integrable, with its exact `2πL` normalization. -/
theorem candidateLogSpectralDensity_integrable {a : ℝ → ℝ} {σ L : ℝ}
    (ha : Integrable (fun t => Real.exp (-σ * t) * a t))
    (ha₂ : MemLp (fun t => Real.exp (-σ * t) * a t) 2) :
    Integrable (candidateLogSpectralDensity a σ L) := by
  have hF := (candidate_literal_fourier_memLp_two ha.ofReal ha₂.ofReal).integrable_norm_pow
    (by decide : 2 ≠ 0)
  have hdiv := (hF.comp_div (by positivity : 2 * Real.pi ≠ 0)).div_const
    (2 * Real.pi * L)
  simpa only [candidateLogSpectralDensity, Real.fourier_real_eq,
    Fourier.fourierIntegral_def] using hdiv

/-- Evaluating the spectral matrix combines the cosine and sine Gram terms. -/
theorem candidateSpectralCovariance_apply {ι : Type*}
    (μ : Measure ℝ) (u : ι → ℝ) {w : ℝ → ℝ} (hw : Integrable w μ) (i j : ι) :
    candidateSpectralCovariance μ u w i j =
      ∫ τ, w τ * (Real.cos (u i * τ) * Real.cos (u j * τ) +
        Real.sin (u i * τ) * Real.sin (u j * τ)) ∂μ := by
  simp only [candidateSpectralCovariance, candidateWeightedGram, Matrix.add_apply]
  rw [← integral_add (candidate_integrable_cos_product hw (u i) (u j))
    (candidate_integrable_sin_product hw (u i) (u j))]
  apply integral_congr_ae
  filter_upwards [] with τ
  ring

private theorem candidate_angular_integral_normalization (g : ℝ → ℝ) (L : ℝ) :
    (∫ τ, g (τ / (2 * Real.pi)) / (2 * Real.pi * L)) =
      (1 / L) * ∫ ξ, g ξ := by
  rw [integral_div, Measure.integral_comp_div,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  simp only [smul_eq_mul]
  by_cases hL : L = 0
  · simp [hL]
  · field_simp

/-- Exact identification of the candidate's stationary time covariance with
its literal angular Fourier covariance. The normalization is `2πL`. -/
theorem candidateStationaryCovariance_eq_spectral {ι : Type*}
    (a : ℝ → ℝ) (u : ι → ℝ) (σ L : ℝ)
    (ha : Integrable (fun t => Real.exp (-σ * t) * a t))
    (ha₂ : MemLp (fun t => Real.exp (-σ * t) * a t) 2) :
    candidateStationaryCovariance a u σ L =
      candidateSpectralCovariance volume u (candidateLogSpectralDensity a σ L) := by
  ext i j
  rw [candidateSpectralCovariance_apply volume u
    (candidateLogSpectralDensity_integrable ha ha₂)]
  let f : ℝ → ℝ := fun t => Real.exp (-σ * t) * a t
  let g : ℝ → ℝ := fun ξ => ‖𝓕 (fun t => (f t : ℂ)) ξ‖ ^ 2 *
    (Real.cos (2 * Real.pi * (u i * ξ)) * Real.cos (2 * Real.pi * (u j * ξ)) +
     Real.sin (2 * Real.pi * (u i * ξ)) * Real.sin (2 * Real.pi * (u j * ξ)))
  have ht : candidateStationaryCovariance a u σ L i j =
      (1 / L) * ∫ x, f (u i - x) * f (u j - x) := by
    simp only [candidateStationaryCovariance, candidateWeightedGram]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [f]
    ring
  rw [ht, candidate_real_translate_covariance_fourier ha ha₂]
  change (1 / L) * ∫ ξ, g ξ = _
  rw [← candidate_angular_integral_normalization g L]
  apply integral_congr_ae
  filter_upwards [] with τ
  have hp : 2 * Real.pi ≠ 0 := by positivity
  have hi : 2 * Real.pi * (u i * (τ / (2 * Real.pi))) = u i * τ := by field_simp
  have hj : 2 * Real.pi * (u j * (τ / (2 * Real.pi))) = u j * τ := by field_simp
  simp only [g, hi, hj, candidateLogSpectralDensity, Real.fourier_real_eq,
    Fourier.fourierIntegral_def, f]
  ring

/-- Every fixed cylinder almost surely admits the exact time/Fourier
covariance identity for both actual processes and every finite grid. -/
theorem candidateCylinderLaw_ae_stationaryCovariance_eq_spectral
    (s : Finset ℕ) (η : s → Bool) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ (m : ℕ) (u : Fin m → ℝ) (L : ℝ),
      candidateStationaryCovariance (harperCandidateLogProcess ω) u σ L =
        candidateSpectralCovariance volume u
          (candidateLogSpectralDensity (harperCandidateLogProcess ω) σ L) ∧
      candidateStationaryCovariance (harperCandidateSquarefreeLogProcess ω) u σ L =
        candidateSpectralCovariance volume u
          (candidateLogSpectralDensity (harperCandidateSquarefreeLogProcess ω) σ L) := by
  filter_upwards [candidateCylinderLaw_ae_damped_L1_L2 s η hσ] with ω hω
  intro m u L
  exact ⟨candidateStationaryCovariance_eq_spectral _ u σ L hω.1.1 hω.1.2,
    candidateStationaryCovariance_eq_spectral _ u σ L hω.2.1 hω.2.2⟩

/-- The actual stationary complete covariance dominates the retained
squarefree spectral window. All Fourier and time-domain regularity here is
derived from the arithmetic moments. -/
theorem exists_candidate_complete_stationaryCovariance_window_domination :
    ∃ C : ℝ, 0 < C ∧ ∀ κ : ℝ, 0 < κ →
      ∀ᶠ T : ℝ in Filter.atTop, ∀ (s : Finset ℕ) (η : s → Bool),
        ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ (m : ℕ) (u : Fin m → ℝ),
          (candidateStationaryCovariance (harperCandidateLogProcess ω) u
              (κ * Real.log (Real.log T) / T) T -
            (1 / ((κ * Real.log (Real.log T)) *
              (C * Real.log (2 * Real.log T ^ 2 + 4) ^ 7) ^ 2)) •
              candidateSpectralCovariance
                (volume.restrict {τ : ℝ | |τ| ≤ Real.log T ^ 2}) u
                (candidateLogSpectralDensity (harperCandidateSquarefreeLogProcess ω)
                  (κ * Real.log (Real.log T) / T)
                  (T / (κ * Real.log (Real.log T))))).PosSemidef := by
  obtain ⟨C, hC, hdom⟩ := exists_candidate_complete_spectralDensity_window_domination
  refine ⟨C, hC, fun κ hκ => ?_⟩
  filter_upwards [hdom κ hκ, Filter.eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop 1] with T hTdom hT hlog
  have hW : 0 < κ * Real.log (Real.log T) := mul_pos hκ (Real.log_pos hlog)
  have hσ : 0 < κ * Real.log (Real.log T) / T := div_pos hW hT
  intro s η
  filter_upwards [hTdom s η, candidateCylinderLaw_ae_damped_L1_L2 s η hσ]
    with ω hω hLp
  intro m u
  let σ := κ * Real.log (Real.log T) / T
  let V := T / (κ * Real.log (Real.log T))
  let c := 1 / ((κ * Real.log (Real.log T)) *
    (C * Real.log (2 * Real.log T ^ 2 + 4) ^ 7) ^ 2)
  let S : Set ℝ := {τ | |τ| ≤ Real.log T ^ 2}
  let wa := candidateLogSpectralDensity (harperCandidateLogProcess ω) σ T
  let wm := candidateLogSpectralDensity (harperCandidateSquarefreeLogProcess ω) σ V
  have hS : MeasurableSet S := measurableSet_le measurable_id.abs measurable_const
  have hai : Integrable wa := candidateLogSpectralDensity_integrable hLp.1.1 hLp.1.2
  have hmi : Integrable wm := candidateLogSpectralDensity_integrable hLp.2.1 hLp.2.2
  have hwi : Integrable (S.indicator fun τ => c * wm τ) :=
    (integrable_indicator_iff hS).mpr (hmi.const_mul c).integrableOn
  have hw : ∀ᵐ τ ∂volume, (S.indicator fun τ => c * wm τ) τ ≤ wa τ := by
    filter_upwards [] with τ
    by_cases hτ : τ ∈ S
    · rw [indicator_of_mem hτ]
      exact hω τ hτ
    · rw [indicator_of_notMem hτ]
      unfold wa candidateLogSpectralDensity
      positivity
  have hpsd := candidateSpectralCovariance_sub_posSemidef volume u hwi hai hw
  rw [← candidateSpectralCovariance_restrict volume u _ hS,
    candidateSpectralCovariance_const_mul] at hpsd
  rw [candidateStationaryCovariance_eq_spectral _ u _ _ hLp.1.1 hLp.1.2]
  exact hpsd

end Erdos.Problem1144
