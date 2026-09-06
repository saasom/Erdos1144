import Erdos.Problem1144.HarperCandidateSpectralCovariance

open MeasureTheory Set

namespace Erdos.Problem1144

local instance candidateSpectralCovarianceMatrixMeasurableSpace {ι : Type*} :
    MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

/-- The diagonal of an angular spectral covariance is the mass of its
density, including on nonsymmetric frequency sets. -/
theorem candidateSpectralCovariance_diag {ι : Type*}
    (μ : Measure ℝ) (u : ι → ℝ) {w : ℝ → ℝ} (hw : Integrable w μ) (i : ι) :
    candidateSpectralCovariance μ u w i i = ∫ τ, w τ ∂μ := by
  rw [candidateSpectralCovariance_apply μ u hw]
  apply integral_congr_ae
  filter_upwards [] with τ
  have h := Real.sin_sq_add_cos_sq (u i * τ)
  have h' : Real.cos (u i * τ) * Real.cos (u i * τ) +
      Real.sin (u i * τ) * Real.sin (u i * τ) = 1 := by nlinarith
  rw [h', mul_one]

/-- Splitting the frequency line gives an exact sum of covariance matrices. -/
theorem candidateSpectralCovariance_split {ι : Type*}
    (μ : Measure ℝ) (u : ι → ℝ) {w : ℝ → ℝ} (hw : Integrable w μ)
    {S : Set ℝ} (hS : MeasurableSet S) :
    candidateSpectralCovariance μ u w =
      candidateSpectralCovariance (μ.restrict S) u w +
      candidateSpectralCovariance (μ.restrict Sᶜ) u w := by
  rw [candidateSpectralCovariance_restrict μ u w hS,
    candidateSpectralCovariance_restrict μ u w hS.compl]
  ext i j
  rw [candidateSpectralCovariance_apply μ u hw,
    Matrix.add_apply,
    candidateSpectralCovariance_apply μ u (hw.indicator hS),
    candidateSpectralCovariance_apply μ u (hw.indicator hS.compl)]
  have hF : Integrable (fun τ => w τ *
      (Real.cos (u i * τ) * Real.cos (u j * τ) +
       Real.sin (u i * τ) * Real.sin (u j * τ))) μ := by
    apply hw.mul_bdd (by fun_prop) (c := 2)
    filter_upwards [] with τ
    calc
      _ ≤ ‖Real.cos (u i * τ) * Real.cos (u j * τ)‖ +
        ‖Real.sin (u i * τ) * Real.sin (u j * τ)‖ := norm_add_le _ _
      _ ≤ 1 * 1 + 1 * 1 := by
        simp only [norm_mul, Real.norm_eq_abs]
        gcongr <;> first | exact Real.abs_cos_le_one _ | exact Real.abs_sin_le_one _
      _ = 2 := by norm_num
  have heq := (integral_add_compl hS hF).symm
  rw [← integral_indicator hS, ← integral_indicator hS.compl] at heq
  convert heq using 1
  congr 1 <;> apply integral_congr_ae <;> filter_upwards [] with τ <;>
    by_cases hτ : τ ∈ S <;> simp [hτ]

/-- The retained squarefree covariance below an angular cutoff. -/
noncomputable def candidateSquarefreeLowCovariance {ι : Type*}
    (ω : Omega) (σ H : ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  candidateSpectralCovariance (volume.restrict {τ : ℝ | |τ| ≤ H}) u
    (candidateLogSpectralDensity (harperCandidateSquarefreeLogProcess ω) σ (1 / σ))

/-- The discarded squarefree covariance above the angular cutoff. -/
noncomputable def candidateSquarefreeHighCovariance {ι : Type*}
    (ω : Omega) (σ H : ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  candidateSpectralCovariance (volume.restrict {τ : ℝ | H < |τ|}) u
    (candidateLogSpectralDensity (harperCandidateSquarefreeLogProcess ω) σ (1 / σ))

/-- Spectral covariance entries depend measurably on a jointly measurable
random density, as needed for conditional Gaussian realization. -/
theorem measurable_candidateSpectralCovariance {Ω ι : Type*}
    [MeasurableSpace Ω] (μ : Measure ℝ) [SFinite μ]
    (u : ι → ℝ) {w : Ω → ℝ → ℝ}
    (hw : Measurable fun z : Ω × ℝ => w z.1 z.2) :
    Measurable (fun ω => candidateSpectralCovariance μ u (w ω)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hc : Measurable fun z : Ω × ℝ =>
      w z.1 z.2 * Real.cos (u i * z.2) * Real.cos (u j * z.2) := by
    exact (hw.mul (by fun_prop)).mul (by fun_prop)
  have hs : Measurable fun z : Ω × ℝ =>
      w z.1 z.2 * Real.sin (u i * z.2) * Real.sin (u j * z.2) := by
    exact (hw.mul (by fun_prop)).mul (by fun_prop)
  exact (StronglyMeasurable.integral_prod_right
    (f := fun ω τ => w ω τ * Real.cos (u i * τ) * Real.cos (u j * τ))
    hc.stronglyMeasurable (ν := μ)).measurable.add
      (StronglyMeasurable.integral_prod_right
        (f := fun ω τ => w ω τ * Real.sin (u i * τ) * Real.sin (u j * τ))
        hs.stronglyMeasurable (ν := μ)).measurable

/-- The actual low-frequency squarefree covariance is a measurable matrix. -/
theorem measurable_candidateSquarefreeLowCovariance {ι : Type*}
    (σ H : ℝ) (u : ι → ℝ) :
    Measurable (fun ω => candidateSquarefreeLowCovariance ω σ H u) := by
  apply measurable_candidateSpectralCovariance
    (volume.restrict {τ : ℝ | |τ| ≤ H}) u
  exact ((measurable_candidateSquarefreeAngularFourier σ).norm.pow_const 2).div_const
    (2 * Real.pi * (1 / σ))

/-- The actual high-frequency squarefree covariance is a measurable matrix. -/
theorem measurable_candidateSquarefreeHighCovariance {ι : Type*}
    (σ H : ℝ) (u : ι → ℝ) :
    Measurable (fun ω => candidateSquarefreeHighCovariance ω σ H u) := by
  apply measurable_candidateSpectralCovariance
    (volume.restrict {τ : ℝ | H < |τ|}) u
  exact ((measurable_candidateSquarefreeAngularFourier σ).norm.pow_const 2).div_const
    (2 * Real.pi * (1 / σ))

/-- The literal squarefree stationary covariance splits into low and high
frequencies. Both are PSD, and the high diagonal is exactly the already
bounded Fourier-tail variance. This holds under every fixed cylinder with no
analytic hypothesis. -/
theorem candidateCylinderLaw_ae_squarefree_covariance_split
    (s : Finset ℕ) (η : s → Bool) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ (m : ℕ) (u : Fin m → ℝ) (H : ℝ),
      candidateStationaryCovariance (harperCandidateSquarefreeLogProcess ω) u σ (1 / σ) =
        candidateSquarefreeLowCovariance ω σ H u +
        candidateSquarefreeHighCovariance ω σ H u ∧
      (candidateSquarefreeLowCovariance ω σ H u).PosSemidef ∧
      (candidateSquarefreeHighCovariance ω σ H u).PosSemidef ∧
      ∀ i, candidateSquarefreeHighCovariance ω σ H u i i =
        candidateSquarefreeSpectralTailVariance ω σ H := by
  filter_upwards [candidateCylinderLaw_ae_damped_L1_L2 s η hσ] with ω hω
  intro m u H
  let w := candidateLogSpectralDensity (harperCandidateSquarefreeLogProcess ω) σ (1 / σ)
  have hw : Integrable w := candidateLogSpectralDensity_integrable hω.2.1 hω.2.2
  have hn (τ : ℝ) : 0 ≤ w τ := by unfold w candidateLogSpectralDensity; positivity
  have hLo : MeasurableSet {τ : ℝ | |τ| ≤ H} :=
    measurableSet_le measurable_id.abs measurable_const
  have hHi : MeasurableSet {τ : ℝ | H < |τ|} :=
    measurableSet_lt measurable_const measurable_id.abs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [candidateStationaryCovariance_eq_spectral _ u σ (1 / σ) hω.2.1 hω.2.2,
      candidateSpectralCovariance_split volume u hw hLo]
    simp only [candidateSquarefreeLowCovariance, candidateSquarefreeHighCovariance,
      w, Set.compl_setOf, not_le]
  · exact candidateSpectralCovariance_posSemidef _ u hw.integrableOn (ae_of_all _ hn)
  · exact candidateSpectralCovariance_posSemidef _ u hw.integrableOn (ae_of_all _ hn)
  · intro i
    rw [candidateSquarefreeHighCovariance,
      candidateSpectralCovariance_diag _ u hw.integrableOn,
      candidateSquarefreeSpectralTailVariance_eq_density_integral ω hσ H]

end Erdos.Problem1144
