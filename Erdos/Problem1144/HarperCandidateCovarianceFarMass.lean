import Erdos.Problem1144.HarperCandidateCovarianceRowPairing
import Erdos.Problem1144.HarperCandidateCovarianceHalfDensityMoments
import Erdos.Problem1144.HarperCandidateSpectralTail

open MeasureTheory Set

namespace Erdos.Problem1144
noncomputable section

/-- Deterministic retained annulus with a genuinely large frequency gap. -/
def candidateCovarianceFarAnnulus (h M d : ℝ) : Set (ℝ × ℝ) :=
  {z | h ≤ |z.1| ∧ |z.1| ≤ M ∧ h ≤ |z.2| ∧ |z.2| ≤ M ∧ d ≤ |z.1 - z.2|}

/-- One random far mass shared by every Fourier covariance entry and every
measurable subregion of the retained far annulus. -/
def candidateEulerBandFarMass (Y : ℕ) (T B h M d : ℝ) (ω : Omega) : ℝ :=
  ∫ z in candidateCovarianceFarAnnulus h M d,
    candidateEulerBandRowWeight Y ω T B z ∂volume.prod volume

theorem candidate_measurableSet_farAnnulus (h M d : ℝ) :
    MeasurableSet (candidateCovarianceFarAnnulus h M d) := by
  unfold candidateCovarianceFarAnnulus
  exact (measurableSet_le measurable_const measurable_fst.abs).inter
    ((measurableSet_le measurable_fst.abs measurable_const).inter
      ((measurableSet_le measurable_const measurable_snd.abs).inter
        ((measurableSet_le measurable_snd.abs measurable_const).inter
          (measurableSet_le measurable_const (measurable_fst.sub measurable_snd).abs))))

private theorem far_subset_box (h M d : ℝ) : candidateCovarianceFarAnnulus h M d ⊆
    Icc (-M) M ×ˢ Icc (-M) M := by
  intro z hz
  exact ⟨abs_le.mp hz.2.1, abs_le.mp hz.2.2.2.1⟩

private theorem finite_far_measure (h M d : ℝ) :
    IsFiniteMeasure ((volume.prod volume).restrict (candidateCovarianceFarAnnulus h M d)) :=
  isFiniteMeasure_restrict.mpr ((measure_mono (far_subset_box h M d)).trans_lt
    ((isCompact_Icc.prod isCompact_Icc).measure_lt_top (μ := volume.prod volume))).ne

/-- The exact Cauchy denominator costs at most two for each angular
amplitude, keeping its literal square-root Euler density. -/
theorem candidate_criticalEuler_norm_le_two_sqrt_density (Y : ℕ) (ω : Omega) (t : ℝ) :
    ‖candidateEulerAngularApprox Y 0 ω t‖ ≤ 2 * Real.sqrt (Problem520.harperEulerDensity Y ω t) := by
  have hd := Problem520.harperEulerDensity_nonneg Y ω t
  have he := candidate_eulerBandSquaredWeight_eq_norm_sq Y ω t
  have hs : ‖candidateEulerAngularApprox Y 0 ω t‖ ^ 2 ≤ 4 * Problem520.harperEulerDensity Y ω t := by
    rw [← he, candidateEulerBandSquaredWeight]
    apply (div_le_iff₀ (by positivity : 0 < (1 / 2 : ℝ) ^ 2 + t ^ 2)).mpr
    nlinarith [mul_nonneg hd (sq_nonneg t)]
  nlinarith [Real.sq_sqrt hd, Real.sqrt_nonneg (Problem520.harperEulerDensity Y ω t),
    norm_nonneg (candidateEulerAngularApprox Y 0 ω t)]

/-- The literal paired row weight retains the true half-density product
when the two Cauchy denominators are removed. -/
theorem candidate_eulerBandRowWeight_le_halfDensityPair (Y : ℕ) (ω : Omega)
    (T B : ℝ) (z : ℝ × ℝ) :
    candidateEulerBandRowWeight Y ω T B z ≤
      4 * (Real.sqrt (Problem520.harperEulerDensity Y ω z.1) *
        Real.sqrt (Problem520.harperEulerDensity Y ω z.2)) *
          ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖ := by
  unfold candidateEulerBandRowWeight
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (mul_le_mul (candidate_criticalEuler_norm_le_two_sqrt_density Y ω z.1)
    (candidate_criticalEuler_norm_le_two_sqrt_density Y ω z.2) (norm_nonneg _)
    (by positivity)).trans_eq (by ring)

private theorem rowWeight_nonneg (Y : ℕ) (ω : Omega) (T B : ℝ) (z : ℝ × ℝ) :
    0 ≤ candidateEulerBandRowWeight Y ω T B z := by unfold candidateEulerBandRowWeight; positivity

private theorem rowWeight_uniform (Y : ℕ) {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B)
    (ω : Omega) (z : ℝ × ℝ) :
    candidateEulerBandRowWeight Y ω T B z ≤
      4 * Problem520.harperEulerDensityUniformBound Y * Real.log (B / T) := by
  have hpair : Real.sqrt (Problem520.harperEulerDensity Y ω z.1) *
      Real.sqrt (Problem520.harperEulerDensity Y ω z.2) ≤
        Problem520.harperEulerDensityUniformBound Y := by
    have hh := mul_le_mul
      (Real.sqrt_le_sqrt (Problem520.harperEulerDensity_le_uniformBound Y ω z.1))
      (Real.sqrt_le_sqrt (Problem520.harperEulerDensity_le_uniformBound Y ω z.2))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    simpa only [← pow_two, Real.sq_sqrt (Problem520.harperEulerDensityUniformBound_nonneg Y)] using hh
  exact (candidate_eulerBandRowWeight_le_halfDensityPair Y ω T B z).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hpair (by norm_num))
      (candidate_whiteKernel_norm_le_log hT hTB _) (norm_nonneg _)
      (mul_nonneg (by norm_num) (Problem520.harperEulerDensityUniformBound_nonneg Y)))

/-- The actual row weight is jointly measurable in its two frequencies
and the signs, so no extra Fubini hypothesis is needed. -/
theorem candidate_measurable_eulerBandRowWeight_joint (Y : ℕ) (T B : ℝ) :
    Measurable (fun z : (ℝ × ℝ) × Omega => candidateEulerBandRowWeight Y z.2 T B z.1) := by
  have hA := measurable_candidateEulerAngularApprox Y 0
  have hK := candidate_measurable_whiteKernel T B
  unfold candidateEulerBandRowWeight
  fun_prop

/-- The deterministic finite Euler bound proves joint integrability on
the full far annulus; it is used only for regularity, not for the moment. -/
theorem candidate_integrable_farRowWeight_joint (Y : ℕ) {T B : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (h M d : ℝ) :
    Integrable (fun z : (ℝ × ℝ) × Omega => candidateEulerBandRowWeight Y z.2 T B z.1)
      (((volume.prod volume).restrict (candidateCovarianceFarAnnulus h M d)).prod mu) := by
  letI := finite_far_measure h M d
  apply (integrable_const (4 * Problem520.harperEulerDensityUniformBound Y * Real.log (B / T))).mono'
    (candidate_measurable_eulerBandRowWeight_joint Y T B).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (rowWeight_nonneg Y z.2 T B z.1)]
    exact rowWeight_uniform Y hT hTB z.2 z.1

private theorem rowWeight_integrable_fixed (Y : ℕ) (ω : Omega) {T B : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (h M d : ℝ) :
    IntegrableOn (candidateEulerBandRowWeight Y ω T B) (candidateCovarianceFarAnnulus h M d)
      (volume.prod volume) := by
  letI := finite_far_measure h M d
  apply (integrable_const (4 * Problem520.harperEulerDensityUniformBound Y * Real.log (B / T))).mono'
    (((candidate_measurable_eulerBandRowWeight_joint Y T B).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  exact ae_of_all _ fun z => by
    change ‖candidateEulerBandRowWeight Y ω T B z‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (rowWeight_nonneg Y ω T B z)]
    exact rowWeight_uniform Y hT hTB ω z

/-- One measurable common far mass suffices for a single Markov event. -/
theorem candidate_measurable_farMass (Y : ℕ) (T B h M d : ℝ) :
    Measurable (candidateEulerBandFarMass Y T B h M d) := by
  have hs : Measurable (fun z : Omega × (ℝ × ℝ) => (z.2, z.1)) :=
    measurable_snd.prodMk measurable_fst
  have hm0 := (candidate_measurable_eulerBandRowWeight_joint Y T B).comp hs
  have hm : Measurable (fun z : Omega × (ℝ × ℝ) => candidateEulerBandRowWeight Y z.1 T B z.2) := by
    simpa only [Function.comp_apply] using hm0
  exact (StronglyMeasurable.integral_prod_right (f := fun ω z => candidateEulerBandRowWeight Y ω T B z)
    (ν := (volume.prod volume).restrict (candidateCovarianceFarAnnulus h M d))
    hm.stronglyMeasurable).measurable

theorem candidate_integrable_farMass (Y : ℕ) {T B : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (h M d : ℝ) :
    Integrable (candidateEulerBandFarMass Y T B h M d) mu :=
  (candidate_integrable_farRowWeight_joint Y hT hTB h M d).integral_prod_right

theorem candidate_farMass_nonneg (Y : ℕ) (T B h M d : ℝ) (ω : Omega) :
    0 ≤ candidateEulerBandFarMass Y T B h M d ω :=
  integral_nonneg (rowWeight_nonneg Y ω T B)

/-- Exact Fubini identity for the common far mass. -/
theorem candidate_integral_farMass_eq (Y : ℕ) {T B : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (h M d : ℝ) :
    (∫ ω, candidateEulerBandFarMass Y T B h M d ω ∂mu) =
      ∫ z in candidateCovarianceFarAnnulus h M d,
        (∫ ω, candidateEulerBandRowWeight Y ω T B z ∂mu) ∂volume.prod volume := by
  exact (integral_integral_swap (f := fun z ω => candidateEulerBandRowWeight Y ω T B z)
    (candidate_integrable_farRowWeight_joint Y hT hTB h M d)).symm

/-- Every restricted actual Fourier covariance is dominated by the same
far mass. Its two time endpoints and the possibly random screen disappear
from the upper bound, so they require no union over entries. -/
theorem candidate_restricted_far_covariance_norm_le (Y : ℕ) (ω : Omega)
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (h M d u v : ℝ)
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) (hsub : S ⊆ candidateCovarianceFarAnnulus h M d) :
    ‖∫ z in S, candidateEulerAngularApprox Y 0 ω z.1 *
      starRingEnd ℂ (candidateEulerAngularApprox Y 0 ω z.2) *
      candidateCovariancePhase (u * z.1 - v * z.2) *
      candidateCovarianceWhiteKernel T B (z.1 - z.2) ∂volume.prod volume‖ ≤
        candidateEulerBandFarMass Y T B h M d ω := by
  have he (z : ℝ × ℝ) :
      ‖candidateEulerAngularApprox Y 0 ω z.1 *
        starRingEnd ℂ (candidateEulerAngularApprox Y 0 ω z.2) *
        candidateCovariancePhase (u * z.1 - v * z.2) *
        candidateCovarianceWhiteKernel T B (z.1 - z.2)‖ = candidateEulerBandRowWeight Y ω T B z := by
    simp only [norm_mul, Complex.norm_conj, candidateCovariancePhase,
      Complex.norm_exp_ofReal_mul_I, mul_one, candidateEulerBandRowWeight]
  calc
    _ ≤ ∫ z in S, ‖candidateEulerAngularApprox Y 0 ω z.1 *
        starRingEnd ℂ (candidateEulerAngularApprox Y 0 ω z.2) *
        candidateCovariancePhase (u * z.1 - v * z.2) *
        candidateCovarianceWhiteKernel T B (z.1 - z.2)‖ ∂volume.prod volume :=
      norm_integral_le_integral_norm _
    _ = ∫ z in S, candidateEulerBandRowWeight Y ω T B z ∂volume.prod volume := by simp_rw [he]
    _ ≤ _ := integral_mono_measure (Measure.restrict_mono hsub le_rfl)
      (ae_of_all _ (rowWeight_nonneg Y ω T B)) (rowWeight_integrable_fixed Y ω hT hTB h M d)

/-- A single Markov event under any fixed cylinder controls the common far
mass, retaining exactly the reciprocal cylinder-probability factor. -/
theorem candidate_farMass_cylinder_markov_le (s : Finset ℕ) (η : s → Bool)
    (Y : ℕ) {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (h M d R : ℝ) :
    R * (candidateCylinderLaw s η).real
      {ω | R ≤ candidateEulerBandFarMass Y T B h M d ω} ≤
        (∫ ω, candidateEulerBandFarMass Y T B h M d ω ∂mu) /
          mu.real (candidateCylinder s η) := by
  have hi := candidateCylinderLaw_integral_nonneg_le s η
    (candidate_integrable_farMass Y hT hTB h M d) (candidate_farMass_nonneg Y T B h M d)
  exact (mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (candidate_farMass_nonneg Y T B h M d)) hi.1 R).trans hi.2

end
end Erdos.Problem1144
