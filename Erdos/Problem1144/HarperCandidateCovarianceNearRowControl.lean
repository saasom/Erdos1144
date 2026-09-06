import Erdos.Problem1144.HarperCandidateCovarianceNearRowMoment
import Erdos.Problem1144.HarperCandidateSpectralTail

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- Every retained subset of the actual frequency screen has the same common
near-row envelope. The grid spacing is exactly `2π`; its origin and fixed row
endpoint are arbitrary and do not occur in the upper bound. -/
theorem candidate_retained_near_row_power_sum_le
    (start stop a : ℕ) (ω : Problem520.Omega) (W M d u v : ℝ)
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (N k : ℕ)
    (S : Set ℝ) (hS : S ⊆ candidateCovarianceScreenedHeightSet
      start (stop - start) W M (Finset.Icc (a - start) (stop - start)) ω) :
    (∑ j ∈ range N, ‖∫ z, candidateEulerAngularApprox
        (Problem520.harperBlockEndpoint stop) 0 ω z.1 *
      starRingEnd ℂ (candidateEulerAngularApprox (Problem520.harperBlockEndpoint stop) 0 ω z.2) *
      candidateCovariancePhase (u * z.1 - (v + j * (2 * Real.pi)) * z.2) *
      candidateCovarianceWhiteKernel T B (z.1 - z.2)
      ∂(((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
        (candidateRowPairDomain S d))‖ ^ (2 * k)) ≤
      candidateEulerBandNearRowEnvelope start stop a W M T B d k N ω := by
  let Y := Problem520.harperBlockEndpoint stop
  let Sf := candidateCovarianceScreenedHeightSet start (stop - start) W M
    (Finset.Icc (a - start) (stop - start)) ω
  let ν₀ := (volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))
  let ν := candidateRowPowerMeasure (ν₀.restrict (candidateRowPairDomain S d)) k
  let νf := candidateRowPowerMeasure (ν₀.restrict (candidateRowPairDomain Sf d)) k
  let f := candidateRowProduct (k := k) (candidateEulerBandRowWeight Y ω T B)
  let X := fun z : (Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ) =>
    candidateRowPowerFrequency Prod.snd z
  have hmeasure : ν ≤ νf := by
    dsimp only [ν, νf]
    rw [candidate_rowPowerMeasure_restrict, candidate_rowPowerMeasure_restrict]
    apply Measure.restrict_mono _ le_rfl
    intro z hz
    constructor
    · intro i hi
      exact ⟨hS (hz.1 i hi).1, hS (hz.1 i hi).2.1, (hz.1 i hi).2.2⟩
    · intro i hi
      exact ⟨hS (hz.2 i hi).1, hS (hz.2 i hi).2.1, (hz.2 i hi).2.2⟩
  have hX : Measurable X := by unfold X candidateRowPowerFrequency; fun_prop
  have hfi : Integrable f νf :=
    candidate_integrable_screened_pairedEuler_rowProduct Y ω start (stop - start) W M
      (Finset.Icc (a - start) (stop - start)) d k hT hTB
  have hwi := candidate_integrable_mul_rowFourierSum_norm νf N X hX f hfi
  have hn (z) : 0 ≤ f z * ‖candidateRowFourierSum N (-(2 * Real.pi)) (X z)‖ := by
    dsimp only [f, candidateRowProduct, candidateEulerBandRowWeight]
    exact mul_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
      (Finset.prod_nonneg fun _ _ => by positivity)) (norm_nonneg _)
  have h := candidate_eulerBand_restricted_row_power_sum_le Y ω M u v
    (2 * Real.pi) hT hTB (candidateRowPairDomain S d) N k
  exact h.trans (integral_mono_measure hmeasure (ae_of_all _ hn) hwi)

/-- The original actual screened near Fourier row is bounded by the same
nonnegative envelope for every fixed row endpoint and affine grid origin. -/
theorem candidate_screened_near_row_power_sum_le
    (start stop a : ℕ) (ω : Problem520.Omega) (W M d u v : ℝ)
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (N k : ℕ) :
    (∑ j ∈ range N, ‖∫ z, candidateEulerAngularApprox
        (Problem520.harperBlockEndpoint stop) 0 ω z.1 *
      starRingEnd ℂ (candidateEulerAngularApprox (Problem520.harperBlockEndpoint stop) 0 ω z.2) *
      candidateCovariancePhase (u * z.1 - (v + j * (2 * Real.pi)) * z.2) *
      candidateCovarianceWhiteKernel T B (z.1 - z.2)
      ∂(((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
        (candidateRowPairDomain
          (candidateCovarianceScreenedHeightSet start (stop - start) W M
            (Finset.Icc (a - start) (stop - start)) ω) d))‖ ^ (2 * k)) ≤
      candidateEulerBandNearRowEnvelope start stop a W M T B d k N ω :=
  candidate_retained_near_row_power_sum_le start stop a ω W M d u v hT hTB N k _
    (fun _ h => h)

/-- One Markov event under any fixed cylinder controls the common near-row
envelope. The conditioning cost is exactly the reciprocal cylinder probability. -/
theorem candidate_nearRowEnvelope_cylinder_markov_le (s : Finset ℕ) (η : s → Bool)
    (start stop a : ℕ) (hst : start ≤ stop) (W M T B d : ℝ) (k N : ℕ) (R : ℝ) :
    R * (candidateCylinderLaw s η).real
      {ω | R ≤ candidateEulerBandNearRowEnvelope start stop a W M T B d k N ω} ≤
        (∫ ω, candidateEulerBandNearRowEnvelope start stop a W M T B d k N ω ∂Problem520.μ) /
          Problem520.μ.real (candidateCylinder s η) := by
  have hi := candidateCylinderLaw_integral_nonneg_le s η
    (candidate_integrable_nearRowEnvelope start stop a hst W M T B d k N)
    (candidate_nearRowEnvelope_nonneg start stop a W M T B d k N)
  exact (mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (candidate_nearRowEnvelope_nonneg start stop a W M T B d k N)) hi.1 R).trans hi.2

end
end Erdos.Problem1144
