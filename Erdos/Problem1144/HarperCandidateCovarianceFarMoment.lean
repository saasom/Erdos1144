import Erdos.Problem1144.HarperCandidateCovarianceFarMass
import Erdos.Problem1144.HarperCandidateCovarianceHalfDensityEnvelope
import Erdos.Problem1144.HarperCandidateCovarianceFarGapIntegral

open MeasureTheory Set

namespace Erdos.Problem1144

private theorem half_pair_integrable (Y : ℕ) (t v : ℝ) :
    Integrable (fun ω : Omega => Real.sqrt (Problem520.harperEulerDensity Y ω t) *
      Real.sqrt (Problem520.harperEulerDensity Y ω v)) mu := by
  have hm : Measurable (fun ω : Omega => Real.sqrt (Problem520.harperEulerDensity Y ω t) *
      Real.sqrt (Problem520.harperEulerDensity Y ω v)) :=
    (Problem520.stronglyMeasurable_harperEulerDensity Y t).measurable.sqrt.mul
      (Problem520.stronglyMeasurable_harperEulerDensity Y v).measurable.sqrt
  apply (integrable_const (Real.sqrt (Problem520.harperEulerDensityUniformBound Y) *
    Real.sqrt (Problem520.harperEulerDensityUniformBound Y))).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact mul_le_mul
      (Real.sqrt_le_sqrt (Problem520.harperEulerDensity_le_uniformBound Y ω t))
      (Real.sqrt_le_sqrt (Problem520.harperEulerDensity_le_uniformBound Y ω v))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

private theorem integral_rowWeight_le (Y : ℕ) (T B : ℝ) (z : ℝ × ℝ) :
    (∫ ω, candidateEulerBandRowWeight Y ω T B z ∂mu) ≤
      4 * (∫ ω, Real.sqrt (Problem520.harperEulerDensity Y ω z.1) *
        Real.sqrt (Problem520.harperEulerDensity Y ω z.2) ∂mu) *
          ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖ := by
  have hi := ((half_pair_integrable Y z.1 z.2).const_mul 4).mul_const
    ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖
  have hp : Measurable (fun ω : Omega => (z, ω)) := measurable_const.prodMk measurable_id
  have hm0 := (candidate_measurable_eulerBandRowWeight_joint Y T B).comp hp
  have hm : Measurable (fun ω : Omega => candidateEulerBandRowWeight Y ω T B z) := by
    simpa only [Function.comp_apply] using hm0
  have hn (ω : Omega) : 0 ≤ candidateEulerBandRowWeight Y ω T B z := by
    unfold candidateEulerBandRowWeight
    positivity
  have hri : Integrable (fun ω : Omega => candidateEulerBandRowWeight Y ω T B z) mu :=
    hi.mono' hm.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hn ω)]
      exact candidate_eulerBandRowWeight_le_halfDensityPair Y ω T B z)
  have hb := integral_mono hri hi (fun ω => candidate_eulerBandRowWeight_le_halfDensityPair Y ω T B z)
  simpa only [integral_mul_const, integral_const_mul] using hb

/-- The actual common far mass has a uniform expectation bound. This
combines the arithmetic half-density moment, exact Fubini, both clipped
correlation channels, and the reciprocal-time kernel integral. The result
has no additional integrability, moment, or comparison premise. -/
theorem candidate_exists_farMass_expectation_bound :
    ∃ C > 0, ∃ J : ℕ, ∀ start stop : ℕ, J ≤ start → start ≤ stop →
      ∀ h M d T B : ℝ, 0 < h → 0 ≤ M → 0 < d → 0 < T → T ≤ B →
        2 * M ≤ candidateCovarianceHeightWindow start →
        let A := Real.log (Problem520.harperBlockEndpoint start : ℝ)
        let L := Real.log (Problem520.harperBlockEndpoint stop : ℝ)
        let U := A * (2 * M) + 3 * Real.log (1 + L * (2 * M))
        (∫ ω, candidateEulerBandFarMass (Problem520.harperBlockEndpoint stop)
          T B h M d ω ∂mu) ≤
          C * Real.sqrt L * Real.sqrt (max A (1 / h)) * Real.sqrt (A + 2 / d) *
            (2 * (Real.log (B / T) + 2) * Real.log (1 + T * (2 * M)) / T) *
            (Real.sqrt (2 * M) * Real.sqrt U) := by
  obtain ⟨C, hC, J, hmoment⟩ := candidate_exists_halfDensityPair_gapEnvelope_moment_bound
  refine ⟨4 * C, by positivity, J, ?_⟩
  intro start stop hstart hss h M d T B hh hM hd hT hTB hwin
  let Y := Problem520.harperBlockEndpoint stop
  let A := Real.log (Problem520.harperBlockEndpoint start : ℝ)
  let L := Real.log (Y : ℝ)
  let G := candidateCovarianceGapEnvelope start stop
  let S := candidateCovarianceFarAnnulus h M d
  let F : (ℝ × ℝ) → ℝ := fun z => Real.sqrt (G |z.1 - z.2|) *
    Real.sqrt (G |z.1 + z.2|) * ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖
  let V := (4 * C) * Real.sqrt L * Real.sqrt (max A (1 / h))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hFn (z : ℝ × ℝ) : 0 ≤ F z := by dsimp [F]; positivity
  have hsub : S ⊆ candidateCovarianceFarFrequencyDomain M d := by
    intro z hz
    exact ⟨hz.2.1, hz.2.2.2.1, hz.2.2.2.2⟩
  have hFi : IntegrableOn F (candidateCovarianceFarFrequencyDomain M d) (volume.prod volume) :=
    candidate_integrableOn_far_gapKernel start stop hT hTB M d
  have hpoint (z : ℝ × ℝ) (hz : z ∈ S) :
      (∫ ω, candidateEulerBandRowWeight Y ω T B z ∂mu) ≤ V * F z := by
    have hm := hmoment start stop hstart hss h M z.1 z.2 hh hz.1 hz.2.2.1 hz.2.1 hz.2.2.2.1 hwin
    calc
      _ ≤ 4 * (∫ ω, Real.sqrt (Problem520.harperEulerDensity Y ω z.1) *
          Real.sqrt (Problem520.harperEulerDensity Y ω z.2) ∂mu) *
            ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖ := integral_rowWeight_le Y T B z
      _ ≤ 4 * (C * Real.sqrt L * Real.sqrt (max A (1 / h)) *
          Real.sqrt (G |z.1 - z.2|) * Real.sqrt (G |z.1 + z.2|)) *
            ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num)) (norm_nonneg _)
      _ = _ := by dsimp only [V, F]; ring
  have hi := (candidate_integrable_farRowWeight_joint Y hT hTB h M d).integral_prod_left
  rw [candidate_integral_farMass_eq Y hT hTB]
  dsimp only
  calc
    _ ≤ ∫ z in S, V * F z ∂volume.prod volume :=
      integral_mono_ae hi ((hFi.mono_set hsub).const_mul V)
        ((ae_restrict_mem (candidate_measurableSet_farAnnulus h M d)).mono fun z hz => hpoint z hz)
    _ = V * ∫ z in S, F z ∂volume.prod volume := integral_const_mul _ _
    _ ≤ V * ∫ z in candidateCovarianceFarFrequencyDomain M d, F z ∂volume.prod volume :=
      mul_le_mul_of_nonneg_left
        (integral_mono_measure (Measure.restrict_mono hsub le_rfl) (ae_of_all _ hFn) hFi) hV
    _ ≤ V * (Real.sqrt (A + 2 / d) *
        (2 * (Real.log (B / T) + 2) * Real.log (1 + T * (2 * M)) / T) *
        (Real.sqrt (2 * M) * Real.sqrt (A * (2 * M) + 3 * Real.log (1 + L * (2 * M))))) :=
      mul_le_mul_of_nonneg_left (candidate_integral_far_gapKernel_le start stop hT hTB hM hd) hV
    _ = _ := by dsimp only [V, A, L, Y]; ring

end Erdos.Problem1144
