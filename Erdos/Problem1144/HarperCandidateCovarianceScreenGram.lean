import Erdos.Problem1144.HarperCandidateCovarianceScreenWhiteKernel

open MeasureTheory Set

namespace Erdos.Problem1144
noncomputable section

/-- Exact complex covariance formula on the literal measurable frequency
screen. The frequency integral uses ordinary product Lebesgue measure. -/
theorem candidate_finiteEuler_white_screen_covariance_eq
    (Y : ℕ) (ω : Omega) {S : Set ℝ} (hS : MeasurableSet S)
    (H : ℝ) (hsub : S ⊆ Icc (-H) H) (u v B : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ r in Icc T B, ((1 / r : ℝ) : ℂ) *
      candidateCovarianceScreenInverse (candidateEulerAngularApprox Y 0 ω) S (u - r) *
      starRingEnd ℂ
        (candidateCovarianceScreenInverse (candidateEulerAngularApprox Y 0 ω) S (v - r))) =
    (2 * Real.pi : ℂ)⁻¹ ^ 2 * ∫ z in S ×ˢ S,
      candidateEulerAngularApprox Y 0 ω z.1 *
        starRingEnd ℂ (candidateEulerAngularApprox Y 0 ω z.2) *
        candidateCovariancePhase (u * z.1 - v * z.2) *
        candidateCovarianceWhiteKernel T B (z.1 - z.2) ∂volume.prod volume := by
  let A := candidateEulerAngularApprox Y 0 ω
  let ν : Measure ℝ := volume.restrict (Icc (-H) H)
  have hw : IntegrableOn (fun r : ℝ => ((1 / r : ℝ) : ℂ)) (Icc T B) := by
    apply ContinuousOn.integrableOn_Icc
    apply Complex.continuous_ofReal.comp_continuousOn
    exact continuousOn_const.div continuousOn_id (fun r hr => (hT.trans_le hr.1).ne')
  have hAc := candidate_continuous_criticalEulerAngularApprox Y ω
  have hAi : IntegrableOn (S.indicator A) (Icc (-H) H) :=
    hAc.integrableOn_Icc.indicator hS
  simp_rw [candidate_screenInverse_eq_bandInverse (candidateEulerAngularApprox Y 0 ω) hS H hsub]
  rw [candidate_band_covariance_eq_measureKernel _ _ _ _ _ _ (by fun_prop) hw
    (hAc.measurable.indicator hS) hAi]
  congr 1
  let F : ℝ × ℝ → ℂ := fun z => A z.1 * starRingEnd ℂ (A z.2) *
    candidateCovariancePhase (u * z.1 - v * z.2) *
      candidateCovarianceWhiteKernel T B (z.1 - z.2)
  have he (z : ℝ × ℝ) :
      S.indicator A z.1 * starRingEnd ℂ (S.indicator A z.2) *
        candidateCovariancePhase (u * z.1 - v * z.2) *
        candidateCovarianceWhiteKernel T B (z.1 - z.2) =
      (S ×ˢ S).indicator F z := by
    by_cases h₁ : z.1 ∈ S <;> by_cases h₂ : z.2 ∈ S <;> simp [F, h₁, h₂]
  change (∫ z, S.indicator A z.1 * starRingEnd ℂ (S.indicator A z.2) *
    candidateCovariancePhase (u * z.1 - v * z.2) *
    candidateCovarianceWhiteKernel T B (z.1 - z.2) ∂ν.prod ν) =
      ∫ z in S ×ˢ S, F z ∂volume.prod volume
  simp_rw [he]
  rw [integral_indicator (hS.prod hS), ← Measure.prod_restrict]
  have hν : ν.restrict S = volume.restrict S := by
    dsimp only [ν]
    rw [Measure.restrict_restrict hS, inter_eq_left.mpr hsub]
  rw [hν, Measure.prod_restrict]

/-- The real screened white Gram entry is exactly the raw Euler double
integral multiplied by `(2π)⁻²`. Symmetry discharges realness of the inverse. -/
theorem candidate_eulerScreenWhiteKernel_covariance_eq (Y : ℕ) (ω : Omega)
    {S : Set ℝ} (hS : MeasurableSet S) (hSym : ∀ τ, τ ∈ S ↔ -τ ∈ S)
    (H : ℝ) (hsub : S ⊆ Icc (-H) H) (B u v : ℝ) {T : ℝ} (hT : 0 < T) :
    ((∫ r, candidateEulerScreenWhiteKernel Y ω S T B u r *
      candidateEulerScreenWhiteKernel Y ω S T B v r : ℝ) : ℂ) =
    (2 * Real.pi : ℂ)⁻¹ ^ 2 * ∫ z in S ×ˢ S,
      candidateEulerAngularApprox Y 0 ω z.1 *
        starRingEnd ℂ (candidateEulerAngularApprox Y 0 ω z.2) *
        candidateCovariancePhase (u * z.1 - v * z.2) *
        candidateCovarianceWhiteKernel T B (z.1 - z.2) ∂volume.prod volume := by
  have he : ((∫ r, candidateEulerScreenWhiteKernel Y ω S T B u r *
      candidateEulerScreenWhiteKernel Y ω S T B v r : ℝ) : ℂ) =
      ∫ r in Icc T B, ((1 / r : ℝ) : ℂ) *
        candidateCovarianceScreenInverse (candidateEulerAngularApprox Y 0 ω) S (u - r) *
        starRingEnd ℂ
          (candidateCovarianceScreenInverse (candidateEulerAngularApprox Y 0 ω) S (v - r)) := by
    rw [← integral_complex_ofReal, integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact ae_of_all _ fun r => by
      by_cases hr : r ∈ Ioc T B
      · have hr0 : 0 ≤ r := (hT.trans hr.1).le
        simp only [candidateEulerScreenWhiteKernel, indicator_of_mem hr]
        have ha :
            (candidateCovarianceScreenInverse (candidateEulerAngularApprox Y 0 ω) S (u - r)).re /
              Real.sqrt r *
              ((candidateCovarianceScreenInverse (candidateEulerAngularApprox Y 0 ω) S (v - r)).re /
                Real.sqrt r) =
            (1 / r) *
              (candidateCovarianceScreenInverse (candidateEulerAngularApprox Y 0 ω) S (u - r)).re *
              (candidateCovarianceScreenInverse (candidateEulerAngularApprox Y 0 ω) S (v - r)).re := by
          rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hr0]
          ring
        rw [ha]
        simp only [Complex.ofReal_mul, candidate_eulerScreenInverse_ofReal_re Y ω hS hSym,
          candidate_screenInverse_conj (candidate_criticalEuler_conj Y ω) hS hSym]
      · simp [candidateEulerScreenWhiteKernel, hr]
  exact he.trans (candidate_finiteEuler_white_screen_covariance_eq Y ω hS H hsub u v B hT)

end
end Erdos.Problem1144
