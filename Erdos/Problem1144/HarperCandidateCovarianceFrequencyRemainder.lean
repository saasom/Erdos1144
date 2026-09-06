import Erdos.Problem1144.HarperCandidateCovarianceFrequencyCommon

open Finset MeasureTheory Set
open scoped Topology

namespace Erdos.Problem1144

private theorem cauchy_central_le {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ t in {t : ℝ | |t| ≤ δ}, 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) ≤ 8 * δ := by
  have hset : {t : ℝ | |t| ≤ δ} = Icc (-δ) δ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
  rw [hset]
  calc
    _ ≤ ∫ _t in Icc (-δ) δ, (4 : ℝ) := by
      apply integral_mono_ae Problem520.integrable_one_div_harperCauchyKernel.integrableOn
        (integrable_const _)
      exact ae_of_all _ fun t => by
        apply (div_le_iff₀ (by positivity : 0 < (1 / 2 : ℝ) ^ 2 + t ^ 2)).mpr
        nlinarith [sq_nonneg t]
    _ = 8 * δ := by simp [integral_const, Real.volume_Icc, hδ, smul_eq_mul]; ring

/-- The omitted frequency window has explicit small central and outer
Cauchy mass. Both terms tend to zero under their stated endpoint choices. -/
theorem candidate_integral_cauchyFrequencyRemainder_le (d M : ℕ) (hM : 1 ≤ M) :
    (∫ t in (candidateCovarianceFrequencyWindow d M)ᶜ,
      1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) ≤
        8 * (1 / 2 : ℝ) ^ (d + 1) + 2 / (M : ℝ) := by
  let δ : ℝ := (1 / 2 : ℝ) ^ (d + 1)
  let A : Set ℝ := {t | |t| ≤ δ}
  let B := Problem520.harperEulerTailSet M
  have hA : MeasurableSet A := measurableSet_le measurable_id.abs measurable_const
  have hB : MeasurableSet B := Problem520.measurableSet_harperEulerTailSet M
  have hI := (candidate_measurableSet_covarianceFrequencyWindow d M).compl
  let f : ℝ → ℝ := fun t => 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)
  have hi : Integrable f := Problem520.integrable_one_div_harperCauchyKernel
  have hpoint (t : ℝ) :
      (candidateCovarianceFrequencyWindow d M)ᶜ.indicator f t ≤ A.indicator f t + B.indicator f t := by
    have hn : 0 ≤ f t := by dsimp [f]; positivity
    by_cases ht : t ∈ (candidateCovarianceFrequencyWindow d M)ᶜ
    · rw [Set.indicator_of_mem ht]
      have hAB : t ∈ A ∨ t ∈ B := by
        by_cases hcentral : |t| ≤ δ
        · exact Or.inl hcentral
        · have hlarge : (M : ℝ) < |t| := by
            have ht' : ¬ (δ < |t| ∧ |t| ≤ (M : ℝ)) := ht
            exact lt_of_not_ge (fun h => ht' ⟨lt_of_not_ge hcentral, h⟩)
          right
          rcases lt_abs.mp hlarge with h | h
          · exact Or.inr h.le
          · exact Or.inl (show t ≤ -(M : ℝ) by linarith)
      rcases hAB with ha | hb
      · rw [Set.indicator_of_mem ha]
        exact le_add_of_nonneg_right (Set.indicator_nonneg (fun _ _ => by dsimp [f]; positivity) t)
      · rw [Set.indicator_of_mem hb]
        exact le_add_of_nonneg_left (Set.indicator_nonneg (fun _ _ => by dsimp [f]; positivity) t)
    · rw [Set.indicator_of_notMem ht]
      exact add_nonneg (Set.indicator_nonneg (fun _ _ => by dsimp [f]; positivity) t)
        (Set.indicator_nonneg (fun _ _ => by dsimp [f]; positivity) t)
  have h := integral_mono (hi.indicator hI) ((hi.indicator hA).add (hi.indicator hB)) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (hi.indicator hA) (hi.indicator hB), integral_indicator hI,
    integral_indicator hA, integral_indicator hB] at h
  exact h.trans (add_le_add (cauchy_central_le (by positivity))
    (Problem520.integral_harperEulerTailSet_one_div_cauchyKernel_le hM))

/-- Actual angular Euler energy outside the retained window. Together with
the common-mesh deletion bound, this charges every discarded frequency. -/
theorem candidate_integral_angularFrequencyRemainder_le (y d M : ℕ) (hM : 1 ≤ M) :
    (∫ ω, (∫ t in (candidateCovarianceFrequencyWindow d M)ᶜ,
      ‖candidateEulerAngularApprox y 0 ω t‖ ^ 2) ∂mu) ≤
      Problem520.primeEnergyNormalizer y *
        (8 * (1 / 2 : ℝ) ^ (d + 1) + 2 / (M : ℝ)) := by
  have heq : (∫ ω, (∫ t in (candidateCovarianceFrequencyWindow d M)ᶜ,
      ‖candidateEulerAngularApprox y 0 ω t‖ ^ 2) ∂mu) =
      Problem520.primeEnergyNormalizer y *
        ∫ t in (candidateCovarianceFrequencyWindow d M)ᶜ,
          1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by
    have h := candidate_integral_eulerFrequencyMass_eq y
      (candidateCovarianceFrequencyWindow d M)ᶜ (G := Set.univ) MeasurableSet.univ
    simp only [candidateEulerFrequencyMass, Set.indicator_univ, Set.mem_univ,
      Set.setOf_true, Measure.restrict_univ, Problem520.integral_harperEulerDensity] at h
    simp_rw [candidate_criticalEuler_norm_sq_eq_cauchyDensity]
    change (∫ ω, (∫ t in (candidateCovarianceFrequencyWindow d M)ᶜ,
      Problem520.harperEulerDensity y ω t / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) ∂Problem520.μ) = _
    rw [h, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun t => by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (candidate_integral_cauchyFrequencyRemainder_le d M hM)
    (Problem520.primeEnergyNormalizer_pos y).le

end Erdos.Problem1144
