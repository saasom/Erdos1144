import Erdos.Problem1144.HarperCandidateCovarianceScreenWhiteKernel
import Erdos.Problem1144.HarperCandidateCovarianceFrequencyRemainder
import Erdos.Problem1144.HarperCandidateCovarianceTerminalFrequency
import Erdos.Problem1144.HarperCandidateCovarianceReflection

open MeasureTheory Set

namespace Erdos.Problem1144
noncomputable section

/-- The actual annulus with the D-star and inclusive strong-prefix screens. -/
def candidateCovarianceRetainedFrequencySet (start N d M : ℕ) (W : ℝ)
    (s : Finset ℕ) (ω : Omega) : Set ℝ :=
  candidateCovarianceFrequencyWindow d M ∩ candidateCovarianceScreenedHeightSet start N W M s ω

theorem candidate_measurableSet_retainedFrequencySet (start N d M : ℕ) (W : ℝ)
    (s : Finset ℕ) (ω : Omega) :
    MeasurableSet (candidateCovarianceRetainedFrequencySet start N d M W s ω) :=
  (candidate_measurableSet_covarianceFrequencyWindow d M).inter
    (candidate_measurableSet_screenedHeightSet start N W M s ω)

theorem candidate_measurableSet_retainedFrequencyGraph (start N d M : ℕ) (W : ℝ)
    (s : Finset ℕ) :
    MeasurableSet {z : Omega × ℝ | z.2 ∈ candidateCovarianceRetainedFrequencySet start N d M W s z.1} := by
  have hd := (candidate_measurableSet_covarianceDStar_joint start N W).preimage
    (measurable_snd.prodMk measurable_fst)
  have hs := (candidate_measurableSet_covarianceStrongScreen_joint start W s).preimage
    (measurable_snd.prodMk measurable_fst)
  exact ((candidate_measurableSet_covarianceFrequencyWindow d M).preimage measurable_snd).inter
    ((measurableSet_le measurable_snd.abs measurable_const).inter (hd.inter hs))

theorem candidate_retainedFrequencySet_subset_band (start N d M : ℕ) (W : ℝ)
    (s : Finset ℕ) (ω : Omega) {H : ℝ} (hH : (M : ℝ) ≤ H) :
    candidateCovarianceRetainedFrequencySet start N d M W s ω ⊆ Icc (-H) H := by
  intro t ht
  exact abs_le.mp (ht.1.2.trans hH)

theorem candidate_mem_retainedFrequencySet_neg (start N d M : ℕ) (W : ℝ)
    (s : Finset ℕ) (ω : Omega) (t : ℝ) :
    -t ∈ candidateCovarianceRetainedFrequencySet start N d M W s ω ↔
      t ∈ candidateCovarianceRetainedFrequencySet start N d M W s ω := by
  simp only [candidateCovarianceRetainedFrequencySet, mem_inter_iff,
    candidate_mem_screenedHeightSet_neg, candidateCovarianceFrequencyWindow, mem_setOf_eq, abs_neg]

/-- Common coefficient-error budget: all outside-annulus energy and the
literal screen deletion on the common mesh event, with Parseval normalization. -/
def candidateCovarianceRetainedError (y start N d M : ℕ) (W T : ℝ)
    (s : Finset ℕ) (ω : Omega) : ℝ :=
  (candidateEulerFrequencyMass y (candidateCovarianceFrequencyWindow d M)ᶜ Set.univ ω +
    candidateEulerFrequencyMass y (candidateCovarianceFrequencyWindow d M)
      (candidateCovarianceCommonFrequencyDeletionGraph start N M W s) ω) / (2 * Real.pi * T)

theorem candidate_retainedError_nonneg (y start N d M : ℕ) (W : ℝ) {T : ℝ}
    (hT : 0 ≤ T) (s : Finset ℕ) (ω : Omega) :
    0 ≤ candidateCovarianceRetainedError y start N d M W T s ω :=
  div_nonneg (add_nonneg (candidate_eulerFrequencyMass_nonneg _ _ _ _)
    (candidate_eulerFrequencyMass_nonneg _ _ _ _)) (by positivity)

theorem candidate_integrable_retainedError (y start N d M : ℕ) (W T : ℝ) (s : Finset ℕ) :
    Integrable (candidateCovarianceRetainedError y start N d M W T s) mu :=
  ((candidate_integrable_eulerFrequencyMass y _ MeasurableSet.univ).add
    (candidate_integrable_eulerFrequencyMass y _
      (candidate_measurableSet_covarianceCommonFrequencyDeletion start N M W s))).div_const _

/-- On the common mesh event, this single budget controls the coefficient
error at every time, simultaneously. Every omitted frequency is paid for. -/
theorem candidate_retainedWhiteKernel_distance_le (y start N d M : ℕ) (W : ℝ)
    (s : Finset ℕ) {ω : Omega} (hω : ω ∈ candidateCovarianceCommonMeshEvent start N M W)
    {H T : ℝ} (hH : (M : ℝ) ≤ H) (hT : 0 < T) (B u : ℝ) :
    (∫ r, (candidateEulerScreenWhiteKernel y ω
      (candidateCovarianceRetainedFrequencySet start N d M W s ω) T B u r -
      candidateEulerBandWhiteKernel y ω H T B u r) ^ 2) ≤
        candidateCovarianceRetainedError y start N d M W T s ω := by
  let I := candidateCovarianceFrequencyWindow d M
  let S := candidateCovarianceRetainedFrequencySet start N d M W s ω
  let F : ℝ → ℝ := fun t => ‖candidateEulerAngularApprox y 0 ω t‖ ^ 2
  let D : Set ℝ := {t | ω ∉ candidateCovarianceDStarEvent start N t W ∩
    candidateCovarianceStrongScreenEvent start t W s}
  have hI : MeasurableSet I := candidate_measurableSet_covarianceFrequencyWindow d M
  have hS : MeasurableSet S := candidate_measurableSet_retainedFrequencySet start N d M W s ω
  have hD : MeasurableSet D := by
    exact (((candidate_measurableSet_covarianceDStar_joint start N W).inter
      (candidate_measurableSet_covarianceStrongScreen_joint start W s)).preimage
        (measurable_id.prodMk measurable_const)).compl
  have hFi : Integrable F := by
    simp only [F, candidate_criticalEuler_norm_sq_eq_cauchyDensity]
    convert Problem520.integrable_harperEulerDensity_div_cauchyKernel y ω using 1 <;> norm_num
  have hFn : ∀ t, 0 ≤ F t := fun t => sq_nonneg _
  have hsub : Icc (-H) H \ S ⊆ Iᶜ ∪ (I ∩ D) := by
    intro t ht
    by_cases htI : t ∈ I
    · right
      refine ⟨htI, ?_⟩
      intro hgood
      apply ht.2
      exact ⟨htI, htI.2, hgood.1, hgood.2⟩
    · exact Or.inl htI
  have hdisj : Disjoint Iᶜ (I ∩ D) := Set.disjoint_left.mpr (fun _ ht htd => ht htd.1)
  have he : (∫ t in Icc (-H) H \ S, F t) ≤ (∫ t in Iᶜ, F t) + ∫ t in I ∩ D, F t := by
    calc
      _ ≤ ∫ t in Iᶜ ∪ (I ∩ D), F t := setIntegral_mono_set hFi.integrableOn
        (ae_of_all _ hFn) (ae_of_all _ hsub)
      _ = _ := setIntegral_union hdisj (hI.inter hD) hFi.integrableOn hFi.integrableOn
  have hR : candidateEulerFrequencyMass y Iᶜ Set.univ ω = ∫ t in Iᶜ, F t := by
    rw [candidate_eulerFrequencyMass_eq_angular]
    simp only [indicator_univ, F]
  have hC : candidateEulerFrequencyMass y I
      (candidateCovarianceCommonFrequencyDeletionGraph start N M W s) ω = ∫ t in I ∩ D, F t := by
    rw [candidate_commonFrequencyMass_eq_angular_deleted y start N M W s I hω,
      integral_indicator hD, Measure.restrict_restrict hD, inter_comm]
  have hh := candidate_eulerScreenWhiteKernel_distance_le y ω hS H
    (candidate_retainedFrequencySet_subset_band start N d M W s ω hH) B u hT
  refine hh.trans ?_
  change (1 / (2 * Real.pi * T)) * (∫ t in Icc (-H) H \ S, F t) ≤ _
  unfold candidateCovarianceRetainedError
  rw [show candidateCovarianceFrequencyWindow d M = I from rfl, hR, hC]
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
    mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 1 / (2 * Real.pi * T))

set_option backward.isDefEq.respectTransparency false in
/-- The common coefficient-error expectation is an explicit numerical
budget, including the entire terminal strong prefix and both annulus tails. -/
theorem candidate_exists_retainedError_integral_bound :
    ∃ C ≥ 0, ∃ D ≥ 0, ∃ J : ℕ, ∀ d start M : ℕ, J + d ≤ start →
      1 ≤ M → (M : ℝ) ≤ candidateCovarianceHeightWindow start →
      ∀ N a : ℕ, 3 ≤ N → 3 ≤ a → ∀ s : Finset ℕ,
      (∀ j ∈ s, a ≤ j ∧ j ≤ N) → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + N) ≤ y →
      ∀ W T : ℝ, 1 ≤ W → 0 < T →
      (∫ ω, candidateCovarianceRetainedError y start N d M W T s ω ∂mu) ≤
        Problem520.primeEnergyNormalizer y / (2 * Real.pi * T) *
          (8 * (1 / 2 : ℝ) ^ (d + 1) + 2 / (M : ℝ) +
            2 * Real.pi * (candidateCovarianceFrequencyDeletionBudget C W start N a (s.erase N) +
              candidateCovarianceTerminalDeletionBudget D W start N)) := by
  obtain ⟨C, hC, D, hD, J, hb⟩ :=
    candidate_exists_covarianceCommonFrequencyDeletion_terminal_integral_le
  refine ⟨C, hC, D, hD, J, ?_⟩
  intro d start M hstart hM hwindow N a hN ha s hs y hy W T hW hT
  have hdel := hb d start M hstart hwindow N a hN ha s hs y hy W hW
  have hrem := candidate_integral_angularFrequencyRemainder_le y d M hM
  have hiR := candidate_integrable_eulerFrequencyMass y
    (candidateCovarianceFrequencyWindow d M)ᶜ (G := Set.univ) MeasurableSet.univ
  have hiD := candidate_integrable_eulerFrequencyMass y
    (candidateCovarianceFrequencyWindow d M)
    (candidate_measurableSet_covarianceCommonFrequencyDeletion start N M W s)
  rw [show Problem520.μ = mu from rfl] at hiR hiD hdel
  have heR : (∫ ω, candidateEulerFrequencyMass y (candidateCovarianceFrequencyWindow d M)ᶜ
      Set.univ ω ∂mu) = ∫ ω, (∫ t in (candidateCovarianceFrequencyWindow d M)ᶜ,
        ‖candidateEulerAngularApprox y 0 ω t‖ ^ 2) ∂mu := by
    simp_rw [candidate_eulerFrequencyMass_eq_angular, indicator_univ]
  unfold candidateCovarianceRetainedError
  rw [integral_div, integral_add hiR hiD, heR]
  have hh := div_le_div_of_nonneg_right (add_le_add hrem hdel)
    (by positivity : 0 ≤ 2 * Real.pi * T)
  convert hh using 1 <;> ring

end
end Erdos.Problem1144
