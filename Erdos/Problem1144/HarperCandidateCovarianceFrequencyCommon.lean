import Erdos.Problem1144.HarperCandidateCovarianceFrequencyDeletion
import Erdos.Problem1144.HarperCandidateSpectralTail

open Finset MeasureTheory Set
open scoped Topology

namespace Erdos.Problem1144

/-- Deletion from the single common upper mesh event, followed by the
literal frequency-dependent D-star and strong screens. -/
def candidateCovarianceCommonFrequencyDeletionGraph
    (start N : ℕ) (M W : ℝ) (s : Finset ℕ) : Set (ℝ × Problem520.Omega) :=
  {z | z.2 ∈ candidateCovarianceCommonMeshEvent start N M W ∧
    z.2 ∉ candidateCovarianceDStarEvent start N z.1 W ∩
      candidateCovarianceStrongScreenEvent start z.1 W s}

theorem candidate_measurableSet_covarianceCommonFrequencyDeletion
    (start N : ℕ) (M W : ℝ) (s : Finset ℕ) :
    MeasurableSet (candidateCovarianceCommonFrequencyDeletionGraph start N M W s) :=
  ((candidate_measurableSet_covarianceCommonMesh start N M W).preimage measurable_snd).diff
    ((candidate_measurableSet_covarianceDStar_joint start N W).inter
      (candidate_measurableSet_covarianceStrongScreen_joint start W s))

/-- On the common mesh event the measured loss is exactly the actual
angular Fourier energy of the frequencies failing the retained screen. -/
theorem candidate_commonFrequencyMass_eq_angular_deleted
    (y start N : ℕ) (M W : ℝ) (s : Finset ℕ) (I : Set ℝ)
    {ω : Problem520.Omega} (hω : ω ∈ candidateCovarianceCommonMeshEvent start N M W) :
    candidateEulerFrequencyMass y I
        (candidateCovarianceCommonFrequencyDeletionGraph start N M W s) ω =
      ∫ t in I, {t | ω ∉ candidateCovarianceDStarEvent start N t W ∩
        candidateCovarianceStrongScreenEvent start t W s}.indicator
          (fun t => ‖candidateEulerAngularApprox y 0 ω t‖ ^ 2) t := by
  rw [candidate_eulerFrequencyMass_eq_angular]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    dsimp only
    by_cases ht : ω ∉ candidateCovarianceDStarEvent start N t W ∩
        candidateCovarianceStrongScreenEvent start t W s
    · have hleft : (t, ω) ∈ candidateCovarianceCommonFrequencyDeletionGraph start N M W s :=
        ⟨hω, ht⟩
      rw [Set.indicator_of_mem hleft, Set.indicator_of_mem ht]
    · have hleft : (t, ω) ∉ candidateCovarianceCommonFrequencyDeletionGraph start N M W s :=
        fun h => ht h.2
      rw [Set.indicator_of_notMem hleft, Set.indicator_of_notMem ht]

/-- A single common-event loss has the same integrated budget as the
pointwise mesh loss. Every screen, weight and frequency endpoint is literal. -/
theorem candidate_exists_covarianceCommonFrequencyDeletion_integral_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ d start M : ℕ, J + d ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start →
      ∀ N a : ℕ, 3 ≤ a → ∀ s : Finset ℕ,
      (∀ j ∈ s, a ≤ j ∧ j < N) → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + N) ≤ y →
      ∀ W : ℝ, 1 ≤ W →
      (∫ ω, candidateEulerFrequencyMass y (candidateCovarianceFrequencyWindow d M)
        (candidateCovarianceCommonFrequencyDeletionGraph start N M W s) ω ∂Problem520.μ) ≤
      2 * Real.pi * Problem520.primeEnergyNormalizer y *
        candidateCovarianceFrequencyDeletionBudget C W start N a s := by
  obtain ⟨C, hC, J, hJ⟩ := candidate_exists_covarianceFrequencyDeletion_section_le
  refine ⟨C, hC, J, ?_⟩
  intro d start M hstart hM N a ha s hs y hy W hW
  have hsection (t : ℝ) (ht : t ∈ candidateCovarianceFrequencyWindow d M) :
      (∫ ω in {ω | (t, ω) ∈ candidateCovarianceCommonFrequencyDeletionGraph start N M W s},
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
        Problem520.primeEnergyNormalizer y *
          candidateCovarianceFrequencyDeletionBudget C W start N a s := by
    have hsub : {ω | (t, ω) ∈ candidateCovarianceCommonFrequencyDeletionGraph start N M W s} ⊆
        {ω | (t, ω) ∈ candidateCovarianceFrequencyDeletionGraph start N W s} := by
      intro ω hω
      exact ⟨candidate_covarianceCommonMesh_subset start N M W t ht.2 hω.1, hω.2⟩
    have hmono := setIntegral_mono_set (Problem520.integrable_harperEulerDensity y t).integrableOn
      (ae_of_all _ fun ω => Problem520.harperEulerDensity_nonneg y ω t)
      (ae_of_all _ hsub)
    exact hmono.trans (hJ d start M hstart hM N a ha s hs y hy W hW t ht)
  have h := candidate_integral_eulerFrequencyMass_le y
    (candidate_measurableSet_covarianceFrequencyWindow d M)
    (candidate_measurableSet_covarianceCommonFrequencyDeletion start N M W s)
    (mul_nonneg (Problem520.primeEnergyNormalizer_pos y).le
      (candidate_covarianceFrequencyDeletionBudget_nonneg hC hW start N a s)) hsection
  convert h using 1 <;> ring

/-- Frequency deletion remains integrable after any fixed finite
conditioning, with the exact reciprocal-cylinder-probability cost. -/
theorem candidate_commonFrequencyMass_cylinder_integral_le
    (q : Finset ℕ) (η : q → Bool) (y start N : ℕ) (M W : ℝ)
    (s : Finset ℕ) (I : Set ℝ) :
    Integrable (candidateEulerFrequencyMass y I
      (candidateCovarianceCommonFrequencyDeletionGraph start N M W s))
        (candidateCylinderLaw q η) ∧
    (∫ ω, candidateEulerFrequencyMass y I
      (candidateCovarianceCommonFrequencyDeletionGraph start N M W s) ω ∂candidateCylinderLaw q η) ≤
    (∫ ω, candidateEulerFrequencyMass y I
      (candidateCovarianceCommonFrequencyDeletionGraph start N M W s) ω ∂mu) /
      mu.real (candidateCylinder q η) :=
  candidateCylinderLaw_integral_nonneg_le q η
    (candidate_integrable_eulerFrequencyMass y I
      (candidate_measurableSet_covarianceCommonFrequencyDeletion start N M W s))
    (candidate_eulerFrequencyMass_nonneg y I _)

/-- Markov's inequality for the actual deleted angular energy under a
fixed cylinder. Together with the preceding integrated estimate this gives
an explicit probability budget, without an additional deletion premise. -/
theorem candidate_commonFrequencyMass_cylinder_markov_le
    (q : Finset ℕ) (η : q → Bool) (y start N : ℕ) (M W : ℝ)
    (s : Finset ℕ) (I : Set ℝ) (ε : ℝ) :
    ε * (candidateCylinderLaw q η).real
      {ω | ε ≤ candidateEulerFrequencyMass y I
        (candidateCovarianceCommonFrequencyDeletionGraph start N M W s) ω} ≤
    (∫ ω, candidateEulerFrequencyMass y I
      (candidateCovarianceCommonFrequencyDeletionGraph start N M W s) ω ∂mu) /
        mu.real (candidateCylinder q η) := by
  have hi := candidate_commonFrequencyMass_cylinder_integral_le q η y start N M W s I
  exact (mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (candidate_eulerFrequencyMass_nonneg y I _)) hi.1 ε).trans hi.2

end Erdos.Problem1144
