import Erdos.Problem1144.HarperCandidateCovarianceTerminalScreen
import Erdos.Problem1144.HarperCandidateCovarianceFrequencyCommon

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

private theorem dyadic_cover (d : ℕ) {x : ℝ}
    (hx : (1 / 2 : ℝ) ^ (d + 1) < x) (hx1 : x ≤ 1) :
    ∃ j ≤ d, (1 / 2 : ℝ) ^ (j + 1) < x ∧ x ≤ (1 / 2 : ℝ) ^ j := by
  induction d with
  | zero => exact ⟨0, le_refl _, hx, by simpa using hx1⟩
  | succ d ih =>
    by_cases h : (1 / 2 : ℝ) ^ (d + 1) < x
    · obtain ⟨j, hj, hlow, hhigh⟩ := ih h
      exact ⟨j, by omega, hlow, hhigh⟩
    · exact ⟨d + 1, le_refl _, hx, le_of_not_gt h⟩

/-- The paid terminal loss is uniform across the entire retained frequency
window, including every central dyadic band and the growing outer part. -/
theorem candidate_exists_DStar_terminal_frequency_section_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ d start M : ℕ, J + d ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start → ∀ N : ℕ, 3 ≤ N →
      ∀ y : ℕ, Problem520.harperBlockEndpoint (start + N) ≤ y →
      ∀ W : ℝ, 1 ≤ W → ∀ t ∈ candidateCovarianceFrequencyWindow d M,
      (∫ ω in candidateCovarianceDStarEvent start N t W \
        candidateCovarianceStrongScreenEvent start t W {N},
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
      Problem520.primeEnergyNormalizer y * candidateCovarianceTerminalDeletionBudget C W start N := by
  obtain ⟨Cg, hCg, Jg, hG⟩ := candidate_exists_growingHeight_DStar_terminal_deletion_le
  obtain ⟨Cc, hCc, Jc, hK⟩ := candidate_exists_centralBand_DStar_terminal_deletion_le
  refine ⟨Cg + Cc, by positivity, max Jg Jc, ?_⟩
  intro d start M hstart hM N hN y hy W hW t ht
  by_cases ht1 : 1 ≤ |t|
  · exact (hG start M (by omega) hM N hN y hy t ht1 ht.2 W hW).trans
      (mul_le_mul_of_nonneg_left
        (candidate_covarianceTerminalDeletionBudget_mono hCg (by linarith) hW start N)
        (Problem520.primeEnergyNormalizer_pos y).le)
  · obtain ⟨j, hj, hjlo, hjhi⟩ := dyadic_cover d ht.1 (le_of_not_ge ht1)
    exact (hK j start (by omega) N hN y hy t hjlo hjhi W hW).trans
      (mul_le_mul_of_nonneg_left
        (candidate_covarianceTerminalDeletionBudget_mono hCc (by linarith) hW start N)
        (Problem520.primeEnergyNormalizer_pos y).le)

private theorem setIntegral_le_add_of_subset_union (y : ℕ) (t : ℝ)
    {D A B : Set Problem520.Omega} (hD : MeasurableSet D)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hsub : D ⊆ A ∪ B) :
    (∫ ω in D, Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
      (∫ ω in A, Problem520.harperEulerDensity y ω t ∂Problem520.μ) +
      (∫ ω in B, Problem520.harperEulerDensity y ω t ∂Problem520.μ) := by
  have hi := Problem520.integrable_harperEulerDensity y t
  rw [← integral_indicator hD, ← integral_indicator hA, ← integral_indicator hB,
    ← integral_add (hi.indicator hA) (hi.indicator hB)]
  apply integral_mono (hi.indicator hD) ((hi.indicator hA).add (hi.indicator hB))
  intro ω
  have hn := Problem520.harperEulerDensity_nonneg y ω t
  by_cases hωD : ω ∈ D <;> by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;>
    simp [hωD, hωA, hωB, hn]
  exact False.elim (by simpa [hωA, hωB] using hsub hωD)

/-- The common-event integrated deletion estimate now permits the full
terminal prefix `j=N`. Interior cutoffs use the established suffix bound;
the full cutoff pays its actual terminal strip bound. This is the screen
needed when microscopic gaps remove the entire finite Euler product. -/
theorem candidate_exists_covarianceCommonFrequencyDeletion_terminal_integral_le :
    ∃ C ≥ 0, ∃ D ≥ 0, ∃ J : ℕ, ∀ d start M : ℕ, J + d ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start →
      ∀ N a : ℕ, 3 ≤ N → 3 ≤ a → ∀ s : Finset ℕ,
      (∀ j ∈ s, a ≤ j ∧ j ≤ N) → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + N) ≤ y →
      ∀ W : ℝ, 1 ≤ W →
      (∫ ω, candidateEulerFrequencyMass y (candidateCovarianceFrequencyWindow d M)
        (candidateCovarianceCommonFrequencyDeletionGraph start N M W s) ω ∂Problem520.μ) ≤
      2 * Real.pi * Problem520.primeEnergyNormalizer y *
        (candidateCovarianceFrequencyDeletionBudget C W start N a (s.erase N) +
          candidateCovarianceTerminalDeletionBudget D W start N) := by
  classical
  obtain ⟨C, hC, Ji, hI⟩ := candidate_exists_covarianceFrequencyDeletion_section_le
  obtain ⟨D, hD, Jt, hT⟩ := candidate_exists_DStar_terminal_frequency_section_le
  refine ⟨C, hC, D, hD, max Ji Jt, ?_⟩
  intro d start M hstart hM N a hN ha s hs y hy W hW
  have hs' (j : ℕ) (hj : j ∈ s.erase N) : a ≤ j ∧ j < N := by
    have hjN := (Finset.mem_erase.mp hj).1
    have hjS := hs j (Finset.mem_erase.mp hj).2
    exact ⟨hjS.1, by omega⟩
  have hsection (t : ℝ) (ht : t ∈ candidateCovarianceFrequencyWindow d M) :
      (∫ ω in {ω | (t, ω) ∈ candidateCovarianceCommonFrequencyDeletionGraph start N M W s},
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
      Problem520.primeEnergyNormalizer y *
        (candidateCovarianceFrequencyDeletionBudget C W start N a (s.erase N) +
          candidateCovarianceTerminalDeletionBudget D W start N) := by
    have hp : Measurable (fun ω : Problem520.Omega => (t, ω)) :=
      measurable_const.prodMk measurable_id
    have hm := (candidate_measurableSet_covarianceCommonFrequencyDeletion start N M W s).preimage hp
    have hi := (candidate_measurableSet_covarianceFrequencyDeletion start N W (s.erase N)).preimage hp
    have hd := (candidate_measurableSet_covarianceDStar_joint start N W).preimage hp
    have hn := (candidate_measurableSet_covarianceStrongScreen_joint start W {N}).preimage hp
    have hsub : {ω | (t, ω) ∈ candidateCovarianceCommonFrequencyDeletionGraph start N M W s} ⊆
        {ω | (t, ω) ∈ candidateCovarianceFrequencyDeletionGraph start N W (s.erase N)} ∪
          (candidateCovarianceDStarEvent start N t W \ candidateCovarianceStrongScreenEvent start t W {N}) := by
      intro ω hω
      have hmesh := candidate_covarianceCommonMesh_subset start N M W t ht.2 hω.1
      by_cases hret : ω ∈ candidateCovarianceDStarEvent start N t W ∩
          candidateCovarianceStrongScreenEvent start t W (s.erase N)
      · right
        refine ⟨hret.1, ?_⟩
        intro hterminal
        apply hω.2
        refine ⟨hret.1, ?_⟩
        intro j hj
        by_cases hjN : j = N
        · subst j
          exact hterminal N (Finset.mem_singleton_self N)
        · exact hret.2 j (Finset.mem_erase.mpr ⟨hjN, hj⟩)
      · exact Or.inl ⟨hmesh, hret⟩
    have hb := setIntegral_le_add_of_subset_union y t hm hi (hd.diff hn) hsub
    have hiB := hI d start M (by omega) hM N a ha (s.erase N) hs' y hy W hW t ht
    have htB := hT d start M (by omega) hM N hN y hy W hW t ht
    have h := hb.trans (add_le_add hiB htB)
    convert h using 1 <;> ring
  have h := candidate_integral_eulerFrequencyMass_le y
    (candidate_measurableSet_covarianceFrequencyWindow d M)
    (candidate_measurableSet_covarianceCommonFrequencyDeletion start N M W s)
    (mul_nonneg (Problem520.primeEnergyNormalizer_pos y).le
      (add_nonneg (candidate_covarianceFrequencyDeletionBudget_nonneg hC hW start N a (s.erase N))
        (candidate_covarianceTerminalDeletionBudget_nonneg hD hW start N))) hsection
  convert h using 1 <;> ring

end Erdos.Problem1144
