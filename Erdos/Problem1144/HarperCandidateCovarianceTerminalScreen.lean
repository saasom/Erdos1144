import Erdos.Problem1144.HarperCandidateCovarianceTerminalEuler
import Erdos.Problem1144.HarperCandidateCovarianceScreen

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

noncomputable section

/-- The paid terminal strong-screen error. The path has length `N` and no
surviving suffix; its terminal strip gives the inverse-three-halves factor. -/
def candidateCovarianceTerminalDeletionBudget (C W : ℝ) (start N : ℕ) : ℝ :=
  candidateEulerTerminalDeletionPrefactor C
    (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 7 * Real.log W)
    (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 1013 * Real.log W) /
      (Real.sqrt ((N / 3 : ℕ) : ℝ)) ^ 3 + 64 * (1 / 2 : ℝ) ^ start

theorem candidate_covarianceTerminalDeletionBudget_nonneg {C W : ℝ}
    (hC : 0 ≤ C) (hW : 1 ≤ W) (start N : ℕ) :
    0 ≤ candidateCovarianceTerminalDeletionBudget C W start N := by
  have hlogW := Real.log_nonneg hW
  have hlogB := Real.log_nonneg (Problem520.one_le_log_harperBlockEndpoint start)
  unfold candidateCovarianceTerminalDeletionBudget
  exact add_nonneg (div_nonneg
    (candidate_eulerTerminalDeletionPrefactor_nonneg hC (by positivity) (by positivity))
    (by positivity)) (by positivity)

theorem candidate_covarianceTerminalDeletionBudget_mono {C D W : ℝ}
    (hC : 0 ≤ C) (hCD : C ≤ D) (hW : 1 ≤ W) (start N : ℕ) :
    candidateCovarianceTerminalDeletionBudget C W start N ≤
      candidateCovarianceTerminalDeletionBudget D W start N := by
  have hlogW := Real.log_nonneg hW
  have hlogB := Real.log_nonneg (Problem520.one_le_log_harperBlockEndpoint start)
  unfold candidateCovarianceTerminalDeletionBudget
  exact add_le_add (div_le_div_of_nonneg_right
    (candidate_eulerTerminalDeletionPrefactor_mono hC hCD (by positivity) (by positivity))
    (by positivity)) (le_refl _)

private theorem terminal_screen_mass_le_probability
    (y start N : ℕ) (hy : Problem520.harperBlockEndpoint (start + N) ≤ y)
    (t W : ℝ) (hW : 1 ≤ W) :
    (∫ ω in candidateCovarianceDStarEvent start N t W \
      candidateCovarianceStrongScreenEvent start t W {N},
      Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
    Problem520.primeEnergyNormalizer y * (Problem520.harperTiltedCubeLaw y t).real
      (candidateEulerInternalBarrierEvent y start N N t
        (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 7 * Real.log W)
        (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 1013 * Real.log W)) := by
  have hsub := candidate_covariance_DStar_deletion_subset_full start N t W hW {N}
  have hfirst := setIntegral_mono_set (Problem520.integrable_harperEulerDensity y t).integrableOn
    (ae_of_all _ fun ω => Problem520.harperEulerDensity_nonneg y ω t) (ae_of_all _ hsub)
  have hsecond := candidate_fullEuler_deletion_mass_le_range y start N hy t
    (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 6 * Real.log W)
    (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) - 1000 * Real.log W)
    (-Real.log W)
    (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 6 * Real.log W)
    {N} (by simp)
  have h : (∫ ω in candidateCovarianceDStarEvent start N t W \
      candidateCovarianceStrongScreenEvent start t W {N},
      Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
      ∫ ω in Problem520.harperPrimeRestriction y ⁻¹'
        candidateEulerInternalBarrierEvent y start N N t
          (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 7 * Real.log W)
          (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 1013 * Real.log W),
        Problem520.harperEulerDensity y ω t ∂Problem520.μ := by
    have heq (x r : ℝ) : candidateEulerStrongBarrierDeletionEvent y start N t x r {N} =
        candidateEulerInternalBarrierEvent y start N N t x r := by
      ext η
      simp [candidateEulerStrongBarrierDeletionEvent, candidateEulerInternalBarrierEvent]
    simp_rw [heq] at hsecond
    convert hfirst.trans hsecond using 1 <;> congr 2 <;> ring
  apply h.trans_eq
  have hdensity : (fun ω => Problem520.harperEulerDensity y ω t) =
      fun ω => Problem520.primeEnergyNormalizer y * Problem520.normalizedHarperEulerDensity y ω t := by
    funext ω
    unfold Problem520.normalizedHarperEulerDensity
    exact (mul_div_cancel₀ _ (Problem520.primeEnergyNormalizer_pos y).ne').symm
  rw [hdensity, integral_const_mul, ← Problem520.harperTiltedCubeLaw_real_apply_eq_omega]

/-- Literal weighted deletion at the full terminal prefix, uniformly on
the quantitative growing frequency window. It permits the exact Euler
cutoff `y = B_(start+N)`. -/
theorem candidate_exists_growingHeight_DStar_terminal_deletion_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ start M : ℕ, J ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start → ∀ N : ℕ, 3 ≤ N →
      ∀ y : ℕ, Problem520.harperBlockEndpoint (start + N) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ W : ℝ, 1 ≤ W →
      (∫ ω in candidateCovarianceDStarEvent start N t W \
        candidateCovarianceStrongScreenEvent start t W {N},
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
      Problem520.primeEnergyNormalizer y * candidateCovarianceTerminalDeletionBudget C W start N := by
  obtain ⟨C, hC, J, hJ⟩ := candidate_exists_growingHeight_euler_terminalBarrier_probability_le
  refine ⟨C, hC, J, ?_⟩
  intro start M hstart hM N hN y hy t htlo hthi W hW
  have hlogW := Real.log_nonneg hW
  have hlogB := Real.log_nonneg (Problem520.one_le_log_harperBlockEndpoint start)
  exact (terminal_screen_mass_le_probability y start N hy t W hW).trans
    (mul_le_mul_of_nonneg_left
      (hJ start M hstart hM N hN y hy t htlo hthi _ _ (by positivity) (by positivity))
      (Problem520.primeEnergyNormalizer_pos y).le)

/-- The same paid terminal prefix on every shrinking central band, with
an absolute starting threshold plus the explicit band depth. -/
theorem candidate_exists_centralBand_DStar_terminal_deletion_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start →
      ∀ N : ℕ, 3 ≤ N → ∀ y : ℕ, Problem520.harperBlockEndpoint (start + N) ≤ y →
      ∀ t : ℝ, (1 / 2 : ℝ) ^ (d + 1) < |t| → |t| ≤ (1 / 2 : ℝ) ^ d →
      ∀ W : ℝ, 1 ≤ W →
      (∫ ω in candidateCovarianceDStarEvent start N t W \
        candidateCovarianceStrongScreenEvent start t W {N},
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
      Problem520.primeEnergyNormalizer y * candidateCovarianceTerminalDeletionBudget C W start N := by
  obtain ⟨C, hC, J, hJ⟩ := candidate_exists_centralBand_euler_terminalBarrier_probability_le
  refine ⟨C, hC, J, ?_⟩
  intro d start hstart N hN y hy t htlo hthi W hW
  have hlogW := Real.log_nonneg hW
  have hlogB := Real.log_nonneg (Problem520.one_le_log_harperBlockEndpoint start)
  exact (terminal_screen_mass_le_probability y start N hy t W hW).trans
    (mul_le_mul_of_nonneg_left
      (hJ d start hstart N hN y hy t htlo hthi _ _ (by positivity) (by positivity))
      (Problem520.primeEnergyNormalizer_pos y).le)

end

end Erdos.Problem1144
