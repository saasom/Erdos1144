import Erdos.Problem1144.HarperCandidateCovarianceResonanceGapIntegralEnvelope

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144

/-- The actual ordered, screened Euler-product integral has an explicit
resonance-cell bound. The small-gap alternative pays the strong-screen
saving, and the other alternative pays the original cell width. All
expectations, gap masses, and changes of variables have been discharged. -/
theorem candidate_exists_ordered_screened_euler_resonance_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ n start stop a : ℕ, J ≤ start → start < a → a ≤ stop → 1 ≤ n →
    ∀ W : ℝ, 1 ≤ W → ∀ M : ℝ, 0 ≤ M →
      M ≤ candidateCovarianceHeightWindow start / 2 →
    ∀ σ : Fin (n + 1) → ℤ, (∀ i, σ i = 1 ∨ σ i = -1) →
    ∀ k : ℕ, 2 * k ≤ n + 1 → ∀ ε : ℝ, 0 ≤ ε → ∀ m : ℤ,
    let Y := Problem520.harperBlockEndpoint stop
    let A := Real.log (Problem520.harperBlockEndpoint start : ℝ)
    let L := Real.log (Y : ℝ)
    let δ := Problem520.invLog (Problem520.harperBlockEndpoint (a - 1))
    let U := A * M + 3 * Real.log (1 + L * M)
    (∫ ω, (∫ t in candidateCovarianceHeightCell start (stop - start) W M
          (Finset.Icc (a - start) (stop - start)) ω σ (m : ℝ) ε ∩
          candidateCovarianceOrderedPositiveHeights (n + 1),
        ∏ i, candidateEulerBandSquaredWeight Y ω (t i)) ∂Problem520.μ) ≤
      ((4 : ℝ) ^ (n + 1) * candidateCovarianceGapMomentFactor C D start (n + 1) *
        L ^ (n + 1) / Real.log 3) *
      (W ^ (12 * n) * M *
        (U ^ n / W ^ (2012 * k) + 2 * ε * n * (A + 2 / δ) * U ^ (n - 1))) := by
  obtain ⟨C, D, hC, hD, J, hordered⟩ :=
    candidate_exists_ordered_screened_euler_le_gap_integral
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro n start stop a hstart hsa has hn W hW M hM hwindow σ hσ k hk ε hε m
  have hfirst := hordered n start stop a hstart hsa has W hW M hwindow σ (m : ℝ) ε
  have hgap := candidate_integral_screenedGapBox_resonance_le
    start stop a hn σ hσ k hk hM hε hW m
  dsimp only at hfirst hgap ⊢
  have hL : 0 ≤ Real.log (Problem520.harperBlockEndpoint stop : ℝ) :=
    (Problem520.one_le_log_harperBlockEndpoint stop).trans' (by norm_num)
  exact hfirst.trans (mul_le_mul_of_nonneg_left hgap
    (div_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (candidate_gapMomentFactor_nonneg C D start _)) (pow_nonneg hL _)) (by positivity)))

end Erdos.Problem1144
