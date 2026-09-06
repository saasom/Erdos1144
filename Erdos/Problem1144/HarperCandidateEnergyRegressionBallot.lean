import Erdos.Problem1144.HarperCandidateEnergyRelativeSuffix
import Erdos.Problem1144.HarperGaussianSuffixBallot

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos.Problem1144

/-- Absolute geometric covariance envelope on every shifted suffix. -/
theorem candidate_exists_rankinScheduledCovariance_geometric_suffix :
    ∃ K > 0, ∃ J : ℕ, ∀ shell start m y : ℕ,
      J + (shell + 1) ≤ start →
      Problem520.harperBlockEndpoint (start + m) ≤ y →
        ∀ σ : ℝ, ∀ hσ : 0 ≤ σ, ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : ℝ) ^ (shell + 1) < |t - s| → ∀ i : Fin m,
              |harperRankinTwoHeightBlockCoordinateCovariance y
                (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s t s| ≤
                K * (1 / 2 : ℝ) ^ i.val := by
  obtain ⟨c, hc, C, hC, Jcov, hcov⟩ :=
    candidate_exists_rankinScheduledCovariance_postCoherence_geometric
  obtain ⟨c', hc', C', hC', Jerr, herr⟩ :=
    Problem520.exists_harperScheduledSummableBlockErrorBounds 1
  obtain ⟨Jtheta, htheta⟩ := Filter.eventually_atTop.1
    (eventually_harperScheduledThetaEnvelope_le_geometric hc hC.le)
  let K : ℝ := 395 + 7 * C
  refine ⟨K, by dsimp [K]; positivity, max Jcov (max Jerr Jtheta), ?_⟩
  intro shell start m y hstart hy σ hσ t ht s hs hsep i
  let j := start + i.val
  have hjEnd : j + 1 ≤ start + m := by dsimp [j]; omega
  have hyj : Problem520.harperBlockEndpoint (j + 1) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint hjEnd).trans hy
  have hjCov : Jcov + (shell + 1) ≤ j := by dsimp [j]; omega
  have hjErr : Jerr ≤ j := by dsimp [j]; omega
  have hjTheta : Jtheta ≤ j := by dsimp [j]; omega
  have hcovj := hcov shell j y hjCov hyj σ hσ t ht s hs hsep
  have hthetaJ := htheta j hjTheta
  have hsquareMass : Problem520.harperScheduledSquareMass y j ≤
      Problem520.harperScheduledSquareEnvelope j := (herr j hjErr y hyj).2.2
  have hpDiff :
      (1 / 2 : Real) ^ (j - (shell + 1)) ≤
        (1 / 2 : Real) ^ i.val := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    dsimp only [j]
    omega
  have hpSum :
      (1 / 2 : Real) ^ (j - 1) ≤
        (1 / 2 : Real) ^ i.val := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    dsimp only [j]
    omega
  have hpJ :
      (1 / 2 : Real) ^ j ≤ (1 / 2 : Real) ^ i.val := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    dsimp only [j]
    omega
  have hthetaI : Problem520.harperScheduledThetaEnvelope c C j ≤
      (C + 1) * (1 / 2 : Real) ^ i.val := by
    exact hthetaJ.trans (mul_le_mul_of_nonneg_left hpJ (by linarith))
  have hsquareI : Problem520.harperScheduledSquareMass y j ≤
      (3 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
    calc
      Problem520.harperScheduledSquareMass y j ≤
          Problem520.harperScheduledSquareEnvelope j := hsquareMass
      _ ≤ (3 / 2 : Real) * (1 / 2 : Real) ^ j :=
        harperScheduledSquareEnvelope_le_threeHalves_geometric j
      _ ≤ (3 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
        gcongr
  have hq :
      |harperRankinTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) σ hσ t s t s| ≤
        K * (1 / 2 : Real) ^ i.val := by
    calc
      |harperRankinTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) σ hσ t s t s| ≤
        2 * (1 / 2 : Real) ^ (j - (shell + 1)) +
          2 * (1 / 2 : Real) ^ (j - 1) +
          7 * Problem520.harperScheduledThetaEnvelope c C j +
          256 * Problem520.harperScheduledSquareMass y j := hcovj
      _ ≤ 2 * (1 / 2 : Real) ^ i.val +
          2 * (1 / 2 : Real) ^ i.val +
          7 * ((C + 1) * (1 / 2 : Real) ^ i.val) +
          256 * ((3 / 2 : Real) * (1 / 2 : Real) ^ i.val) := by
        gcongr
      _ = K * (1 / 2 : Real) ^ i.val := by
        dsimp only [K]
        ring
  exact hq

/-- Apply the generic regression ballot to the literal matched Gaussian laws. -/
theorem candidate_rankinMatchedGaussian_relaxedSuffixGuard_probability_le
    {d m y : ℕ} (hm : 0 < m)
    (S : Fin m → Finset (Problem520.HarperPrimeIndex y))
    (σ : ℝ) (hσ : 0 ≤ σ) (t s L : ℝ) (hL : 0 ≤ L)
    (hlambda : ∀ i, |candidateRankinRegressionCoefficient y (S i) σ hσ t s| ≤
      L * (1 / 2 : ℝ) ^ i.val)
    (hvarianceLower : ∀ i, (1 / 4 : ℝ) ≤
      (candidateRankinTwoHeightCoordinateVarianceNNReal y (S i) σ hσ t s t : ℝ))
    (hvarianceUpper : ∀ i,
      (candidateRankinTwoHeightCoordinateVarianceNNReal y (S i) σ hσ t s t : ℝ) ≤ 1 / 2)
    (hresidualLower : ∀ i, (1 / 4 : ℝ) ≤
      (candidateRankinRegressionResidualVariance y (S i) σ hσ t s : ℝ))
    (hresidualUpper : ∀ i,
      (candidateRankinRegressionResidualVariance y (S i) σ hσ t s : ℝ) ≤ 1 / 2) :
    (Measure.pi (fun i ↦ candidateRankinMatchedGaussianLaw y (S i) σ hσ t s)).real
      (harperPairedRelaxedSuffixGuardPathEvent d m) ≤
        (4096 * 68 * (536 * L + 68)) * ((d + 1 : ℕ) : ℝ)^2 * (m : ℝ)⁻¹ := by
  let variance : Fin m → ℝ≥0 := fun i ↦
    candidateRankinTwoHeightCoordinateVarianceNNReal y (S i) σ hσ t s t
  let residual : Fin m → ℝ≥0 := fun i ↦
    candidateRankinRegressionResidualVariance y (S i) σ hσ t s
  let lam : Fin m → ℝ := fun i ↦ candidateRankinRegressionCoefficient y (S i) σ hσ t s
  have hmap := map_harperPairPathZipCLM_regressedGaussian_eq_pi variance residual lam
  change (Measure.pi (fun i ↦ harperGaussianRegressionBlockLaw
    (variance i) (residual i) (lam i))).real _ ≤ _
  rw [← hmap, map_measureReal_apply (harperPairPathZipCLM m).measurable
    (measurableSet_harperPairedRelaxedSuffixGuardPathEvent d m)]
  exact harperRegressedGaussianTwoWalk_relaxedSuffixGuard_probability_le
    hm variance residual lam L hL hlambda
    (fun i ↦ by exact_mod_cast hvarianceLower i)
    (fun i ↦ by exact_mod_cast hvarianceUpper i)
    (fun i ↦ by exact_mod_cast hresidualLower i)
    (fun i ↦ by exact_mod_cast hresidualUpper i)

/-- The matched Gaussian suffix bound has absolute constants and no delay
past natural coherence beyond one fixed start. -/
theorem candidate_exists_gap_rankinMatchedGaussian_relaxedSuffixGuard_le :
    ∃ L > 0, ∃ J : ℕ, ∀ V : ℝ, 0 ≤ V → ∃ gap : ℕ,
      ∀ shell start d m y : ℕ, 0 < m → J + (shell + 1) ≤ start →
        Problem520.harperBlockEndpoint (start + m + gap) ≤ y →
          ∀ hσ : 0 ≤ 4 * V / Real.log (y : ℝ),
            ∀ t ∈ harperLowerVerticalBand, ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : ℝ) ^ (shell + 1) < |t - s| →
                (Measure.pi (fun i : Fin m ↦ candidateRankinMatchedGaussianLaw y
                  (Problem520.harperScheduledPrimeBlock y (start + i.val))
                  (4 * V / Real.log (y : ℝ)) hσ t s)).real
                  (harperPairedRelaxedSuffixGuardPathEvent d m) ≤
                    (4096 * 68 * (536 * L + 68)) * ((d + 1 : ℕ) : ℝ)^2 * (m : ℝ)⁻¹ := by
  obtain ⟨K, hK, Jcov, hcov⟩ := candidate_exists_rankinScheduledCovariance_geometric_suffix
  obtain ⟨Jparams, hparams⟩ := candidate_exists_gap_rankinMatchedGaussian_parameters
  refine ⟨4 * K, by positivity, max Jcov Jparams, ?_⟩
  intro V hV
  obtain ⟨gap, hparams⟩ := hparams V hV
  refine ⟨gap, ?_⟩
  intro shell start d m y hm hstart hy hσ t ht s hs hsep
  have hnear : Problem520.harperBlockEndpoint (start + m) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans hy
  have hq := hcov shell start m y (by omega) hnear _ hσ t ht s hs hsep
  have hp (i : Fin m) := hparams shell (start + i.val) y (by omega)
    ((Problem520.monotone_harperBlockEndpoint (by omega)).trans hy) hσ t ht s hs hsep
  dsimp only at hp
  apply candidate_rankinMatchedGaussian_relaxedSuffixGuard_probability_le
    hm (fun i ↦ Problem520.harperScheduledPrimeBlock y (start + i.val)) _ hσ t s
    (4 * K) (by positivity)
  · intro i
    unfold candidateRankinRegressionCoefficient
    rw [abs_div, abs_of_pos (hp i).1, div_le_iff₀ (hp i).1]
    have hAi := (hp i).2.1
    change (1 / 4 : ℝ) ≤ harperRankinTwoHeightBlockCoordinateCovariance y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) _ hσ t s t t at hAi
    have hscale : 0 ≤ K * (1 / 2 : ℝ)^i.val := by positivity
    nlinarith [hq i, mul_le_mul_of_nonneg_left hAi hscale]
  · exact fun i ↦ (hp i).2.1
  · exact fun i ↦ (hp i).2.2.1
  · exact fun i ↦ (hp i).2.2.2.1
  · exact fun i ↦ (hp i).2.2.2.2.1

end Erdos.Problem1144
