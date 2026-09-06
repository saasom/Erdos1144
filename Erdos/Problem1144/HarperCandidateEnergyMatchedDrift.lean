import Erdos.Problem1144.HarperCandidateEnergyRegressionBallot
import Erdos.Problem1144.HarperCandidateEnergyTwoHeightDrifted

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos.Problem1144

/-! Actual shifted centering drifts, uniformly summable from natural coherence. -/

theorem candidate_exists_rankinRelativeDrift_geometric_half :
    ∃ J : Nat, ∀ shell baseStart d m y : Nat,
      J ≤ baseStart → shell + 1 ≤ d →
      Problem520.harperBlockEndpoint (baseStart + d + m) ≤ y →
        ∀ σ : ℝ, ∀ hσ : 0 ≤ σ, ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ i : Fin m,
                |harperRankinTwoHeightCenteredBlockDrift y
                    (Problem520.harperScheduledPrimeBlock y
                      (baseStart + d + i.val)) σ t s t| ≤
                    (1 / 2 : Real) * (1 / 2 : Real) ^ i.val ∧
                  |harperRankinTwoHeightCenteredBlockDrift y
                    (Problem520.harperScheduledPrimeBlock y
                      (baseStart + d + i.val)) σ s t s| ≤
                    (1 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
  obtain ⟨c, hc, C, hC, Jcov, hcov⟩ :=
    candidate_exists_rankinScheduledCovariance_postCoherence_geometric
  obtain ⟨c', hc', C', hC', Jerr, herr⟩ :=
    Problem520.exists_harperScheduledSummableBlockErrorBounds 1
  obtain ⟨Jtheta, htheta⟩ := Filter.eventually_atTop.1
    (eventually_harperScheduledThetaEnvelope_le_geometric hc hC.le)
  let K : Real := 395 + 7 * C
  let A : Real := 864 + 2 * K
  have hK : 0 < K := by
    dsimp only [K]
    nlinarith
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hhalfTendsto : Tendsto (fun j : Nat ↦ (1 / 2 : Real) ^ j)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hscaleTendsto : Tendsto
      (fun j : Nat ↦ A * (1 / 2 : Real) ^ j) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hhalfTendsto
  have hscaleEventually : ∀ᶠ j : Nat in atTop,
      A * (1 / 2 : Real) ^ j ≤ (1 / 2 : Real) := by
    filter_upwards
      [(tendsto_order.mp hscaleTendsto).2 (1 / 2 : Real) (by norm_num)]
      with j hj
    exact hj.le
  obtain ⟨Jscale, hscale⟩ := Filter.eventually_atTop.1 hscaleEventually
  let J := max Jcov (max Jerr (max Jtheta Jscale))
  refine ⟨J, ?_⟩
  intro shell baseStart d m y hstart hd hy σ hσ t ht s hs hsep i
  let j := baseStart + d + i.val
  have hjEnd : j + 1 ≤ baseStart + d + m := by
    dsimp only [j]
    omega
  have hyj : Problem520.harperBlockEndpoint (j + 1) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint hjEnd).trans hy
  have hJcov : Jcov + (shell + 1) ≤ j := by
    dsimp only [j, J] at hstart ⊢
    have : Jcov ≤ max Jcov (max Jerr (max Jtheta Jscale)) :=
      le_max_left _ _
    omega
  have hJerr : Jerr ≤ j := by
    dsimp only [j, J] at hstart ⊢
    have : Jerr ≤ max Jcov (max Jerr (max Jtheta Jscale)) :=
      (le_max_left Jerr _).trans (le_max_right Jcov _)
    omega
  have hJtheta : Jtheta ≤ j := by
    dsimp only [j, J] at hstart ⊢
    have : Jtheta ≤ max Jcov (max Jerr (max Jtheta Jscale)) :=
      ((le_max_left Jtheta Jscale).trans (le_max_right Jerr _)).trans
        (le_max_right Jcov _)
    omega
  have hJscale : Jscale ≤ baseStart := by
    dsimp only [J] at hstart
    have : Jscale ≤ max Jcov (max Jerr (max Jtheta Jscale)) :=
      ((le_max_right Jtheta Jscale).trans (le_max_right Jerr _)).trans
        (le_max_right Jcov _)
    exact this.trans hstart
  have hscaleBase := hscale baseStart hJscale
  have hthetaJ := htheta j hJtheta
  have hsquareMass : Problem520.harperScheduledSquareMass y j ≤
      Problem520.harperScheduledSquareEnvelope j :=
    (herr j hJerr y hyj).2.2
  have hpDiff :
      (1 / 2 : Real) ^ (j - (shell + 1)) ≤
        (1 / 2 : Real) ^ (baseStart + i.val) := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    dsimp only [j]
    omega
  have hpSum :
      (1 / 2 : Real) ^ (j - 1) ≤
        (1 / 2 : Real) ^ (baseStart + i.val) := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    dsimp only [j]
    omega
  have hpJ :
      (1 / 2 : Real) ^ j ≤
        (1 / 2 : Real) ^ (baseStart + i.val) := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    dsimp only [j]
    omega
  have hthetaI : Problem520.harperScheduledThetaEnvelope c C j ≤
      (C + 1) * (1 / 2 : Real) ^ (baseStart + i.val) := by
    exact hthetaJ.trans (mul_le_mul_of_nonneg_left hpJ (by linarith))
  have hsquareI : Problem520.harperScheduledSquareMass y j ≤
      (3 / 2 : Real) * (1 / 2 : Real) ^ (baseStart + i.val) := by
    calc
      Problem520.harperScheduledSquareMass y j ≤
          Problem520.harperScheduledSquareEnvelope j := hsquareMass
      _ ≤ (3 / 2 : Real) * (1 / 2 : Real) ^ j :=
        harperScheduledSquareEnvelope_le_threeHalves_geometric j
      _ ≤ (3 / 2 : Real) *
          (1 / 2 : Real) ^ (baseStart + i.val) := by gcongr
  have hone (a b : Real) (haBand : a ∈ harperLowerVerticalBand)
      (hbBand : b ∈ harperLowerVerticalBand)
      (hsepAB : (1 / 2 : Real) ^ (shell + 1) < |a - b|) :
      |harperRankinTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y j) σ a b a| ≤
        (1 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
    have hcovj := hcov shell j y hJcov hyj σ hσ a haBand b hbBand hsepAB
    have hq :
        |harperRankinTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y j) σ hσ a b a b| ≤
          K * (1 / 2 : Real) ^ (baseStart + i.val) := by
      calc
        |harperRankinTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y j) σ hσ a b a b| ≤
          2 * (1 / 2 : Real) ^ (j - (shell + 1)) +
            2 * (1 / 2 : Real) ^ (j - 1) +
            7 * Problem520.harperScheduledThetaEnvelope c C j +
            256 * Problem520.harperScheduledSquareMass y j := hcovj
        _ ≤ 2 * (1 / 2 : Real) ^ (baseStart + i.val) +
            2 * (1 / 2 : Real) ^ (baseStart + i.val) +
            7 * ((C + 1) *
              (1 / 2 : Real) ^ (baseStart + i.val)) +
            256 * ((3 / 2 : Real) *
              (1 / 2 : Real) ^ (baseStart + i.val)) := by gcongr
        _ = K * (1 / 2 : Real) ^ (baseStart + i.val) := by
          dsimp only [K]
          ring
    have hcompare :=
      candidate_rankinTwoHeightScheduledDrift_sub_two_covariance_le
        y j hσ a b
    have htri :
        |harperRankinTwoHeightCenteredBlockDrift y
            (Problem520.harperScheduledPrimeBlock y j) σ a b a| ≤
          576 * Problem520.harperScheduledSquareMass y j +
            2 * |harperRankinTwoHeightBlockCoordinateCovariance y
              (Problem520.harperScheduledPrimeBlock y j) σ hσ a b a b| := by
      calc
        |harperRankinTwoHeightCenteredBlockDrift y
            (Problem520.harperScheduledPrimeBlock y j) σ a b a| =
          |(harperRankinTwoHeightCenteredBlockDrift y
              (Problem520.harperScheduledPrimeBlock y j) σ a b a -
                2 * harperRankinTwoHeightBlockCoordinateCovariance y
                  (Problem520.harperScheduledPrimeBlock y j) σ hσ a b a b) +
              2 * harperRankinTwoHeightBlockCoordinateCovariance y
                (Problem520.harperScheduledPrimeBlock y j) σ hσ a b a b| := by
            congr 1
            ring
        _ ≤
          |harperRankinTwoHeightCenteredBlockDrift y
              (Problem520.harperScheduledPrimeBlock y j) σ a b a -
                2 * harperRankinTwoHeightBlockCoordinateCovariance y
                  (Problem520.harperScheduledPrimeBlock y j) σ hσ a b a b| +
            |2 * harperRankinTwoHeightBlockCoordinateCovariance y
              (Problem520.harperScheduledPrimeBlock y j) σ hσ a b a b| :=
          abs_add_le _ _
        _ ≤ 576 * Problem520.harperScheduledSquareMass y j +
            2 * |harperRankinTwoHeightBlockCoordinateCovariance y
              (Problem520.harperScheduledPrimeBlock y j) σ hσ a b a b| := by
          gcongr
          rw [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
    calc
      |harperRankinTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y j) σ a b a| ≤
        576 * Problem520.harperScheduledSquareMass y j +
          2 * |harperRankinTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y j) σ hσ a b a b| := htri
      _ ≤ A * (1 / 2 : Real) ^ (baseStart + i.val) := by
        calc
          576 * Problem520.harperScheduledSquareMass y j +
              2 * |harperRankinTwoHeightBlockCoordinateCovariance y
                (Problem520.harperScheduledPrimeBlock y j) σ hσ a b a b| ≤
            576 * ((3 / 2 : Real) *
                (1 / 2 : Real) ^ (baseStart + i.val)) +
              2 * (K *
                (1 / 2 : Real) ^ (baseStart + i.val)) := by gcongr
          _ = A * (1 / 2 : Real) ^ (baseStart + i.val) := by
            dsimp only [A]
            ring
      _ = (A * (1 / 2 : Real) ^ baseStart) *
          (1 / 2 : Real) ^ i.val := by rw [pow_add]; ring
      _ ≤ (1 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
        exact mul_le_mul_of_nonneg_right hscaleBase (by positivity)
  constructor
  · exact hone t s ht hs hsep
  · have hsepSwap :
        (1 / 2 : Real) ^ (shell + 1) < |s - t| := by
      simpa only [abs_sub_comm] using hsep
    have hraw := hone s t hs ht hsepSwap
    exact hraw

/-- Pointwise geometric drift decay gives a uniform one-unit bound for every
cumulative suffix drift. -/
theorem candidate_cumulative_rankinRelativeDrift_le_one
    {baseStart d m y : Nat} {σ t s : Real}
    (hpoint : ∀ i : Fin m,
      |harperRankinTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) σ t s t| ≤
          (1 / 2 : Real) * (1 / 2 : Real) ^ i.val ∧
        |harperRankinTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) σ s t s| ≤
          (1 / 2 : Real) * (1 / 2 : Real) ^ i.val) :
    ∀ k : Fin m,
      |∑ i ∈ Finset.Iic k,
        (candidateRankinTwoHeightBallotBlockDrift y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) σ t s).1| ≤ 1 ∧
      |∑ i ∈ Finset.Iic k,
        (candidateRankinTwoHeightBallotBlockDrift y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) σ t s).2| ≤ 1 := by
  intro k
  have hsum :
      (∑ i ∈ Finset.Iic k,
          (1 / 2 : Real) * (1 / 2 : Real) ^ i.val) ≤ 1 := by
    calc
      (∑ i ∈ Finset.Iic k,
          (1 / 2 : Real) * (1 / 2 : Real) ^ i.val) ≤
        ∑ i : Fin m, (1 / 2 : Real) * (1 / 2 : Real) ^ i.val :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (by intro i hi hnot; positivity)
      _ = (1 / 2 : Real) *
          ∑ i : Fin m, (1 / 2 : Real) ^ (0 + i.val) := by
        simp only [zero_add]
        rw [Finset.mul_sum]
      _ ≤ (1 / 2 : Real) * (2 * (1 / 2 : Real) ^ 0) := by
        exact mul_le_mul_of_nonneg_left
          (sum_fin_half_pow_shift_le 0 m) (by norm_num)
      _ = 1 := by norm_num
  constructor
  · calc
      |∑ i ∈ Finset.Iic k,
          (candidateRankinTwoHeightBallotBlockDrift y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) σ t s).1| ≤
        ∑ i ∈ Finset.Iic k,
          |(candidateRankinTwoHeightBallotBlockDrift y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) σ t s).1| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Iic k,
          (1 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
        gcongr with i hi
        exact (hpoint i).1
      _ ≤ 1 := hsum
  · calc
      |∑ i ∈ Finset.Iic k,
          (candidateRankinTwoHeightBallotBlockDrift y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) σ t s).2| ≤
        ∑ i ∈ Finset.Iic k,
          |(candidateRankinTwoHeightBallotBlockDrift y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) σ t s).2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Iic k,
          (1 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
        gcongr with i hi
        exact (hpoint i).2
      _ ≤ 1 := hsum


end Erdos.Problem1144
