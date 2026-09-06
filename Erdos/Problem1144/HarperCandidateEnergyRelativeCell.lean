import Erdos.Problem1144.HarperCandidateEnergyMatchedRectangle

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos.Problem1144

/-- Relative matched-Gaussian cells at the natural coherence scale, with
a terminal radial gap and an absolute start independent of path length. -/
theorem candidate_exists_gap_rankinRelativeRectangleProbability_le
    : ∃ J : Nat, ∀ V : ℝ, 0 ≤ V → ∃ gap : Nat, ∀ shell j y : Nat, J + (shell + 1) ≤ j →
      Problem520.harperBlockEndpoint (j + gap + 1) ≤ y →
        ∀ hσ : 0 ≤ 4 * V / Real.log (y : ℝ), ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ a b : Real,
                |a| + |b| + 3 ≤
                    (1 / 16 : Real) *
                      Real.sqrt (((2 ^ j : Nat) : Real)) →
                  (1 - 2 / Real.sqrt
                      (Problem520.harperScheduledStrongComparisonFrequency j)) ^
                        (2 : Nat) *
                      (harperRankinTwoHeightPrimeBlockVectorLaw y
                        (Problem520.harperScheduledPrimeBlock y j) (4 * V / Real.log (y : ℝ)) hσ t s).real
                          (Ioc a
                              (a + Problem520.harperScheduledRelativeIntervalWidth j) ×ˢ
                            Ioc b
                              (b + Problem520.harperScheduledRelativeIntervalWidth j)) ≤
                    (1 + 2 * Problem520.harperScheduledRelativeIntervalWidth j) *
                      (candidateRankinMatchedGaussianLaw y
                        (Problem520.harperScheduledPrimeBlock y j) (4 * V / Real.log (y : ℝ)) hσ t s).real
                        (Ioc
                            (a - 2 *
                              (Real.sqrt
                                  (Problem520.harperScheduledStrongComparisonFrequency j) /
                                (Problem520.harperScheduledStrongComparisonFrequency j / 2)))
                            ((a + Problem520.harperScheduledRelativeIntervalWidth j) +
                              2 *
                                (Real.sqrt
                                    (Problem520.harperScheduledStrongComparisonFrequency j) /
                                  (Problem520.harperScheduledStrongComparisonFrequency j / 2))) ×ˢ
                          Ioc
                            (b - 2 *
                              (Real.sqrt
                                  (Problem520.harperScheduledStrongComparisonFrequency j) /
                                (Problem520.harperScheduledStrongComparisonFrequency j / 2)))
                            ((b + Problem520.harperScheduledRelativeIntervalWidth j) +
                              2 *
                                (Real.sqrt
                                    (Problem520.harperScheduledStrongComparisonFrequency j) /
                                  (Problem520.harperScheduledStrongComparisonFrequency j / 2)))) := by
  obtain ⟨Jtail, htail⟩ := Filter.eventually_atTop.1
    eventually_harperScheduledBivariateFejerTail_le_relativeGaussianMass
  obtain ⟨Jfourier, hfourier⟩ := Filter.eventually_atTop.1
    eventually_harperScheduledBivariateFourierError_le_fejerTail
  obtain ⟨Jparams, hparams⟩ := candidate_exists_gap_rankinMatchedGaussian_parameters
  let J := max 4 (max Jtail (max Jfourier Jparams))
  refine ⟨J, ?_⟩
  intro V hV
  obtain ⟨gap, hparams⟩ := hparams V hV
  refine ⟨gap, ?_⟩
  intro shell j y hj hy hσ t ht s hs hsep a b hmoderate
  have hjFour : 4 ≤ j := by dsimp only [J] at hj; omega
  have hjTail : Jtail ≤ j := by dsimp only [J] at hj; omega
  have hjFourier : Jfourier ≤ j := by dsimp only [J] at hj; omega
  have hjParams : Jparams + (shell + 1) ≤ j := by dsimp only [J] at hj; omega
  have hp := hparams shell j y hjParams hy hσ t ht s hs hsep
  dsimp only at hp
  let F : Real := Problem520.harperScheduledStrongComparisonFrequency j
  let T : Real := F / 2
  let r : Real := Real.sqrt F
  let delta : Real := Problem520.harperScheduledRelativeIntervalWidth j
  let lambda : Real := candidateRankinRegressionCoefficient y
    (Problem520.harperScheduledPrimeBlock y j) (4 * V / Real.log (y : ℝ)) hσ t s
  let nu : Measure (Real × Real) := candidateRankinMatchedGaussianLaw y
    (Problem520.harperScheduledPrimeBlock y j) (4 * V / Real.log (y : ℝ)) hσ t s
  have hFPos : 0 < F := by
    dsimp only [F]
    exact Problem520.harperScheduledStrongComparisonFrequency_pos j
  have hTPos : 0 < T := by dsimp only [T]; positivity
  have hrPos : 0 < r := by dsimp only [r]; exact Real.sqrt_pos.2 hFPos
  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    exact Problem520.harperScheduledRelativeIntervalWidth_pos j
  have hdeltaOne : delta ≤ 1 := by
    dsimp only [delta]
    exact Problem520.harperScheduledRelativeIntervalWidth_le_one j
  have hpow : (16 : Nat) ≤ 2 ^ j := by
    simpa only [show (16 : Nat) = 2 ^ 4 by norm_num] using
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hjFour
  have hFlarge : (65536 : Real) ≤ F := by
    dsimp only [F]
    calc
      (65536 : Real) = ((2 ^ 16 : Nat) : Real) := by norm_num
      _ ≤ ((2 ^ (2 ^ j) : Nat) : Real) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hpow
      _ = Problem520.harperScheduledStrongComparisonFrequency j := by
        simp only [Problem520.harperScheduledStrongComparisonFrequency,
          Nat.cast_pow, Nat.cast_ofNat]
  have hrTwo : 2 ≤ r := by
    dsimp only [r]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hfrequency :
      4 * T ≤ Real.sqrt (Problem520.harperBlockEndpoint j : Real) := by
    dsimp only [T, F]
    convert Problem520.harperScheduledStrongComparisonFrequency_condition j using 1 <;>
      ring
  have hlambda : |lambda| ≤ (3 / 8 : Real) := hp.2.2.2.2.2
  have htailBudget := htail j hjTail lambda a b hlambda hmoderate
  have hgaussLower := harperGaussianRegressionBlockLaw_rectangleMass_lower
    (candidateRankinTwoHeightCoordinateVarianceNNReal y (Problem520.harperScheduledPrimeBlock y j)
      (4 * V / Real.log (y : ℝ)) hσ t s t)
    (candidateRankinRegressionResidualVariance y (Problem520.harperScheduledPrimeBlock y j)
      (4 * V / Real.log (y : ℝ)) hσ t s)
    lambda a b delta hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hlambda hdeltaPos hdeltaOne
  have htailGauss :
      2 / r ≤ delta *
        nu.real (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) := by
    calc
      2 / r ≤ delta *
          ((delta ^ (2 : Nat) / 64) *
            Real.exp (-2 *
              ((|a| + 1) ^ (2 : Nat) +
                (|b - lambda * a + delta / 4| + 1) ^ (2 : Nat)))) := by
        simpa only [r, F, delta] using htailBudget
      _ ≤ delta * nu.real
          (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) := by
        exact mul_le_mul_of_nonneg_left hgaussLower hdeltaPos.le
  have hfourierTail :
      (2 * Real.pi)⁻¹ ^ (2 : Nat) *
            |((a + delta) + r / T) - (a - r / T)| *
            |((b + delta) + r / T) - (b - r / T)| *
            (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
              (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat)) ≤
          2 / r := by
    have hf := hfourier j hjFourier
    simpa only [F, T, r, delta,
      show ((a + Problem520.harperScheduledRelativeIntervalWidth j) +
          Real.sqrt (Problem520.harperScheduledStrongComparisonFrequency j) /
            (Problem520.harperScheduledStrongComparisonFrequency j / 2)) -
          (a - Real.sqrt
            (Problem520.harperScheduledStrongComparisonFrequency j) /
              (Problem520.harperScheduledStrongComparisonFrequency j / 2)) =
        Problem520.harperScheduledRelativeIntervalWidth j +
          2 * (Real.sqrt
            (Problem520.harperScheduledStrongComparisonFrequency j) /
              (Problem520.harperScheduledStrongComparisonFrequency j / 2)) by ring,
      show ((b + Problem520.harperScheduledRelativeIntervalWidth j) +
          Real.sqrt (Problem520.harperScheduledStrongComparisonFrequency j) /
            (Problem520.harperScheduledStrongComparisonFrequency j / 2)) -
          (b - Real.sqrt
            (Problem520.harperScheduledStrongComparisonFrequency j) /
              (Problem520.harperScheduledStrongComparisonFrequency j / 2)) =
        Problem520.harperScheduledRelativeIntervalWidth j +
          2 * (Real.sqrt
            (Problem520.harperScheduledStrongComparisonFrequency j) /
              (Problem520.harperScheduledStrongComparisonFrequency j / 2)) by ring,
      pow_two, mul_assoc] using hf
  have hraw := candidate_rankinScheduledRectangleMass_le_matched_explicit
    y j (4 * V / Real.log (y : ℝ)) hσ t s T r
      (a := a) (b := a + delta) (c := b) (d := b + delta)
      (by linarith) (by linarith) hTPos hrTwo hfrequency hp.1
  let expanded : Set (Real × Real) :=
    Ioc (a - 2 * (r / T)) ((a + delta) + 2 * (r / T)) ×ˢ
      Ioc (b - 2 * (r / T)) ((b + delta) + 2 * (r / T))
  have hsubset :
      Ioc a (a + delta) ×ˢ Ioc b (b + delta) ⊆ expanded := by
    intro z hz
    have hexpand : 0 ≤ 2 * (r / T) := by positivity
    constructor <;> constructor <;> dsimp only [expanded] <;>
      linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  have hmono :
      nu.real (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) ≤
        nu.real expanded := measureReal_mono hsubset
  have hfourierGauss :
      (2 * Real.pi)⁻¹ ^ (2 : Nat) *
            |((a + delta) + r / T) - (a - r / T)| *
            |((b + delta) + r / T) - (b - r / T)| *
            (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
              (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat)) ≤
          delta * nu.real (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) :=
    hfourierTail.trans htailGauss
  change (1 - 2 / r) ^ (2 : Nat) *
      (harperRankinTwoHeightPrimeBlockVectorLaw y
        (Problem520.harperScheduledPrimeBlock y j) (4 * V / Real.log (y : ℝ)) hσ t s).real
          (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) ≤
    (1 + 2 * delta) * nu.real expanded
  calc
    _ ≤ nu.real expanded + 2 / r +
        (2 * Real.pi)⁻¹ ^ (2 : Nat) *
          |((a + delta) + r / T) - (a - r / T)| *
          |((b + delta) + r / T) - (b - r / T)| *
          (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
            (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat)) := by
      simpa only [nu, expanded, mul_assoc] using hraw
    _ ≤ nu.real expanded +
          delta * nu.real (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) +
          delta * nu.real (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) := by
      gcongr
    _ ≤ (1 + 2 * delta) * nu.real expanded := by
      nlinarith [hmono, (measureReal_nonneg : 0 ≤ nu.real expanded),
        hdeltaPos.le]

end Erdos.Problem1144
