import Erdos.Problem1144.HarperCandidateEnergyTwoHeightCorridor

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

/-- The literal pair of one-height-centered shifted ballot increments. -/
noncomputable def candidateRankinTwoHeightBallotBlockVector
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t s : ℝ) (eta : Problem520.HarperPrimeCube y) : ℝ × ℝ :=
  (harperRankinCenteredLinearPrimeBlockSum y S a t t eta,
    harperRankinCenteredLinearPrimeBlockSum y S a s s eta)

/-- The two exact deterministic translations previously bounded after coherence. -/
noncomputable def candidateRankinTwoHeightBallotBlockDrift
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y)) (a t s : ℝ) : ℝ × ℝ :=
  (harperRankinTwoHeightCenteredBlockDrift y S a t s t,
    harperRankinTwoHeightCenteredBlockDrift y S a s t s)

private theorem candidate_rankinCenteredBlock_eq_fluctuation_add_drift
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t s u : ℝ) (eta : Problem520.HarperPrimeCube y) :
    harperRankinCenteredLinearPrimeBlockSum y S a t u eta =
      (∑ p ∈ S, harperRankinTwoHeightPrimeFluctuation p.1 a t s u (eta p)) +
        harperRankinTwoHeightCenteredBlockDrift y S a t s u := by
  unfold harperRankinCenteredLinearPrimeBlockSum harperRankinCenteredLinearPrimeIncrement
    harperRankinLinearPrimeIncrement harperRankinTwoHeightPrimeFluctuation
    harperRankinTwoHeightCenteredBlockDrift harperRankinTwoHeightCenteredPrimeDrift
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Exact centering identity for the actual shifted ballot pair. -/
theorem candidate_rankinTwoHeightBallotBlockVector_eq_translate
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t s : ℝ) (eta : Problem520.HarperPrimeCube y) :
    candidateRankinTwoHeightBallotBlockVector y S a t s eta =
      harperPairTranslate (candidateRankinTwoHeightBallotBlockDrift y S a t s)
        (harperRankinTwoHeightPrimeBlockVector y S a t s eta) := by
  apply Prod.ext
  · exact candidate_rankinCenteredBlock_eq_fluctuation_add_drift y S a t s t eta
  · have h := candidate_rankinCenteredBlock_eq_fluctuation_add_drift y S a s t s eta
    change harperRankinCenteredLinearPrimeBlockSum y S a s s eta =
      (∑ p ∈ S, harperRankinTwoHeightPrimeFluctuation p.1 a t s s (eta p)) +
        harperRankinTwoHeightCenteredBlockDrift y S a s t s
    rw [h]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    unfold harperRankinTwoHeightPrimeFluctuation
    rw [harperRankinTwoHeightTiltBias_comm p.1 a s t]

/-- The literal ballot block law under the joint tilt. -/
noncomputable def candidateRankinTwoHeightBallotBlockLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real) : Measure (Real × Real) :=
  Measure.map (candidateRankinTwoHeightBallotBlockVector y S σ t s)
    (harperRankinTwoHeightCubeLaw y σ hσ t s)

instance candidateRankinTwoHeightBallotBlockLaw_isProbabilityMeasure
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real) :
    IsProbabilityMeasure (candidateRankinTwoHeightBallotBlockLaw y S σ hσ t s) := by
  unfold candidateRankinTwoHeightBallotBlockLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_of_finite _).aemeasurable

/-- The comparison Gaussian translated by the exact ballot drift. -/
noncomputable def candidateRankinTwoHeightDriftedIndependentGaussianBlockLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real) : Measure (Real × Real) :=
  Measure.map
    (harperPairTranslate (candidateRankinTwoHeightBallotBlockDrift y S σ t s))
    (candidateRankinTwoHeightIndependentGaussianBlockLaw y S σ hσ t s)

instance candidateRankinTwoHeightDriftedIndependentGaussianBlockLaw_isProbabilityMeasure
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real) :
    IsProbabilityMeasure
      (candidateRankinTwoHeightDriftedIndependentGaussianBlockLaw y S σ hσ t s) := by
  unfold candidateRankinTwoHeightDriftedIndependentGaussianBlockLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_harperPairTranslate _).aemeasurable

theorem candidateRankinTwoHeightBallotBlockLaw_eq_translate
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real) :
    candidateRankinTwoHeightBallotBlockLaw y S σ hσ t s =
      Measure.map
        (harperPairTranslate (candidateRankinTwoHeightBallotBlockDrift y S σ t s))
        (harperRankinTwoHeightPrimeBlockVectorLaw y S σ hσ t s) := by
  unfold candidateRankinTwoHeightBallotBlockLaw harperRankinTwoHeightPrimeBlockVectorLaw
  rw [Measure.map_map (measurable_harperPairTranslate _)
    (measurable_of_finite _)]
  apply Measure.map_congr
  exact ae_of_all (harperRankinTwoHeightCubeLaw y σ hσ t s) fun eta ↦
    candidate_rankinTwoHeightBallotBlockVector_eq_translate y S σ t s eta


theorem candidate_rankinScheduledBallotClosedRectangleMass_le_drifted_cutoff
    (y j n : Nat) (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real) {a b c d : Real}
    (hn : 4 ≤ n)
    (hab : a ≤ b) (hcd : c ≤ d)
    (habWidth : b - a ≤ 65 * (n : Real) - 1)
    (hcdWidth : d - c ≤ 65 * (n : Real) - 1)
    (hfrequency :
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real))
    (hendpoint :
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real))
    (hcovariance :
      |harperRankinTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) σ hσ t s t s| ≤
        1 / (n : Real) ^ (40 : Nat)) :
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat) *
        (candidateRankinTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) σ hσ t s).real
            (Icc a b ×ˢ Icc c d) ≤
      (candidateRankinTwoHeightDriftedIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y j) σ hσ t s).real
          (Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
            Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (d + 4 * (1 / (n : Real) ^ (2 : Nat)))) +
        6 / (n : Real) ^ (4 : Nat) := by
  let S := Problem520.harperScheduledPrimeBlock y j
  let drift := candidateRankinTwoHeightBallotBlockDrift y S σ t s
  have hsource :
      (candidateRankinTwoHeightBallotBlockLaw y S σ hσ t s).real
          (Icc a b ×ˢ Icc c d) =
        (harperRankinTwoHeightPrimeBlockVectorLaw y S σ hσ t s).real
          (Icc (a - drift.1) (b - drift.1) ×ˢ
            Icc (c - drift.2) (d - drift.2)) := by
    rw [candidateRankinTwoHeightBallotBlockLaw_eq_translate,
      map_measureReal_apply (measurable_harperPairTranslate drift)
        (measurableSet_Icc.prod measurableSet_Icc),
      preimage_harperPairTranslate_prod_Icc]
  have htarget :
      (candidateRankinTwoHeightDriftedIndependentGaussianBlockLaw y S σ hσ t s).real
          (Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
            Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (d + 4 * (1 / (n : Real) ^ (2 : Nat)))) =
        (candidateRankinTwoHeightIndependentGaussianBlockLaw y S σ hσ t s).real
          (Icc ((a - drift.1) - 4 * (1 / (n : Real) ^ (2 : Nat)))
              ((b - drift.1) + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
            Icc ((c - drift.2) - 4 * (1 / (n : Real) ^ (2 : Nat)))
              ((d - drift.2) + 4 * (1 / (n : Real) ^ (2 : Nat)))) := by
    unfold candidateRankinTwoHeightDriftedIndependentGaussianBlockLaw
    rw [map_measureReal_apply (measurable_harperPairTranslate drift)
      (measurableSet_Icc.prod measurableSet_Icc),
      preimage_harperPairTranslate_prod_Icc]
    congr 1 <;> ring
  rw [show Problem520.harperScheduledPrimeBlock y j = S by rfl,
    hsource, htarget]
  apply
    candidate_rankinScheduledClosedRectangleMass_le_independent_cutoff
      y j n σ hσ t s hn
  · linarith
  · linarith
  · linarith
  · linarith
  · exact hfrequency
  · exact hendpoint
  · exact hcovariance

end Erdos.Problem1144
