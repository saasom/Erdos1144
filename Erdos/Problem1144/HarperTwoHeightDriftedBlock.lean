import Erdos.Problem1144.HarperTwoHeightClosedRectangle
import Erdos.Problem1144.HarperTwoHeightBlockIndependence

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Returning from joint centering to the two ballot coordinates

The characteristic-function comparison centers each block under the joint
two-height tilt.  The two ballot events instead use the one-height centering
at `t` and at `s` separately.  Their difference is a deterministic block
drift.  This file makes that translation exact and transfers the closed
rectangle comparison to the literal pair of ballot increments.
-/

/-- Drift from joint two-height centering to one-height centering at a
possibly different base height `q`, observed at height `u`. -/
noncomputable def harperTwoHeightRelativeBlockDrift
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s q u : Real) : Real :=
  ∑ p ∈ S,
    (harperTwoHeightTiltBias p.1 t s - Problem520.harperTiltBias p.1 q) *
      (Real.cos (u * Real.log (p.1 : Real)) /
        Real.sqrt (p.1 : Real))

/-- The pair of block increments used by the literal one-height-centered
ballot events at `t` and `s`. -/
noncomputable def harperTwoHeightBallotBlockVector
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) (eta : Problem520.HarperPrimeCube y) : Real × Real :=
  (Problem520.harperCenteredLinearPrimeBlockSum y S t t eta,
    Problem520.harperCenteredLinearPrimeBlockSum y S s s eta)

/-- The deterministic drift pair connecting joint-centered fluctuations to
the two literal ballot increments. -/
noncomputable def harperTwoHeightBallotBlockDrift
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) : Real × Real :=
  (harperTwoHeightRelativeBlockDrift y S t s t t,
    harperTwoHeightRelativeBlockDrift y S t s s s)

/-- Coordinatewise translation of a real pair. -/
def harperPairTranslate (d z : Real × Real) : Real × Real :=
  (z.1 + d.1, z.2 + d.2)

theorem measurable_harperPairTranslate (d : Real × Real) :
    Measurable (harperPairTranslate d) := by
  unfold harperPairTranslate
  fun_prop

/-- Scalar form of the exact centering translation. -/
theorem harperCenteredLinearPrimeBlockSum_eq_twoHeightFluctuation_add_drift
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s q u : Real) (eta : Problem520.HarperPrimeCube y) :
    Problem520.harperCenteredLinearPrimeBlockSum y S q u eta =
      (∑ p ∈ S, harperTwoHeightPrimeFluctuation p.1 t s u (eta p)) +
        harperTwoHeightRelativeBlockDrift y S t s q u := by
  unfold harperTwoHeightRelativeBlockDrift
    Problem520.harperCenteredLinearPrimeBlockSum
    Problem520.harperCenteredLinearPrimeIncrement
    Problem520.harperLinearPrimeIncrement
    harperTwoHeightPrimeFluctuation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Exact blockwise centering identity. -/
theorem harperTwoHeightBallotBlockVector_eq_translate
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) (eta : Problem520.HarperPrimeCube y) :
    harperTwoHeightBallotBlockVector y S t s eta =
      harperPairTranslate (harperTwoHeightBallotBlockDrift y S t s)
        (harperTwoHeightPrimeBlockVector y S t s eta) := by
  apply Prod.ext
  · exact harperCenteredLinearPrimeBlockSum_eq_twoHeightFluctuation_add_drift
      y S t s t t eta
  · exact harperCenteredLinearPrimeBlockSum_eq_twoHeightFluctuation_add_drift
      y S t s s s eta

/-- The literal ballot block law under the joint tilt. -/
noncomputable def harperTwoHeightBallotBlockLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) : Measure (Real × Real) :=
  Measure.map (harperTwoHeightBallotBlockVector y S t s)
    (harperTwoHeightCubeLaw y t s)

instance harperTwoHeightBallotBlockLaw_isProbabilityMeasure
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    IsProbabilityMeasure (harperTwoHeightBallotBlockLaw y S t s) := by
  unfold harperTwoHeightBallotBlockLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_of_finite _).aemeasurable

/-- The comparison Gaussian translated by the exact ballot drift. -/
noncomputable def harperTwoHeightDriftedIndependentGaussianBlockLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) : Measure (Real × Real) :=
  Measure.map
    (harperPairTranslate (harperTwoHeightBallotBlockDrift y S t s))
    (harperTwoHeightIndependentGaussianBlockLaw y S t s)

instance harperTwoHeightDriftedIndependentGaussianBlockLaw_isProbabilityMeasure
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    IsProbabilityMeasure
      (harperTwoHeightDriftedIndependentGaussianBlockLaw y S t s) := by
  unfold harperTwoHeightDriftedIndependentGaussianBlockLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_harperPairTranslate _).aemeasurable

theorem harperTwoHeightBallotBlockLaw_eq_translate
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    harperTwoHeightBallotBlockLaw y S t s =
      Measure.map
        (harperPairTranslate (harperTwoHeightBallotBlockDrift y S t s))
        (harperTwoHeightPrimeBlockVectorLaw y S t s) := by
  unfold harperTwoHeightBallotBlockLaw harperTwoHeightPrimeBlockVectorLaw
  rw [Measure.map_map (measurable_harperPairTranslate _)
    (measurable_of_finite _)]
  apply Measure.map_congr
  exact ae_of_all (harperTwoHeightCubeLaw y t s) fun eta ↦
    harperTwoHeightBallotBlockVector_eq_translate y S t s eta

theorem preimage_harperPairTranslate_prod_Icc
    (d : Real × Real) (a b c e : Real) :
    harperPairTranslate d ⁻¹' (Icc a b ×ˢ Icc c e) =
      Icc (a - d.1) (b - d.1) ×ˢ Icc (c - d.2) (e - d.2) := by
  ext z
  change
    ((a ≤ z.1 + d.1 ∧ z.1 + d.1 ≤ b) ∧
      c ≤ z.2 + d.2 ∧ z.2 + d.2 ≤ e) ↔
    ((a - d.1 ≤ z.1 ∧ z.1 ≤ b - d.1) ∧
      c - d.2 ≤ z.2 ∧ z.2 ≤ e - d.2)
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- Closed-corridor comparison for the actual pair of ballot increments.
Both source and reference law carry the same exact deterministic drift. -/
theorem harperScheduledTwoHeightBallotClosedRectangleMass_le_driftedGaussian_cutoff
    (y j n : Nat) (t s : Real) {a b c d : Real}
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
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
        1 / (n : Real) ^ (40 : Nat)) :
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat) *
        (harperTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) t s).real
            (Icc a b ×ˢ Icc c d) ≤
      (harperTwoHeightDriftedIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y j) t s).real
          (Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
            Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (d + 4 * (1 / (n : Real) ^ (2 : Nat)))) +
        6 / (n : Real) ^ (4 : Nat) := by
  let S := Problem520.harperScheduledPrimeBlock y j
  let drift := harperTwoHeightBallotBlockDrift y S t s
  have hsource :
      (harperTwoHeightBallotBlockLaw y S t s).real
          (Icc a b ×ˢ Icc c d) =
        (harperTwoHeightPrimeBlockVectorLaw y S t s).real
          (Icc (a - drift.1) (b - drift.1) ×ˢ
            Icc (c - drift.2) (d - drift.2)) := by
    rw [harperTwoHeightBallotBlockLaw_eq_translate,
      map_measureReal_apply (measurable_harperPairTranslate drift)
        (measurableSet_Icc.prod measurableSet_Icc),
      preimage_harperPairTranslate_prod_Icc]
  have htarget :
      (harperTwoHeightDriftedIndependentGaussianBlockLaw y S t s).real
          (Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
            Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (d + 4 * (1 / (n : Real) ^ (2 : Nat)))) =
        (harperTwoHeightIndependentGaussianBlockLaw y S t s).real
          (Icc ((a - drift.1) - 4 * (1 / (n : Real) ^ (2 : Nat)))
              ((b - drift.1) + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
            Icc ((c - drift.2) - 4 * (1 / (n : Real) ^ (2 : Nat)))
              ((d - drift.2) + 4 * (1 / (n : Real) ^ (2 : Nat)))) := by
    unfold harperTwoHeightDriftedIndependentGaussianBlockLaw
    rw [map_measureReal_apply (measurable_harperPairTranslate drift)
      (measurableSet_Icc.prod measurableSet_Icc),
      preimage_harperPairTranslate_prod_Icc]
    congr 1 <;> ring
  rw [show Problem520.harperScheduledPrimeBlock y j = S by rfl,
    hsource, htarget]
  apply
    harperScheduledTwoHeightClosedCorridorRectangleMass_le_independentGaussian_cutoff
      y j n t s hn
  · linarith
  · linarith
  · linarith
  · linarith
  · exact hfrequency
  · exact hendpoint
  · exact hcovariance

#print axioms Erdos.Problem1144.harperTwoHeightBallotBlockVector_eq_translate
#print axioms Erdos.Problem1144.harperTwoHeightBallotBlockLaw_eq_translate
#print axioms Erdos.Problem1144.harperScheduledTwoHeightBallotClosedRectangleMass_le_driftedGaussian_cutoff

end

end Problem1144
end Erdos
