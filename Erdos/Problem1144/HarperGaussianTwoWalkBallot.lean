import Erdos.Problem1144.HarperLogBarrierBallot
import Erdos.Problem520.HarperCentralBandBarrier

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# The independent Gaussian two-walk ballot

The separated-height comparison is supposed to replace the pair of tilted
Rademacher block paths by two nearly independent Gaussian paths.  This file
closes the Gaussian endpoint of that comparison: under the literal product
of the two variance-matched Gaussian laws, the simultaneous logarithmic
ballot has probability `O(1/n)`.

Thus the remaining bivariate work is only the replacement of the actual
two-height block law by this product law, with a controlled correlation
error.  There is no further two-walk probability theorem hidden behind that
replacement.
-/

/-- The expanded logarithmic barrier used by reverse finite slicing. -/
def harper1144ExpandedGaussianLogBallotEvent
    (start n : Nat) : Set (Fin n → Real) :=
  Problem520.harperExpandedPartialSumBarrierSet
    (harper1144LogBallotLowerBarrier start n)
    (harper1144LogBallotUpperBarrier n)
    (Problem520.harperScheduledRelativeCellWidth start n)

theorem measurableSet_harper1144ExpandedGaussianLogBallotEvent
    (start n : Nat) :
    MeasurableSet (harper1144ExpandedGaussianLogBallotEvent start n) := by
  unfold harper1144ExpandedGaussianLogBallotEvent
    Problem520.harperExpandedPartialSumBarrierSet
  exact Problem520.measurableSet_harperPartialSumBarrierSet _ _

/-- The elapsed-prefix pinch lies below the flat level `1`, so the expanded
event is contained in the existing `x = 1, c = 0` Gaussian barrier event. -/
theorem harper1144ExpandedGaussianLogBallotEvent_subset_flat
    (start n : Nat) :
    harper1144ExpandedGaussianLogBallotEvent start n ⊆
      Problem520.harperExpandedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start n)
        (Problem520.harperNormalizedReverseLogBarrier n 1 0)
        (Problem520.harperScheduledRelativeCellWidth start n) := by
  intro omega homega
  unfold harper1144ExpandedGaussianLogBallotEvent at homega
  unfold Problem520.harperExpandedPartialSumBarrierSet at homega ⊢
  rw [Problem520.mem_harperPartialSumBarrierSet] at homega ⊢
  intro k
  have hk := homega k
  refine ⟨hk.1, hk.2.trans ?_⟩
  unfold Problem520.harperNormalizedReverseLogBarrier
  have hupper := harper1144LogBallotUpperBarrier_le_one n k
  linarith

/-- Product of the two variance-matched, independent scheduled Gaussian path
laws at heights `t` and `s`. -/
noncomputable def harper1144IndependentGaussianTwoWalkMeasure
    (y start n : Nat) (t s : Real) :
    Measure ((Fin n → Real) × (Fin n → Real)) :=
  (Problem520.harperScheduledOffDiagonalGaussianProductMeasure
      y start n t (fun _i : Fin n ↦ t)).prod
    (Problem520.harperScheduledOffDiagonalGaussianProductMeasure
      y start n s (fun _i : Fin n ↦ s))

instance harper1144IndependentGaussianTwoWalkMeasure_isProbabilityMeasure
    (y start n : Nat) (t s : Real) :
    IsProbabilityMeasure
      (harper1144IndependentGaussianTwoWalkMeasure y start n t s) := by
  unfold harper1144IndependentGaussianTwoWalkMeasure
  infer_instance

/-- The independent Gaussian two-walk probability is the product of the two
one-walk probabilities, hence has the sharp squared-ballot scale `1/n`. -/
theorem exists_harper1144IndependentGaussianTwoWalk_logBallot_le :
    ∃ J : Nat, ∀ start : Nat, J + 1 ≤ start →
      ∀ n : Nat, 0 < n → ∀ y : Nat,
        Problem520.harperBlockEndpoint (start + n) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (harper1144IndependentGaussianTwoWalkMeasure
                y start n t s).real
              (harper1144ExpandedGaussianLogBallotEvent start n ×ˢ
                harper1144ExpandedGaussianLogBallotEvent start n) ≤
              (102400 : Real) * (n : Real)⁻¹ := by
  obtain ⟨J, hwalk⟩ :=
    Problem520.exists_harperScheduledCentralBandGaussianWalk_expandedReverseLogBarrier_probability_le
  refine ⟨J, ?_⟩
  intro start hstart n hn y hy t ht s hs
  have htBounds : (1 / 3 : Real) ≤ t ∧ t ≤ 1 / 2 := ht
  have hsBounds : (1 / 3 : Real) ≤ s ∧ s ≤ 1 / 2 := hs
  have htNonneg : 0 ≤ t := by linarith
  have hsNonneg : 0 ≤ s := by linarith
  have htLower : (1 / 2 : Real) ^ (1 + 1) < |t| := by
    rw [abs_of_nonneg htNonneg]
    norm_num
    linarith
  have hsLower : (1 / 2 : Real) ^ (1 + 1) < |s| := by
    rw [abs_of_nonneg hsNonneg]
    norm_num
    linarith
  have htUpper : |t| ≤ (1 / 2 : Real) ^ 1 := by
    rw [abs_of_nonneg htNonneg]
    norm_num
    exact htBounds.2
  have hsUpper : |s| ≤ (1 / 2 : Real) ^ 1 := by
    rw [abs_of_nonneg hsNonneg]
    norm_num
    exact hsBounds.2
  let A := harper1144ExpandedGaussianLogBallotEvent start n
  let Qt := Problem520.harperScheduledOffDiagonalGaussianProductMeasure
    y start n t (fun _i : Fin n ↦ t)
  let Qs := Problem520.harperScheduledOffDiagonalGaussianProductMeasure
    y start n s (fun _i : Fin n ↦ s)
  have htWalk : Qt.real A ≤
      320 / Real.sqrt (n : Real) := by
    have h := hwalk 1 start hstart n hn y hy t htLower htUpper
      (fun _i : Fin n ↦ t) (fun _i ↦ by simp) 1 0
      (by norm_num) (by norm_num)
      (harper1144LogBallotLowerBarrier start n)
    norm_num at h
    exact (measureReal_mono
      (harper1144ExpandedGaussianLogBallotEvent_subset_flat start n)).trans
        (by simpa only [Qt, A] using h)
  have hsWalk : Qs.real A ≤
      320 / Real.sqrt (n : Real) := by
    have h := hwalk 1 start hstart n hn y hy s hsLower hsUpper
      (fun _i : Fin n ↦ s) (fun _i ↦ by simp) 1 0
      (by norm_num) (by norm_num)
      (harper1144LogBallotLowerBarrier start n)
    norm_num at h
    exact (measureReal_mono
      (harper1144ExpandedGaussianLogBallotEvent_subset_flat start n)).trans
        (by simpa only [Qs, A] using h)
  have hproduct : (Qt.prod Qs).real (A ×ˢ A) =
      Qt.real A * Qs.real A := by
    simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  change (Qt.prod Qs).real (A ×ˢ A) ≤
    (102400 : Real) * (n : Real)⁻¹
  rw [hproduct]
  calc
    Qt.real A * Qs.real A ≤
        (320 / Real.sqrt (n : Real)) *
          (320 / Real.sqrt (n : Real)) :=
      mul_le_mul htWalk hsWalk measureReal_nonneg (by positivity)
    _ = (102400 : Real) * (n : Real)⁻¹ := by
      rw [div_mul_div_comm, ← pow_two (Real.sqrt (n : Real)),
        Real.sq_sqrt hnR.le]
      field_simp
      norm_num

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.exists_harper1144IndependentGaussianTwoWalk_logBallot_le
