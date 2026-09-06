import Erdos.Problem1144.HarperRankinBallotLowerComparison
import Erdos.Problem1144.HarperGaussianFixedStart

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Fixed-start one-height lower bound for the Rankin walk

The schedule-free Gaussian logarithmic core only uses the coordinate
variance window `[1/4,1/2]`.  Combining it with the shifted reverse slicing
theorem therefore gives the complete one-height ballot estimate at the
product-law level, uniformly in the path length.
-/

/-- The Rankin-centered scheduled product walk has the required
inverse-square-root logarithmic-ballot probability.  Only a fixed number of
terminal blocks is discarded, depending on the fixed localization parameter
`V`. -/
theorem exists_gap_harperRankinLogBallotFixedStart_product_lower
    (V : ℝ) (hV : 0 ≤ V) :
    ∃ gap J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n →
      ∀ y : ℕ,
        Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            (3 / 16 : ℝ) *
                Real.exp
                  (-2 - harper1144GaussianLogFenceCertificateBudget) /
                  Real.sqrt (n : ℝ) ≤
              (Measure.pi (fun i : Fin n =>
                harperRankinCenteredLinearBlockLaw y
                  (Problem520.harperScheduledPrimeBlock y
                    (start + (i : ℕ)))
                  (4 * V / Real.log (y : ℝ)) t t)).real
                (Problem520.harperPartialSumBarrierSet
                  (harper1144LogBallotLowerBarrier start n)
                  (harper1144LogBallotUpperBarrier n)) := by
  obtain ⟨gapTransfer, Jtransfer, htransfer⟩ :=
    exists_gap_three_fourths_mul_gaussian_contractedBarrier_le_harperRankinScheduledCentralBandBarrier
      V hV
  obtain ⟨gapVar, Jvar, hvar⟩ :=
    exists_gap_harperRankinScheduledCentralBandVarianceWindow V hV
  let gap := max gapTransfer gapVar
  let J : ℕ := max 30 (max (Jtransfer + 1) (Jvar + 1))
  refine ⟨gap, J, ?_⟩
  intro start hstart n hn y hy t ht
  have hstart30 : 30 ≤ start :=
    (le_max_left 30 (max (Jtransfer + 1) (Jvar + 1))).trans hstart
  have hstartTransfer : Jtransfer + 1 ≤ start :=
    (le_max_of_le_right
      (le_max_left (Jtransfer + 1) (Jvar + 1))).trans hstart
  have hstartVar : Jvar + 1 ≤ start :=
    (le_max_of_le_right
      (le_max_right (Jtransfer + 1) (Jvar + 1))).trans hstart
  have hyTransfer :
      Problem520.harperBlockEndpoint (start + n + gapTransfer) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (by
      dsimp only [gap]
      omega)).trans hy
  have htBounds : (1 / 3 : ℝ) ≤ t ∧ t ≤ (1 / 2 : ℝ) := ht
  have htPositive : 0 < t := by linarith
  have htLower : (1 / 2 : ℝ) ^ (1 + 1) < |t| := by
    rw [abs_of_pos htPositive]
    norm_num
    linarith
  have htUpper : |t| ≤ (1 / 2 : ℝ) ^ (1 : ℕ) := by
    rw [abs_of_pos htPositive]
    norm_num
    exact htBounds.2
  let variance : Fin n → NNReal := fun i =>
    harperRankinLinearBlockVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
      (4 * V / Real.log (y : ℝ)) t t
  let Q : Measure (Fin n → ℝ) :=
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
  have hvariance (i : Fin n) :
      (1 / 4 : ℝ) < (variance i : ℝ) ∧
        (variance i : ℝ) < 3 / 8 := by
    have hfar :
        Problem520.harperBlockEndpoint
            (start + (i : ℕ) + gapVar + 1) ≤ y := by
      apply (Problem520.monotone_harperBlockEndpoint ?_).trans hy
      dsimp only [gap]
      omega
    simpa only [variance, coe_harperRankinLinearBlockVarianceNNReal] using
      hvar 1 (start + (i : ℕ)) y (by omega) hfar t htLower htUpper
  have hlower : ∀ i, (1 / 4 : NNReal) ≤ variance i := by
    intro i
    exact_mod_cast (hvariance i).1.le
  have hupper : ∀ i, variance i ≤ (1 / 2 : NNReal) := by
    intro i
    exact_mod_cast (hvariance i).2.le.trans
      (by norm_num : (3 / 8 : ℝ) ≤ 1 / 2)
  have hcore :
      Real.exp
            (-2 - harper1144GaussianLogFenceCertificateBudget) /
          (4 * Real.sqrt (n : ℝ)) ≤
        Q.real (harper1144GaussianLogBallotCoreEvent n) := by
    simpa only [Q] using
      exp_neg_certificateBudget_div_sqrt_le_gaussianLogBallotCore
        n hn variance hlower hupper
  have hinter :
      Real.exp
            (-2 - harper1144GaussianLogFenceCertificateBudget) /
          (4 * Real.sqrt (n : ℝ)) ≤
        Q.real
          (harper1144ContractedGaussianLogBallotEvent start n ∩
            Problem520.harperCoordinateBox
              (Problem520.harperScheduledModerateRadius start n)) :=
    hcore.trans (measureReal_mono
      (harper1144GaussianLogBallotCoreEvent_subset_contracted_inter_box
        hstart30))
  have hmain := htransfer 1 start hstartTransfer n y hyTransfer t
    htLower htUpper
      (harper1144LogBallotLowerBarrier start n)
      (harper1144LogBallotUpperBarrier n)
  have hmain' :
      (3 / 4 : ℝ) *
          Q.real
            (harper1144ContractedGaussianLogBallotEvent start n ∩
              Problem520.harperCoordinateBox
                (Problem520.harperScheduledModerateRadius start n)) ≤
        (Measure.pi (fun i : Fin n =>
          harperRankinCenteredLinearBlockLaw y
            (Problem520.harperScheduledPrimeBlock y
              (start + (i : ℕ)))
            (4 * V / Real.log (y : ℝ)) t t)).real
          (Problem520.harperPartialSumBarrierSet
            (harper1144LogBallotLowerBarrier start n)
            (harper1144LogBallotUpperBarrier n)) := by
    simpa only [Q, variance, harperRankinGaussianBlockLaw,
      harper1144ContractedGaussianLogBallotEvent] using hmain
  calc
    (3 / 16 : ℝ) *
          Real.exp
            (-2 - harper1144GaussianLogFenceCertificateBudget) /
          Real.sqrt (n : ℝ) =
        (3 / 4 : ℝ) *
          (Real.exp
              (-2 - harper1144GaussianLogFenceCertificateBudget) /
            (4 * Real.sqrt (n : ℝ))) := by ring
    _ ≤ (3 / 4 : ℝ) *
        Q.real
          (harper1144ContractedGaussianLogBallotEvent start n ∩
            Problem520.harperCoordinateBox
              (Problem520.harperScheduledModerateRadius start n)) := by
      gcongr
    _ ≤ _ := hmain'

#print axioms
  Erdos.Problem1144.exists_gap_harperRankinLogBallotFixedStart_product_lower

end

end Problem1144
end Erdos
