import Erdos.Problem1144.HarperLogBarrierBallot

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Lower transfer for the elapsed-prefix logarithmic ballot

This file isolates the probabilistic first-moment needle from the already
completed reverse local-limit comparison.  The Gaussian input must be proved
for the cumulatively contracted logarithmic corridor.  The theorems below
then transfer it, with the fixed `3/4` reverse-comparison constant and only the
geometric moderate-box loss, to the literal tilted Rademacher cube event.
-/

/-- The Gaussian corridor which reserves exactly the cumulative lattice
width required by reverse finite slicing. -/
noncomputable def harper1144ContractedGaussianLogBallotEvent
    (start n : Nat) : Set (Fin n -> Real) :=
  Problem520.harperPartialSumBarrierSet
    (fun k => harper1144LogBallotLowerBarrier start n k +
      Problem520.harperCumulativeCellWidth
        (Problem520.harperScheduledRelativeCellWidth start n) k)
    (fun k => harper1144LogBallotUpperBarrier n k -
      Problem520.harperCumulativeCellWidth
        (Problem520.harperScheduledRelativeCellWidth start n) k)

theorem measurableSet_harper1144ContractedGaussianLogBallotEvent
    (start n : Nat) :
    MeasurableSet (harper1144ContractedGaussianLogBallotEvent start n) := by
  unfold harper1144ContractedGaussianLogBallotEvent
  exact Problem520.measurableSet_harperPartialSumBarrierSet _ _

/-- A schedule-free core event for the one-height analytic theorem.  The
half-unit upper slack pays for every cumulative lattice width once the
scheduled path starts at block `16`; the linear lower guard is stronger than
the literal contracted lower boundary. -/
noncomputable def harper1144GaussianLogBallotCoreEvent
    (n : Nat) : Set (Fin n -> Real) :=
  Problem520.harperPartialSumBarrierSet
    (fun k => -32 * ((k.val + 1 : Nat) : Real))
    (fun k => (1 / 2 : Real) -
      2 * Real.log ((k.val + 1 : Nat) : Real))

theorem measurableSet_harper1144GaussianLogBallotCoreEvent
    (n : Nat) :
    MeasurableSet (harper1144GaussianLogBallotCoreEvent n) := by
  unfold harper1144GaussianLogBallotCoreEvent
  exact Problem520.measurableSet_harperPartialSumBarrierSet _ _

/-- The entire cumulative reverse-slicing mesh is at most `1/start`. -/
theorem harperCumulativeScheduledRelativeCellWidth_le_inv
    {start n : Nat} (hstart : 0 < start) (k : Fin n) :
    Problem520.harperCumulativeCellWidth
        (Problem520.harperScheduledRelativeCellWidth start n) k <=
      1 / (start : Real) := by
  let delta := Problem520.harperScheduledRelativeCellWidth start n
  have hpartial :
      (∑ i ∈ Finset.Iic k, delta i) <= ∑ i : Fin n, delta i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_univ _
    · intro i _hi _hnot
      exact (Problem520.harperScheduledRelativeIntervalWidth_pos
        (start + (i : Nat))).le
  calc
    Problem520.harperCumulativeCellWidth
        (Problem520.harperScheduledRelativeCellWidth start n) k =
        ∑ i ∈ Finset.Iic k, delta i := rfl
    _ <= ∑ i : Fin n, delta i := hpartial
    _ <= 1 / (start : Real) := by
      simpa only [delta, Problem520.harperScheduledRelativeCellWidth] using
        sum_fin_harperScheduledRelativeIntervalWidth_le_inv start n hstart

/-- At block `16` and beyond, every scheduled moderate radius is at least
`32`. -/
theorem thirtyTwo_le_harperScheduledModerateRadius
    {start n : Nat} (hstart : 16 <= start) (i : Fin n) :
    (32 : Real) <= Problem520.harperScheduledModerateRadius start n i := by
  have hindex : 16 <= start + (i : Nat) := by omega
  have hpowNat : 2 ^ 16 <= 2 ^ (start + (i : Nat)) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hindex
  have hpowReal : (65536 : Real) <=
      ((2 ^ (start + (i : Nat)) : Nat) : Real) := by
    exact_mod_cast hpowNat
  have hsqrt : (256 : Real) <= Real.sqrt
      (((2 ^ (start + (i : Nat)) : Nat) : Real)) := by
    have := Real.sqrt_le_sqrt hpowReal
    norm_num at this ⊢
    exact this
  have hradius :=
    Problem520.one_eighth_sqrt_two_pow_le_harperScheduledModerateRadius
      i (by omega : 8 <= start + (i : Nat))
  nlinarith

/-- The schedule-free core corridor lies inside the exact contracted
logarithmic corridor consumed by reverse slicing. -/
theorem harper1144GaussianLogBallotCoreEvent_subset_contracted
    {start n : Nat} (hstart : 16 <= start) :
    harper1144GaussianLogBallotCoreEvent n ⊆
      harper1144ContractedGaussianLogBallotEvent start n := by
  intro omega homega
  intro k
  have hkCore := homega k
  let delta := Problem520.harperScheduledRelativeCellWidth start n
  let width := Problem520.harperCumulativeCellWidth delta k
  have hwidthNonneg : 0 <= width := by
    dsimp only [width]
    exact Problem520.harperCumulativeCellWidth_nonneg
      (fun i => (Problem520.harperScheduledRelativeIntervalWidth_pos
        (start + (i : Nat))).le) k
  have hwidthInv : width <= 1 / (start : Real) := by
    simpa only [width, delta] using
      harperCumulativeScheduledRelativeCellWidth_le_inv (by omega) k
  have hstartReal : (16 : Real) <= start := by exact_mod_cast hstart
  have hwidthHalf : width <= (1 / 2 : Real) :=
    hwidthInv.trans (by
      exact (one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2)
        (by linarith : (2 : Real) <= start)))
  have hsumRadius :
      32 * ((k.val + 1 : Nat) : Real) <=
        ∑ i ∈ Finset.Iic k,
          Problem520.harperScheduledModerateRadius start n i := by
    calc
      32 * ((k.val + 1 : Nat) : Real) =
          ∑ _i ∈ Finset.Iic k, (32 : Real) := by
        simp
        ring
      _ <= ∑ i ∈ Finset.Iic k,
          Problem520.harperScheduledModerateRadius start n i := by
        exact Finset.sum_le_sum fun i _hi =>
          thirtyTwo_le_harperScheduledModerateRadius hstart i
  have hlowerContracted :
      harper1144LogBallotLowerBarrier start n k + width <=
        -32 * ((k.val + 1 : Nat) : Real) := by
    unfold harper1144LogBallotLowerBarrier
      harperScheduledAutomaticLowerBarrier
    rw [← max_add_add_right]
    apply max_le
    · dsimp only [width, delta]
      linarith
    · have hkm : (1 : Real) <= ((k.val + 1 : Nat) : Real) := by
        exact_mod_cast (show 1 <= k.val + 1 by omega)
      linarith
  have hupperContracted :
      (1 / 2 : Real) -
          2 * Real.log ((k.val + 1 : Nat) : Real) <=
        harper1144LogBallotUpperBarrier n k - width := by
    unfold harper1144LogBallotUpperBarrier
    linarith
  exact ⟨hlowerContracted.trans hkCore.1,
    hkCore.2.trans hupperContracted⟩

/-- Reverse local comparison for the exact contracted logarithmic event.
This is the non-Gaussian part of the one-height lower bound. -/
theorem
    exists_three_fourths_mul_contractedGaussianLogBallot_inter_box_le_tiltedLogBallot :
    ∃ J : Nat, ∀ d start : Nat, J + d <= start -> ∀ n y : Nat,
      Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
            (3 / 4 : Real) *
                (Measure.pi (fun i : Fin n =>
                  Problem520.harperGaussianBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + (i : Nat))) t t)).real
                  (harper1144ContractedGaussianLogBallotEvent start n ∩
                    Problem520.harperCoordinateBox
                      (Problem520.harperScheduledModerateRadius start n)) <=
              (Problem520.harperTiltedCubeLaw y t).real
                (harper1144LogBallotCubeEvent y start n t) := by
  obtain ⟨J, hJ⟩ :=
    exists_three_fourths_mul_gaussian_contractedBarrier_le_harperScheduledCentralBandBarrier
  refine ⟨J, ?_⟩
  intro d start hstart n y hy t htLower htUpper
  let Q : Measure (Fin n -> Real) := Measure.pi (fun i : Fin n =>
    Problem520.harperGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t)
  let P : Measure (Fin n -> Real) := Measure.pi (fun i : Fin n =>
    Problem520.harperCenteredLinearBlockLaw y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t)
  let lower := harper1144LogBallotLowerBarrier start n
  let upper := harper1144LogBallotUpperBarrier n
  have hcompare := hJ d start hstart n y hy t htLower htUpper lower upper
  have hcube :
      (Problem520.harperTiltedCubeLaw y t).real
          (harper1144LogBallotCubeEvent y start n t) =
        P.real (Problem520.harperPartialSumBarrierSet lower upper) := by
    unfold harper1144LogBallotCubeEvent
    rw [Problem520.harperTiltedCubeLaw_real_preimage_centeredBlockVectorVarying_eq_pi
      y start n t (fun _i : Fin n => t)
      (Problem520.harperPartialSumBarrierSet lower upper)
      (Problem520.measurableSet_harperPartialSumBarrierSet lower upper)]
  rw [hcube]
  simpa only [Q, P, lower, upper,
    harper1144ContractedGaussianLogBallotEvent] using hcompare

/-- Any lower bound for the contracted Gaussian logarithmic ballot transfers
after subtracting only the Gaussian moderate-box complement. -/
theorem
    exists_three_fourths_mul_gaussianLogBallot_sub_boxTail_le_tiltedLogBallot :
    ∃ J : Nat, ∀ d start : Nat, J + d <= start -> ∀ n y : Nat,
      Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
            ∀ L : Real,
              L <=
                (Measure.pi (fun i : Fin n =>
                  Problem520.harperGaussianBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + (i : Nat))) t t)).real
                  (harper1144ContractedGaussianLogBallotEvent start n) ->
              (3 / 4 : Real) *
                  (L -
                    (Measure.pi (fun i : Fin n =>
                      Problem520.harperGaussianBlockLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (start + (i : Nat))) t t)).real
                      (Problem520.harperCoordinateBox
                        (Problem520.harperScheduledModerateRadius start n))ᶜ) <=
                (Problem520.harperTiltedCubeLaw y t).real
                  (harper1144LogBallotCubeEvent y start n t) := by
  obtain ⟨J, hJ⟩ :=
    exists_three_fourths_mul_contractedGaussianLogBallot_inter_box_le_tiltedLogBallot
  refine ⟨J, ?_⟩
  intro d start hstart n y hy t htLower htUpper L hL
  let Q : Measure (Fin n -> Real) := Measure.pi (fun i : Fin n =>
    Problem520.harperGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t)
  let A := harper1144ContractedGaussianLogBallotEvent start n
  let B := Problem520.harperCoordinateBox
    (Problem520.harperScheduledModerateRadius start n)
  have hcover : A ⊆ (A ∩ B) ∪ Bᶜ := by
    intro omega homega
    by_cases hbox : omega ∈ B
    · exact Or.inl ⟨homega, hbox⟩
    · exact Or.inr hbox
  have hsplit : Q.real A <= Q.real (A ∩ B) + Q.real Bᶜ :=
    (measureReal_mono hcover).trans (measureReal_union_le _ _)
  have hinter : L - Q.real Bᶜ <= Q.real (A ∩ B) := by
    linarith
  have hcompare := hJ d start hstart n y hy t htLower htUpper
  calc
    (3 / 4 : Real) * (L - Q.real Bᶜ) <=
        (3 / 4 : Real) * Q.real (A ∩ B) := by gcongr
    _ <= (Problem520.harperTiltedCubeLaw y t).real
          (harper1144LogBallotCubeEvent y start n t) := by
      simpa only [Q, A, B] using hcompare

/-- Once the Gaussian moderate-box tail costs at most half of a Gaussian
log-ballot lower bound, the literal tilted event retains a fixed `3/8`
fraction. -/
theorem
    exists_three_eighths_mul_gaussianLogBallot_le_tiltedLogBallot :
    ∃ J : Nat, ∀ d start : Nat, J + d <= start -> ∀ n y : Nat,
      Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
            ∀ L : Real,
              L <=
                (Measure.pi (fun i : Fin n =>
                  Problem520.harperGaussianBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + (i : Nat))) t t)).real
                  (harper1144ContractedGaussianLogBallotEvent start n) ->
              (Measure.pi (fun i : Fin n =>
                Problem520.harperGaussianBlockLaw y
                  (Problem520.harperScheduledPrimeBlock y
                    (start + (i : Nat))) t t)).real
                (Problem520.harperCoordinateBox
                  (Problem520.harperScheduledModerateRadius start n))ᶜ <=
                  (1 / 2 : Real) * L ->
              (3 / 8 : Real) * L <=
                (Problem520.harperTiltedCubeLaw y t).real
                  (harper1144LogBallotCubeEvent y start n t) := by
  obtain ⟨J, hJ⟩ :=
    exists_three_fourths_mul_gaussianLogBallot_sub_boxTail_le_tiltedLogBallot
  refine ⟨J, ?_⟩
  intro d start hstart n y hy t htLower htUpper L hL hbox
  have hmain := hJ d start hstart n y hy t htLower htUpper L hL
  have hremain : (1 / 2 : Real) * L <= L -
      (Measure.pi (fun i : Fin n =>
        Problem520.harperGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y
            (start + (i : Nat))) t t)).real
        (Problem520.harperCoordinateBox
          (Problem520.harperScheduledModerateRadius start n))ᶜ := by
    linarith
  calc
    (3 / 8 : Real) * L =
        (3 / 4 : Real) * ((1 / 2 : Real) * L) := by ring
    _ <= (3 / 4 : Real) *
        (L -
          (Measure.pi (fun i : Fin n =>
            Problem520.harperGaussianBlockLaw y
              (Problem520.harperScheduledPrimeBlock y
                (start + (i : Nat))) t t)).real
            (Problem520.harperCoordinateBox
              (Problem520.harperScheduledModerateRadius start n))ᶜ) := by
      gcongr
    _ <= (Problem520.harperTiltedCubeLaw y t).real
          (harper1144LogBallotCubeEvent y start n t) := hmain

#print axioms Erdos.Problem1144.exists_three_fourths_mul_contractedGaussianLogBallot_inter_box_le_tiltedLogBallot
#print axioms Erdos.Problem1144.exists_three_eighths_mul_gaussianLogBallot_le_tiltedLogBallot
#print axioms Erdos.Problem1144.harper1144GaussianLogBallotCoreEvent_subset_contracted

end

end Problem1144
end Erdos
