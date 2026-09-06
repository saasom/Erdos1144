import Erdos.Problem1144.HarperGaussianFenceSummation
import Erdos.Problem1144.HarperShiftedLatticeAveraging

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Fixed-start one-height logarithmic ballot

The earlier transfer discarded the whole Gaussian moderate-box complement.
That absolute error forced the scheduled start to grow with the path length.
For the actual logarithmic core this loss is unnecessary: its two-sided path
corridor bounds every coordinate linearly in elapsed time, while the scheduled
moderate radius grows exponentially in the absolute block index.  From one
fixed block onward the core is therefore contained in the moderate box
pointwise.
-/

/-- Every increment of a path in the schedule-free logarithmic core is at
most linear in elapsed time. -/
theorem abs_coordinate_le_of_gaussianLogBallotCore
    {n : Nat} {omega : Fin n -> Real}
    (homega : omega ∈ harper1144GaussianLogBallotCoreEvent n)
    (i : Fin n) :
    |omega i| <= 128 * (((i.val + 1 : Nat) : Real)) := by
  apply abs_coordinate_le_of_linear_partialSum_guard omega
  · intro k
    have hk :=
      (Problem520.mem_harperPartialSumBarrierSet.mp homega k).1
    nlinarith
  · intro k
    have hk :=
      (Problem520.mem_harperPartialSumBarrierSet.mp homega k).2
    have harg : (1 : Real) <= ((k.val + 1 : Nat) : Real) := by
      exact_mod_cast (show 1 <= k.val + 1 by omega)
    have hlog : 0 <= Real.log ((k.val + 1 : Nat) : Real) :=
      Real.log_nonneg harg
    nlinarith

/-- From block `30` onward, the scheduled moderate radius contains the
coordinate envelope forced by the logarithmic core. -/
theorem gaussianLogBallotCore_coordinate_le_scheduledModerateRadius
    {start n : Nat} (hstart : 30 <= start)
    {omega : Fin n -> Real}
    (homega : omega ∈ harper1144GaussianLogBallotCoreEvent n)
    (i : Fin n) :
    |omega i| <=
      Problem520.harperScheduledModerateRadius start n i := by
  have hcoord := abs_coordinate_le_of_gaussianLogBallotCore homega i
  have henvelope :=
    harperScheduled_linearEnvelope_le_moderateWindow hstart i.val
  have hradius :=
    Problem520.one_eighth_sqrt_two_pow_le_harperScheduledModerateRadius
      i (by omega : 8 <= start + (i : Nat))
  have hi : (0 : Real) <= ((i.val + 1 : Nat) : Real) := by positivity
  nlinarith

/-- The Gaussian logarithmic core lies in the full scheduled moderate box
for every path length once the start is fixed at block `30` or later. -/
theorem harper1144GaussianLogBallotCoreEvent_subset_coordinateBox
    {start n : Nat} (hstart : 30 <= start) :
    harper1144GaussianLogBallotCoreEvent n ⊆
      Problem520.harperCoordinateBox
        (Problem520.harperScheduledModerateRadius start n) := by
  intro omega homega
  rw [Problem520.mem_harperCoordinateBox]
  intro i
  exact gaussianLogBallotCore_coordinate_le_scheduledModerateRadius
    hstart homega i

/-- The core simultaneously supplies the contracted barrier and the
moderate-coordinate condition consumed by reverse finite slicing. -/
theorem harper1144GaussianLogBallotCoreEvent_subset_contracted_inter_box
    {start n : Nat} (hstart : 30 <= start) :
    harper1144GaussianLogBallotCoreEvent n ⊆
      harper1144ContractedGaussianLogBallotEvent start n ∩
        Problem520.harperCoordinateBox
          (Problem520.harperScheduledModerateRadius start n) := by
  intro omega homega
  exact ⟨
    harper1144GaussianLogBallotCoreEvent_subset_contracted
      (hstart.trans' (by norm_num)) homega,
    harper1144GaussianLogBallotCoreEvent_subset_coordinateBox
      hstart homega⟩

/-- The literal tilted one-height logarithmic ballot has an inverse-square-
root lower bound from one fixed scheduled start, uniformly in the path
length.  No `clog n` guard and no Gaussian box-tail subtraction remain. -/
theorem exists_harper1144LogBallotFixedStart_oneHeight_lower :
    ∃ J : Nat, ∀ start : Nat, J <= start -> ∀ n : Nat, 0 < n ->
      ∀ y : Nat, Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t ∈ harperLowerVerticalBand,
          (3 / 16 : Real) *
              Real.exp
                (-2 - harper1144GaussianLogFenceCertificateBudget) /
                Real.sqrt (n : Real) <=
            (Problem520.harperTiltedCubeLaw y t).real
              (harper1144LogBallotCubeEvent y start n t) := by
  obtain ⟨Jtransfer, htransfer⟩ :=
    exists_three_fourths_mul_contractedGaussianLogBallot_inter_box_le_tiltedLogBallot
  obtain ⟨Jvar, hvar⟩ :=
    Problem520.exists_harperScheduledCentralBandVarianceVector_quarter_half
  let J : Nat := max 30 (max (Jtransfer + 1) (Jvar + 1))
  refine ⟨J, ?_⟩
  intro start hstart n hn
  intro y hy
  intro t ht
  have hstart30 : 30 <= start :=
    (le_max_left 30 (max (Jtransfer + 1) (Jvar + 1))).trans hstart
  have hstartTransfer : Jtransfer + 1 <= start :=
    (le_max_of_le_right (le_max_left (Jtransfer + 1) (Jvar + 1))).trans
      hstart
  have hstartVar : Jvar + 1 <= start :=
    (le_max_of_le_right (le_max_right (Jtransfer + 1) (Jvar + 1))).trans
      hstart
  have htBounds : (1 / 3 : Real) <= t ∧ t <= (1 / 2 : Real) := ht
  have htPositive : 0 < t := by linarith
  have htLower : (1 / 2 : Real) ^ (1 + 1) < |t| := by
    rw [abs_of_pos htPositive]
    norm_num
    linarith
  have htUpper : |t| <= (1 / 2 : Real) ^ (1 : Nat) := by
    rw [abs_of_pos htPositive]
    norm_num
    exact htBounds.2
  let variance : Fin n -> NNReal := fun i =>
    Problem520.harperLinearBlockVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t
  let Q : Measure (Fin n -> Real) :=
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
  have hvarianceVector := hvar 1 start hstartVar n y hy t
    htLower htUpper (fun _i : Fin n => t) (by intro i; simp)
  have hlower : ∀ i, (1 / 4 : NNReal) <= variance i := by
    intro i
    exact_mod_cast (hvarianceVector i).1.le
  have hupper : ∀ i, variance i <= (1 / 2 : NNReal) := by
    intro i
    exact_mod_cast (hvarianceVector i).2.le
  have hcore :
      Real.exp
            (-2 - harper1144GaussianLogFenceCertificateBudget) /
          (4 * Real.sqrt (n : Real)) <=
        Q.real (harper1144GaussianLogBallotCoreEvent n) := by
    simpa only [Q] using
      exp_neg_certificateBudget_div_sqrt_le_gaussianLogBallotCore
        n hn variance hlower hupper
  have hinter :
      Real.exp
            (-2 - harper1144GaussianLogFenceCertificateBudget) /
          (4 * Real.sqrt (n : Real)) <=
        Q.real
          (harper1144ContractedGaussianLogBallotEvent start n ∩
            Problem520.harperCoordinateBox
              (Problem520.harperScheduledModerateRadius start n)) :=
    hcore.trans (measureReal_mono
      (harper1144GaussianLogBallotCoreEvent_subset_contracted_inter_box
        hstart30))
  have hmain := htransfer 1 start hstartTransfer n y hy t
    htLower htUpper
  have hmain' :
      (3 / 4 : Real) *
          Q.real
            (harper1144ContractedGaussianLogBallotEvent start n ∩
              Problem520.harperCoordinateBox
                (Problem520.harperScheduledModerateRadius start n)) <=
        (Problem520.harperTiltedCubeLaw y t).real
          (harper1144LogBallotCubeEvent y start n t) := by
    simpa only [Q, variance, Problem520.harperGaussianBlockLaw] using hmain
  calc
    (3 / 16 : Real) *
          Real.exp
            (-2 - harper1144GaussianLogFenceCertificateBudget) /
          Real.sqrt (n : Real) =
        (3 / 4 : Real) *
          (Real.exp
              (-2 - harper1144GaussianLogFenceCertificateBudget) /
            (4 * Real.sqrt (n : Real))) := by ring
    _ <= (3 / 4 : Real) *
        Q.real
          (harper1144ContractedGaussianLogBallotEvent start n ∩
            Problem520.harperCoordinateBox
              (Problem520.harperScheduledModerateRadius start n)) := by
      gcongr
    _ <= (Problem520.harperTiltedCubeLaw y t).real
          (harper1144LogBallotCubeEvent y start n t) := hmain'

#print axioms Erdos.Problem1144.abs_coordinate_le_of_gaussianLogBallotCore
#print axioms Erdos.Problem1144.harper1144GaussianLogBallotCoreEvent_subset_coordinateBox
#print axioms Erdos.Problem1144.harper1144GaussianLogBallotCoreEvent_subset_contracted_inter_box
#print axioms Erdos.Problem1144.exists_harper1144LogBallotFixedStart_oneHeight_lower

end

end Problem1144
end Erdos
