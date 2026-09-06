import Erdos.Problem1144.HarperGaussianBallotLower
import Erdos.Problem1144.HarperTwoHeightRestrictedMass

open MeasureTheory Set

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# The sole remaining two-height certificate

The one-height ballot estimate for the explicit central-band graph is now
unconditional.  This module states only the matching two-height mass bound
and wires it through the existing restricted-energy and fractional-moment
handoffs.
-/

/-- The remaining analytic statement for the explicit ballot graph.  Both
sections use the same path length
`floor ((1 + log log y) / 4)` and the same automatic barriers already proved
to have the sharp one-height mass. -/
def HarperCentralLowerBallotTwoHeightStatement : Prop :=
  ∃ C : Real, 0 < C ∧ ∃ Y : Nat, ∀ y : Nat,
    Y <= y -> 4 <= y ->
      let n := harper1144LowerBallotPathLength y
      let A : Real -> Set (Problem520.HarperPrimeCube y) := fun t =>
        harperCentralLowerBallotCubeEvent y n n t
      (∫ ts,
          harperTwoHeightCubeMass y ts.1 ts.2 (A ts.1 ∩ A ts.2)
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand)) <=
        ((C * harperInitialCriticalScale y) *
          Real.log (y : Real)) ^ (2 : Nat)

/-- The explicit two-height estimate above supplies the general
one-height/two-height ballot certificate.  The one-height component is the
unconditional theorem from `HarperGaussianBallotLower`. -/
theorem harperRestrictedTwoHeightBallotStatement_of_centralLowerBallot
    (htwo : HarperCentralLowerBallotTwoHeightStatement) :
    HarperRestrictedTwoHeightBallotStatement := by
  obtain ⟨C, hC, Ytwo, htwo⟩ := htwo
  obtain ⟨delta, hdelta, Yone, hone⟩ :=
    exists_eventually_harper1144LowerBallot_tiltedProbability_ge_criticalScale
  refine ⟨delta, C, hdelta, hC, max 4 (max Yone Ytwo), ?_⟩
  intro y hyY hy4
  have hyBoth : max Yone Ytwo <= y := (le_max_right _ _).trans hyY
  have hyOne : Yone <= y := (le_max_left _ _).trans hyBoth
  have hyTwo : Ytwo <= y := (le_max_right _ _).trans hyBoth
  let n := harper1144LowerBallotPathLength y
  let G := harperCentralLowerBallotGraph y n n
  let A : Real -> Set (Problem520.HarperPrimeCube y) := fun t =>
    harperCentralLowerBallotCubeEvent y n n t
  refine ⟨G, A, ?_, ?_, ?_, ?_⟩
  · simpa only [G] using measurableSet_harperCentralLowerBallotGraph y n n
  · intro t omega
    rfl
  · intro t ht
    simpa only [A, n] using hone y hyOne t ht
  · simpa only [A, n] using htwo y hyTwo hy4

/-- End-to-end reduction of the missing lower half moment to the single
explicit two-height mass estimate. -/
theorem harperRademacherInitialHalfMomentLowerStatement_of_centralLowerBallot
    (htwo : HarperCentralLowerBallotTwoHeightStatement) :
    HarperRademacherInitialHalfMomentLowerStatement :=
  harperRademacherInitialHalfMomentLowerStatement_of_twoHeightBallot
    (harperRestrictedTwoHeightBallotStatement_of_centralLowerBallot htwo)

end
end Problem1144
end Erdos

#print axioms
  Erdos.Problem1144.harperRademacherInitialHalfMomentLowerStatement_of_centralLowerBallot
