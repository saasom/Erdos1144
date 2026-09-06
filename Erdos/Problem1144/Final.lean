import Erdos.Problem1144.MomentConcentration
import Erdos.Problem1144.PositiveBlockCertificate
import Erdos.Problem1144.Resonator
import Erdos.Problem1144.ResonatorMargin
import Erdos.Problem1144.HarperBlock
import Erdos.Problem1144.HarperProcessBlock
import Erdos.Problem1144.HarperSelector
import Erdos.Problem1144.HarperThresholdSelector
import Erdos.Problem1144.HarperAbundance
import Erdos.Problem1144.HarperCandidateFinalCertificate

namespace Erdos
namespace Problem1144

/-- The downstream proof of Erdős #1144 from finite moment concentration. -/
theorem erdos1144_of_momentConcentration
    (h : MomentConcentration) :
    Erdos1144 :=
  erdos1144_of_squareTarget
    (squareTarget_of_cubicRatioCert
      (cubicRatioCert_of_momentConcentration h))

/-- Temporary analytic input for development.

Eliminating this axiom is the main mathematical task.
-/
axiom momentConcentration : MomentConcentration

/-- Temporary resonator transfer input for development.

Eliminating this axiom is the current resonator fallback route to closing
#1144. It is sharper than a bare block estimate: the lower-tail bound is
obtained from
per-test positive resonator margins whose means dominate their raw fourth
moments.
-/
axiom resonatorTransferCertificate : ResonatorTransferCertificate

/-- The resonator route's positive-block certificate. -/
noncomputable def positiveBlockOmega_resonator : PositiveBlockOmega :=
  positiveBlockOmega_of_resonatorTransferCertificate resonatorTransferCertificate

/-- Erdős #1144 from the resonator transfer-certificate axiom. -/
theorem erdos1144_of_resonatorTransferCertificate_axiom : Erdos1144 :=
  erdos1144_of_positiveBlockOmega positiveBlockOmega_resonator

/-- Temporary split Harper-process input for development.

This comparison target asks for high-probability bounds for the large-prime
process failure and the smooth-remainder bad event, with summable total failure
budget.
-/
axiom harperProcessBlockCertificate : HarperProcessBlockCertificate

/-- The Harper-process route's positive-block certificate. -/
noncomputable def positiveBlockOmega_harperProcess : PositiveBlockOmega :=
  positiveBlockOmega_of_harperProcessBlockCertificate
    harperProcessBlockCertificate

/-- Erdős #1144 from the split Harper-process certificate axiom. -/
theorem erdos1144_of_harperProcessBlockCertificate_axiom : Erdos1144 :=
  erdos1144_of_positiveBlockOmega positiveBlockOmega_harperProcess

/-- Temporary test-point Harper-process input for development.

This older target asks directly for summable failure bounds for both the
large-prime process maximum and the smooth-remainder lower tail on the selected
mesh. It remains available as a comparison route.
-/
axiom harperTestPointBlockCertificate : HarperTestPointBlockCertificate

/-- The test-point Harper route's positive-block certificate. -/
noncomputable def positiveBlockOmega_harperTestPoint : PositiveBlockOmega :=
  positiveBlockOmega_of_harperTestPointBlockCertificate
    harperTestPointBlockCertificate

/-- Erdős #1144 from the test-point Harper-process certificate axiom. -/
theorem erdos1144_of_harperTestPointBlockCertificate_axiom : Erdos1144 :=
  erdos1144_of_positiveBlockOmega positiveBlockOmega_harperTestPoint

/-- Temporary refined test-point Harper-process input for development.

This target asks for a direct large-prime positive maximum failure bound and a
summable finite smooth-pair second-moment budget for the smooth-remainder bad
event. It remains available as a comparison route.
-/
axiom harperTestPointSecondMomentCertificate :
  HarperTestPointSecondMomentCertificate

/-- The refined test-point Harper route's positive-block certificate. -/
noncomputable def positiveBlockOmega_harperTestPointSecondMoment :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperTestPointSecondMomentCertificate
    harperTestPointSecondMomentCertificate

/-- Erdős #1144 from the refined test-point Harper-process certificate axiom. -/
theorem erdos1144_of_harperTestPointSecondMomentCertificate_axiom :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    positiveBlockOmega_harperTestPointSecondMoment

/-- Temporary geometry-refined test-point Harper-process input for development.

This comparison target chooses a finite mesh, proves that the large-prime
coefficient geometry has large variances and small covariances with high
probability, proves the one-sided positive maximum estimate on that good
geometry event, and proves the finite smooth-pair second-moment budget.
-/
axiom harperGeometrySecondMomentCertificate :
  HarperGeometrySecondMomentCertificate

/-- The geometry-refined Harper route's positive-block certificate. -/
noncomputable def positiveBlockOmega_harperGeometrySecondMoment :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperGeometrySecondMomentCertificate
    harperGeometrySecondMomentCertificate

/-- Erdős #1144 from the geometry-refined Harper-process certificate axiom. -/
theorem erdos1144_of_harperGeometrySecondMomentCertificate_axiom :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    positiveBlockOmega_harperGeometrySecondMoment

/-- Temporary finite-kernel geometry-refined test-point Harper-process input.

This comparison target refines
`harperGeometrySecondMomentCertificate`, the smooth side has been reduced to a
deterministic finite reciprocal-kernel budget; the elementary square-pair count
needed for that reduction is proved in `HarperProcess`. -/
axiom harperGeometryFiniteKernelCertificate :
  HarperGeometryFiniteKernelCertificate

/-- The finite-kernel geometry-refined Harper route's positive-block
certificate. -/
noncomputable def positiveBlockOmega_harperGeometryFiniteKernel :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperGeometryFiniteKernelCertificate
    harperGeometryFiniteKernelCertificate

/-- Erdős #1144 from the finite-kernel geometry-refined Harper-process
certificate axiom. -/
theorem erdos1144_of_harperGeometryFiniteKernelCertificate_axiom :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    positiveBlockOmega_harperGeometryFiniteKernel

/-- Temporary selector-based Harper-process input for development.

This comparison target chooses one test point, typically a large-prime winner
or near-winner, so the smooth remainder is paid only at that selected point
instead of over the entire deterministic mesh. -/
axiom harperSelectorBlockCertificate :
  HarperSelectorBlockCertificate

/-- The selector-based Harper route's positive-block certificate. -/
noncomputable def positiveBlockOmega_harperSelector :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperSelectorBlockCertificate
    harperSelectorBlockCertificate

/-- Erdős #1144 from the selector-based Harper-process certificate axiom. -/
theorem erdos1144_of_harperSelectorBlockCertificate_axiom :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    positiveBlockOmega_harperSelector

/-- Temporary concrete first-argmax Harper-process input for development.

This comparison target fixes the selector to be the least test point attaining
the large-prime maximum on the test mesh. The large-prime estimate is the
ordinary mesh-maximum failure bound, and the smooth estimate is the aggregate
lower-tail bound at that first argmax. -/
axiom harperMaxSelectorBlockCertificate :
  HarperMaxSelectorBlockCertificate

/-- The concrete first-argmax Harper route's positive-block certificate. -/
noncomputable def positiveBlockOmega_harperMaxSelector :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperMaxSelectorBlockCertificate
    harperMaxSelectorBlockCertificate

/-- Erdős #1144 from the concrete first-argmax Harper-process certificate
axiom. -/
theorem erdos1144_of_harperMaxSelectorBlockCertificate_axiom :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    positiveBlockOmega_harperMaxSelector

/-- Temporary fixed-candidate first-argmax event input for development.

This stricter comparison target assigns failure budgets to events saying that
a fixed test point is the least large-prime maximizer and has smooth remainder
below the buffer. It remains available, but the active paper route uses the
aggregate selected-smooth estimate in `harperMaxSelectorBlockCertificate`.
-/
axiom harperFirstMaxEventBlockCertificate :
  HarperFirstMaxEventBlockCertificate

/-- The fixed-candidate first-argmax event route's positive-block
certificate. -/
noncomputable def positiveBlockOmega_harperFirstMaxEvent :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperFirstMaxEventBlockCertificate
    harperFirstMaxEventBlockCertificate

/-- Erdős #1144 from the fixed-candidate first-argmax event certificate
axiom. -/
theorem erdos1144_of_harperFirstMaxEventBlockCertificate_axiom :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    positiveBlockOmega_harperFirstMaxEvent

/-- Temporary threshold-selector Harper-process input for development.

This direct route asks for a good-geometry failure bound, a bound for too few
large-prime threshold exceedances on that good event, and a bound for having
many threshold exceedances whose smooth remainder is bad. It remains available
as a comparison target; the active path below derives the few-exceedance bound
from a finite second-moment abundance certificate. -/
axiom harperThresholdSelectorBlockCertificate :
  HarperThresholdSelectorBlockCertificate

/-- The threshold-selector Harper route's positive-block certificate. -/
noncomputable def positiveBlockOmega_harperThresholdSelector :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperThresholdSelectorBlockCertificate
    harperThresholdSelectorBlockCertificate

/-- Erdős #1144 from the threshold-selector Harper-process certificate
axiom. -/
theorem erdos1144_of_harperThresholdSelectorBlockCertificate_axiom :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    positiveBlockOmega_harperThresholdSelector

/-- Temporary threshold-abundance Harper-process input for development.

This is the current active analytic target. It replaces the raw
few-exceedance probability by a finite second-moment abundance estimate for the
large-prime exceedance count, while keeping the good-geometry and
threshold/smooth-overlap estimates explicit. -/
axiom harperThresholdAbundanceCertificate :
  HarperThresholdAbundanceCertificate

/-- The threshold-abundance Harper route's positive-block certificate. -/
noncomputable def positiveBlockOmega_harperThresholdAbundance :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperThresholdAbundanceCertificate
    harperThresholdAbundanceCertificate

/-- Erdős #1144 from the threshold-abundance Harper-process certificate
axiom. -/
theorem erdos1144_of_harperThresholdAbundanceCertificate_axiom :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    positiveBlockOmega_harperThresholdAbundance

/-- The retained threshold-abundance positive-block certificate. The final
theorem below uses the independently proved stationary candidate certificate. -/
noncomputable def positiveBlockOmega : PositiveBlockOmega :=
  positiveBlockOmega_harperThresholdAbundance

/-- Erdős #1144: almost surely, the normalized complete random
multiplicative sums have arbitrarily late positive excursions above every
real threshold. The stationary candidate certificate is fully instantiated. -/
theorem erdos1144 : Erdos1144 := by
  obtain ⟨p, hp, hcertificate⟩ := candidate_scheduledGaussianRobustCrossing_certificate
  exact erdos1144_of_candidateScheduledGaussianRobustCrossing
    (α := 7 / 6) (β := 5 / 4) (κ := 18) (ρ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hp hcertificate

end Problem1144
end Erdos
