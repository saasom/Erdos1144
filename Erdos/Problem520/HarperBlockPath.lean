import Erdos.Problem520.HarperConsecutiveBlocks
import Erdos.Problem520.HarperGaussianWalk

open Finset MeasureTheory ProbabilityTheory Set

namespace Erdos
namespace Problem520

/-!
# The scheduled centered-block path

The coordinate vector of consecutive centered prime blocks has an exact
finite product law.  This module packages the corresponding barrier event
and transports its probability from the tilted prime cube to that product.
-/

noncomputable def harperScheduledCenteredBlockVector
    (y start n : ℕ) (t u : ℝ) :
    HarperPrimeCube y → (Fin n → ℝ) :=
  fun eta j ↦ harperCenteredLinearPrimeBlockSum y
    (harperScheduledPrimeBlock y (start + (j : ℕ))) t u eta

def harperScheduledCenteredBlockSurvivalSet
    (y start n : ℕ) (t u x : ℝ) : Set (HarperPrimeCube y) :=
  {eta | gaussianWalkSurvives n x
    (harperScheduledCenteredBlockVector y start n t u eta)}

theorem measurable_harperScheduledCenteredBlockVector
    (y start n : ℕ) (t u : ℝ) :
    Measurable (harperScheduledCenteredBlockVector y start n t u) := by
  exact measurable_of_finite _

theorem measurableSet_harperScheduledCenteredBlockSurvivalSet
    (y start n : ℕ) (t u : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    MeasurableSet
      (harperScheduledCenteredBlockSurvivalSet y start n t u x) := by
  change MeasurableSet
    ((harperScheduledCenteredBlockVector y start n t u) ⁻¹'
      gaussianWalkSurvivalSet n x)
  exact (measurable_harperScheduledCenteredBlockVector y start n t u)
    (measurableSet_gaussianWalkSurvivalSet n hx)

/-- Exact product-law representation of the centered block-path barrier
probability. -/
theorem measureReal_harperScheduledCenteredBlockSurvivalSet_eq_pi
    (y start n : ℕ) (t u : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (harperTiltedCubeLaw y t).real
        (harperScheduledCenteredBlockSurvivalSet y start n t u x) =
      (Measure.pi (fun j : Fin n ↦
        harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y (start + (j : ℕ))) t u)).real
        (gaussianWalkSurvivalSet n x) := by
  have hmap := map_measureReal_apply
    (μ := harperTiltedCubeLaw y t)
    (measurable_harperScheduledCenteredBlockVector y start n t u)
    (measurableSet_gaussianWalkSurvivalSet n hx)
  have hlaw : Measure.map
      (harperScheduledCenteredBlockVector y start n t u)
      (harperTiltedCubeLaw y t) =
      Measure.pi (fun j : Fin n ↦
        harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y (start + (j : ℕ))) t u) := by
    simpa only [harperScheduledCenteredBlockVector] using
      map_harperScheduledCenteredBlockSums_eq_pi y start n t u
  rw [hlaw] at hmap
  change (harperTiltedCubeLaw y t).real
      ((harperScheduledCenteredBlockVector y start n t u) ⁻¹'
        gaussianWalkSurvivalSet n x) = _
  exact hmap.symm

/-- The terminal partial sum of the block vector is the centered sum over
the entire consecutive prime range. -/
theorem sum_harperScheduledCenteredBlockVector_eq_rangeFrom
    (y start n : ℕ) (t u : ℝ) (eta : HarperPrimeCube y) :
    (∑ j : Fin n, harperScheduledCenteredBlockVector y start n t u eta j) =
      harperCenteredLinearPrimeBlockSum y
        (harperScheduledPrimeRangeFrom y start n) t u eta := by
  unfold harperScheduledCenteredBlockVector
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ ↦ harperCenteredLinearPrimeBlockSum y
      (harperScheduledPrimeBlock y (start + k)) t u eta) n]
  exact sum_harperCenteredLinearPrimeBlockSum_eq_rangeFrom
    y start n t u eta

end Problem520
end Erdos
