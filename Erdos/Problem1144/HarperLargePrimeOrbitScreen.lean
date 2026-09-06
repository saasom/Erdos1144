import Erdos.Problem1144.EndpointSeparationBridge
import Erdos.Problem1144.HarperFreshCoefficientScreen
import Erdos.Problem1144.HarperScreenOrbitMoments

open MeasureTheory
open scoped BigOperators

namespace Erdos
namespace Problem1144

/-!
# Exact finite-orbit screen for the complete large-prime process

In the Harper range `N < X^2`, the complete normalized partial sum splits as

`cutoffNormSum = smoothProcess + largePrimeProcess`.

The first term only uses coordinates at most `X`.  The second is an exact
Rademacher linear form in the primes `p > X`, whose coefficients are also
determined by coordinates at most `X`.  This file applies the finite-orbit
second/fourth-moment theorem directly to that complete-model decomposition.

The final endpoint says that a variance-threshold event of probability
`delta` forces the *original normalized endpoint* to have magnitude at least
`U` with probability at least `delta / 24`.  No lower-tail estimate for the
smooth/old contribution is required: the global fresh-prime flip changes the
sign of the fresh process and fixes the old process, so an arbitrary shift
cannot hide both signs.
-/

/-- In the Harper range, a complete large-prime coefficient is unchanged by
flipping any subset of the visible fresh primes. -/
theorem largePrimeCoeff_freshSignFlip_subset_eq
    (omega : Omega) {X N p : ℕ} (hN : N < X ^ 2)
    (hp : p ∈ largePrimeInterval X N)
    (t : Finset ℕ) (ht : t ⊆ largePrimeInterval X N) :
    largePrimeCoeff (freshSignFlip t omega) X N p =
      largePrimeCoeff omega X N p := by
  apply largePrimeCoeff_freshSignFlip_eq_of_above t omega
    (by simpa [pow_two] using hN) hp
  intro q hqt
  exact (mem_largePrimeInterval.mp (ht hqt)).2.1

/-- On a finite fresh-sign orbit, the complete large-prime process is the
ordinary Rademacher linear form with its complementary-world coefficients
frozen at the orbit base point. -/
theorem largePrimeProcess_freshSignFlip_subset_eq_orbitLinear
    (omega : Omega) {X N : ℕ} (hN : N < X ^ 2)
    (t : Finset ℕ) (ht : t ⊆ largePrimeInterval X N) :
    largePrimeProcess (freshSignFlip t omega) X N =
      orbitLinear (largePrimeInterval X N)
        (fun p => largePrimeCoeff omega X N p) omega t := by
  classical
  rw [largePrimeProcess_eq_sum_coeff]
  unfold orbitLinear epsLinearForm
  apply Finset.sum_congr rfl
  intro p hp
  rw [largePrimeCoeff_freshSignFlip_subset_eq omega hN hp t ht]
  ring

/-- The complete conditional variance is constant on every subset-flip orbit
of its visible fresh-prime coordinates. -/
theorem largePrimeVariance_freshSignFlip_subset_eq
    (omega : Omega) {X N : ℕ} (hN : N < X ^ 2)
    (t : Finset ℕ) (ht : t ⊆ largePrimeInterval X N) :
    largePrimeVariance (freshSignFlip t omega) X N =
      largePrimeVariance omega X N := by
  classical
  unfold largePrimeVariance
  apply Finset.sum_congr rfl
  intro p hp
  rw [largePrimeCoeff_freshSignFlip_subset_eq omega hN hp t ht]

/-- Large-value event for the complete normalized large-prime process. -/
def largePrimeProcessLargeEvent (X N : ℕ) (U : ℝ) : Set Omega :=
  {omega | U ≤ |largePrimeProcess omega X N|}

/-- Orbit-invariant event on which the complete conditional variance is
positive and at least `2 * U^2`. -/
def largePrimeVarianceThresholdEvent (X N : ℕ) (U : ℝ) : Set Omega :=
  {omega |
    0 < largePrimeVariance omega X N ∧
      U ^ 2 ≤ largePrimeVariance omega X N / 2}

theorem measurableSet_largePrimeProcessLargeEvent
    (X N : ℕ) (U : ℝ) :
    MeasurableSet (largePrimeProcessLargeEvent X N U) := by
  exact measurableSet_le measurable_const
    (continuous_abs.measurable.comp (measurable_largePrimeProcess X N))

theorem measurableSet_largePrimeVarianceThresholdEvent
    (X N : ℕ) (U : ℝ) :
    MeasurableSet (largePrimeVarianceThresholdEvent X N U) := by
  exact
    (measurableSet_lt measurable_const (measurable_largePrimeVariance X N)).inter
      (measurableSet_le measurable_const
        ((measurable_largePrimeVariance X N).div_const 2))

theorem largePrimeVarianceThresholdEvent_freshSignFlip_subset_iff
    (omega : Omega) {X N : ℕ} (hN : N < X ^ 2) (U : ℝ)
    (t : Finset ℕ) (ht : t ⊆ largePrimeInterval X N) :
    freshSignFlip t omega ∈ largePrimeVarianceThresholdEvent X N U ↔
      omega ∈ largePrimeVarianceThresholdEvent X N U := by
  unfold largePrimeVarianceThresholdEvent
  simp only [Set.mem_setOf_eq]
  rw [largePrimeVariance_freshSignFlip_subset_eq omega hN t ht]

/-- Fiberwise finite-cube Paley--Zygmund bound for the complete large-prime
process. -/
theorem card_largePrimeProcess_orbit_large_lower
    (omega : Omega) {X N : ℕ} (hN : N < X ^ 2) (U : ℝ)
    (hV : 0 < largePrimeVariance omega X N)
    (hU : U ^ 2 ≤ largePrimeVariance omega X N / 2) :
    ((2 ^ (largePrimeInterval X N).card : ℕ) : ℝ) / 12 ≤
      (((largePrimeInterval X N).powerset.filter fun t =>
        U ≤ |largePrimeProcess (freshSignFlip t omega) X N|).card : ℝ) := by
  let s := largePrimeInterval X N
  let a : ℕ → ℝ := fun p => largePrimeCoeff omega X N p
  have horbit :
      s.powerset.filter (fun t =>
          U ≤ |largePrimeProcess (freshSignFlip t omega) X N|) =
        orbitLargeSet s a omega U := by
    classical
    unfold orbitLargeSet
    ext t
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro htPower
    rw [largePrimeProcess_freshSignFlip_subset_eq_orbitLinear
      omega hN t (Finset.mem_powerset.mp htPower)]
  rw [horbit]
  apply card_orbitLargeSet_lower s a omega U
  · simpa [s, a, largePrimeVariance] using hV
  · simpa [s, a, largePrimeVariance] using hU

/-- Exact ambient-probability form of the complete conditional fresh-screen
bound. -/
theorem measureReal_largePrimeProcessLarge_inter_varianceThreshold_lower
    {X N : ℕ} (hN : N < X ^ 2) (U : ℝ) :
    (1 : ℝ) / 12 *
        mu.real (largePrimeVarianceThresholdEvent X N U) ≤
      mu.real
        (largePrimeVarianceThresholdEvent X N U ∩
          largePrimeProcessLargeEvent X N U) := by
  let s := largePrimeInterval X N
  let G := largePrimeVarianceThresholdEvent X N U
  let E := largePrimeProcessLargeEvent X N U
  apply measureReal_inter_lower_of_orbitEventCount s
    (measurableSet_largePrimeVarianceThresholdEvent X N U)
    (measurableSet_largePrimeProcessLargeEvent X N U)
  · intro t ht omega
    exact
      (largePrimeVarianceThresholdEvent_freshSignFlip_subset_iff
        omega hN U t (Finset.mem_powerset.mp ht)).symm
  · intro omega homega
    have hcard := card_largePrimeProcess_orbit_large_lower
      omega hN U homega.1 homega.2
    have hcount :
        orbitEventCount s E omega =
          (((largePrimeInterval X N).powerset.filter fun t =>
            U ≤ |largePrimeProcess (freshSignFlip t omega) X N|).card : ℝ) := by
      classical
      unfold orbitEventCount E largePrimeProcessLargeEvent s
      rfl
    rw [hcount]
    simpa [div_eq_mul_inv, mul_comm] using hcard

/-- A variance-threshold event of probability `delta` gives a complete
large-prime-process fluctuation with the universal finite-orbit loss `1/12`.
-/
theorem measureReal_largePrimeProcessLarge_lower_of_varianceThreshold
    {X N : ℕ} (hN : N < X ^ 2) (U delta : ℝ)
    (hdelta : delta ≤
      mu.real (largePrimeVarianceThresholdEvent X N U)) :
    delta / 12 ≤ mu.real (largePrimeProcessLargeEvent X N U) := by
  have hinter :=
    measureReal_largePrimeProcessLarge_inter_varianceThreshold_lower hN U
  have hmono :
      mu.real
          (largePrimeVarianceThresholdEvent X N U ∩
            largePrimeProcessLargeEvent X N U) ≤
        mu.real (largePrimeProcessLargeEvent X N U) :=
    measureReal_mono Set.inter_subset_right
  calc
    delta / 12 ≤ (1 : ℝ) / 12 *
        mu.real (largePrimeVarianceThresholdEvent X N U) := by
          nlinarith
    _ ≤ mu.real
        (largePrimeVarianceThresholdEvent X N U ∩
          largePrimeProcessLargeEvent X N U) := hinter
    _ ≤ mu.real (largePrimeProcessLargeEvent X N U) := hmono

/-- The normalized smooth background is fixed by the global visible-fresh
prime flip. -/
theorem smoothProcess_freshSignFlip_largePrimeInterval
    (omega : Omega) (X N : ℕ) :
    smoothProcess (freshSignFlip (largePrimeInterval X N) omega) X N =
      smoothProcess omega X N := by
  unfold smoothProcess
  rw [smoothSum_freshSignFlip_eq_of_above]
  intro p hp
  exact (mem_largePrimeInterval.mp hp).2.1

/-- The complete large-prime process is exactly odd under the global flip of
its visible fresh coordinates. -/
theorem largePrimeProcess_freshSignFlip_largePrimeInterval_eq_neg
    (omega : Omega) {X N : ℕ} (hN : N < X ^ 2) :
    largePrimeProcess (freshSignFlip (largePrimeInterval X N) omega) X N =
      -largePrimeProcess omega X N := by
  rw [largePrimeProcess_freshSignFlip_subset_eq_orbitLinear
    omega hN (largePrimeInterval X N) (by rfl)]
  unfold orbitLinear
  rw [epsLinearForm_freshSignFlip]
  have hlinear :
      epsLinearForm (largePrimeInterval X N)
          (fun p => largePrimeCoeff omega X N p) omega =
        largePrimeProcess omega X N := by
    rw [largePrimeProcess_eq_sum_coeff]
    unfold epsLinearForm
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  rw [hlinear]

/-- Reflection turns a complete large-prime fluctuation into a fluctuation of
the original normalized endpoint, losing only a factor `1/2` and making no
assumption on the old background. -/
theorem measureReal_cutoffNormSum_large_lower_of_largePrimeProcess
    {X N : ℕ} (hN : N < X ^ 2) (U p : ℝ)
    (hfresh : p ≤ mu.real (largePrimeProcessLargeEvent X N U)) :
    p / 2 ≤ mu.real {omega | U ≤ |cutoffNormSum omega N|} := by
  let A : Omega → ℝ := fun omega => smoothProcess omega X N
  let Z : Omega → ℝ := fun omega => largePrimeProcess omega X N
  have hreflect :
      mu.real (shiftedFreshLargeEvent A Z U) =
        mu.real (shiftedFreshReflectedLargeEvent A Z U) :=
    measureReal_shiftedFreshLarge_eq_reflected_of_measurePreserving
      A Z U (freshSignFlip (largePrimeInterval X N))
      (measurePreserving_freshSignFlip (largePrimeInterval X N))
      (fun omega => smoothProcess_freshSignFlip_largePrimeInterval omega X N)
      (fun omega =>
        largePrimeProcess_freshSignFlip_largePrimeInterval_eq_neg omega hN)
  have hlower := measureReal_shiftedFreshLarge_lower_of_freshLarge
    A Z U p hreflect (by simpa [freshLargeEvent, Z] using hfresh)
  simpa [shiftedFreshLargeEvent, A, Z,
    cutoffNormSum_eq_smoothProcess_add_largePrimeProcess _ hN] using hlower

/-- Complete-model endpoint theorem: a positive-probability conditional
variance threshold for the visible primes above `X` forces the original
normalized endpoint itself to be large with probability at least
`delta / 24`. -/
theorem measureReal_cutoffNormSum_large_lower_of_largePrimeVarianceThreshold
    {X N : ℕ} (hN : N < X ^ 2) (U delta : ℝ)
    (hdelta : delta ≤
      mu.real (largePrimeVarianceThresholdEvent X N U)) :
    delta / 24 ≤ mu.real {omega | U ≤ |cutoffNormSum omega N|} := by
  have hfresh :=
    measureReal_largePrimeProcessLarge_lower_of_varianceThreshold
      hN U delta hdelta
  have hendpoint :=
    measureReal_cutoffNormSum_large_lower_of_largePrimeProcess
      hN U (delta / 12) hfresh
  convert hendpoint using 1 <;> ring

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.largePrimeCoeff_freshSignFlip_subset_eq
#print axioms Erdos.Problem1144.card_largePrimeProcess_orbit_large_lower
#print axioms Erdos.Problem1144.measureReal_largePrimeProcessLarge_lower_of_varianceThreshold
#print axioms Erdos.Problem1144.measureReal_cutoffNormSum_large_lower_of_largePrimeVarianceThreshold
