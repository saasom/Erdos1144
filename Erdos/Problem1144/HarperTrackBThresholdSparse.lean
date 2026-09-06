import Erdos.Problem1144.HarperTrackBThresholdAbundance
import Erdos.Problem1144.HarperIncrementOneSidedBridge
import Mathlib.Probability.Moments.Variance

open MeasureTheory Filter
open ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-!
# Sparse Track B threshold-abundance tail package

`HarperTrackBThresholdAbundance` is the final sparse Track B bridge: it turns
many abstract core exceedances, plus a selected-remainder overlap estimate,
into positive blocks.  This file adds the finite probability adapter expected
from the analytic sparse-core estimates.

The analytic package should usually prove one-point and two-point tail bounds
for the sparse core.  The lemmas below expand the exceedance count into finite
sums of indicators, convert those tail bounds into the first and raw second
moments of the count, and then use the existing Chebyshev spine.
-/

/-- One-point exceedance event for the abstract Track B threshold core. -/
def trackBThresholdExceedanceEvent
    (core : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (j N : ℕ) : Set Omega :=
  {omega | M j + buffer j ≤ core omega j N}

/-- Pair exceedance event for the abstract Track B threshold core. -/
def trackBThresholdPairExceedanceEvent
    (core : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (j N N' : ℕ) : Set Omega :=
  trackBThresholdExceedanceEvent core M buffer j N ∩
    trackBThresholdExceedanceEvent core M buffer j N'

/-- Indicator of a one-point sparse Track B threshold exceedance. -/
noncomputable def trackBThresholdExceedanceIndicator
    (core : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (j N : ℕ) : Omega → ℝ :=
  (trackBThresholdExceedanceEvent core M buffer j N).indicator
    (fun _ : Omega => (1 : ℝ))

theorem measurableSet_trackBThresholdPairExceedanceEvent
    (core : Omega → ℕ → ℕ → ℝ) (M buffer : ℕ → ℝ)
    (hmeas :
      ∀ j N, MeasurableSet
        (trackBThresholdExceedanceEvent core M buffer j N))
    (j N N' : ℕ) :
    MeasurableSet
      (trackBThresholdPairExceedanceEvent core M buffer j N N') := by
  exact (hmeas j N).inter (hmeas j N')

/-- The integral of one threshold indicator is the event probability. -/
theorem integral_trackBThresholdExceedanceIndicator
    (core : Omega → ℕ → ℕ → ℝ) (M buffer : ℕ → ℝ)
    (hmeas :
      ∀ j N, MeasurableSet
        (trackBThresholdExceedanceEvent core M buffer j N))
    (j N : ℕ) :
    (∫ omega,
      trackBThresholdExceedanceIndicator core M buffer j N omega ∂mu)
      =
    mu.real (trackBThresholdExceedanceEvent core M buffer j N) := by
  exact MeasureTheory.integral_indicator_one (hmeas j N)

/-- The product of two threshold indicators is the pair-event indicator. -/
theorem trackBThresholdExceedanceIndicator_mul
    (core : Omega → ℕ → ℕ → ℝ) (M buffer : ℕ → ℝ)
    (j N N' : ℕ) :
    (fun omega =>
      trackBThresholdExceedanceIndicator core M buffer j N omega *
        trackBThresholdExceedanceIndicator core M buffer j N' omega)
      =
    (trackBThresholdPairExceedanceEvent core M buffer j N N').indicator
      (fun _ : Omega => (1 : ℝ)) := by
  funext omega
  by_cases hN :
      omega ∈ trackBThresholdExceedanceEvent core M buffer j N
  · by_cases hN' :
      omega ∈ trackBThresholdExceedanceEvent core M buffer j N'
    · have hpair :
          omega ∈ trackBThresholdPairExceedanceEvent core M buffer j N N' :=
        ⟨hN, hN'⟩
      simp [trackBThresholdExceedanceIndicator, hN, hN', hpair]
    · have hpair :
          omega ∉ trackBThresholdPairExceedanceEvent core M buffer j N N' := by
        intro h
        exact hN' h.2
      simp [trackBThresholdExceedanceIndicator, hN, hN', hpair]
  · have hpair :
        omega ∉ trackBThresholdPairExceedanceEvent core M buffer j N N' := by
      intro h
      exact hN h.1
    simp [trackBThresholdExceedanceIndicator, hN, hpair]

/-- The integral of a product of threshold indicators is the pair-event
probability. -/
theorem integral_trackBThresholdExceedanceIndicator_mul
    (core : Omega → ℕ → ℕ → ℝ) (M buffer : ℕ → ℝ)
    (hmeas :
      ∀ j N, MeasurableSet
        (trackBThresholdExceedanceEvent core M buffer j N))
    (j N N' : ℕ) :
    (∫ omega,
      trackBThresholdExceedanceIndicator core M buffer j N omega *
        trackBThresholdExceedanceIndicator core M buffer j N' omega ∂mu)
      =
    mu.real (trackBThresholdPairExceedanceEvent core M buffer j N N') := by
  rw [trackBThresholdExceedanceIndicator_mul]
  exact
    MeasureTheory.integral_indicator_one
      (measurableSet_trackBThresholdPairExceedanceEvent
        core M buffer hmeas j N N')

/-- Threshold indicators are square-integrable. -/
theorem memLp_trackBThresholdExceedanceIndicator
    (core : Omega → ℕ → ℕ → ℝ) (M buffer : ℕ → ℝ)
    (hmeas :
      ∀ j N, MeasurableSet
        (trackBThresholdExceedanceEvent core M buffer j N))
    (j N : ℕ) :
    MemLp (trackBThresholdExceedanceIndicator core M buffer j N) 2 mu := by
  exact
    (memLp_const (1 : ℝ)).indicator (hmeas j N)

/-- Diagonal covariance of a threshold indicator is bounded by its
probability, hence by any supplied one-point upper bound. -/
theorem covariance_trackBThresholdExceedanceIndicator_self_le
    (core : Omega → ℕ → ℕ → ℝ) (M buffer : ℕ → ℝ)
    (hmeas :
      ∀ j N, MeasurableSet
        (trackBThresholdExceedanceEvent core M buffer j N))
    (j N : ℕ) (tailUpper : ℝ)
    (htail :
      mu.real (trackBThresholdExceedanceEvent core M buffer j N) ≤
        tailUpper) :
    cov[
        trackBThresholdExceedanceIndicator core M buffer j N,
        trackBThresholdExceedanceIndicator core M buffer j N;
        mu]
      ≤ tailUpper := by
  let I := trackBThresholdExceedanceIndicator core M buffer j N
  let E := trackBThresholdExceedanceEvent core M buffer j N
  have hmem : MemLp I 2 mu :=
    memLp_trackBThresholdExceedanceIndicator core M buffer hmeas j N
  have hcov :
      cov[I, I; mu] =
        mu.real E - mu.real E * mu.real E := by
    rw [ProbabilityTheory.covariance_eq_sub hmem hmem]
    simp only [I, E, Pi.mul_apply]
    change
      (∫ omega,
        trackBThresholdExceedanceIndicator core M buffer j N omega *
          trackBThresholdExceedanceIndicator core M buffer j N omega ∂mu) -
        (∫ omega, trackBThresholdExceedanceIndicator core M buffer j N omega ∂mu) *
          ∫ omega, trackBThresholdExceedanceIndicator core M buffer j N omega ∂mu =
        mu.real (trackBThresholdExceedanceEvent core M buffer j N) -
          mu.real (trackBThresholdExceedanceEvent core M buffer j N) *
            mu.real (trackBThresholdExceedanceEvent core M buffer j N)
    rw [integral_trackBThresholdExceedanceIndicator_mul
      core M buffer hmeas j N N]
    rw [integral_trackBThresholdExceedanceIndicator
      core M buffer hmeas j N]
    simp [trackBThresholdPairExceedanceEvent]
  have hprod_nonneg : 0 ≤ mu.real E * mu.real E :=
    mul_nonneg measureReal_nonneg measureReal_nonneg
  calc
    cov[I, I; mu] = mu.real E - mu.real E * mu.real E := hcov
    _ ≤ mu.real E := by linarith
    _ ≤ tailUpper := htail

/-- Off-diagonal covariance bound from a pair-probability covariance bound. -/
theorem covariance_trackBThresholdExceedanceIndicator_le_of_pairCov
    (core : Omega → ℕ → ℕ → ℝ) (M buffer : ℕ → ℝ)
    (hmeas :
      ∀ j N, MeasurableSet
        (trackBThresholdExceedanceEvent core M buffer j N))
    (j N N' : ℕ) (pairCovUpper : ℝ)
    (hpair :
      mu.real (trackBThresholdPairExceedanceEvent core M buffer j N N') -
          mu.real (trackBThresholdExceedanceEvent core M buffer j N) *
            mu.real (trackBThresholdExceedanceEvent core M buffer j N')
        ≤ pairCovUpper) :
    cov[
        trackBThresholdExceedanceIndicator core M buffer j N,
        trackBThresholdExceedanceIndicator core M buffer j N';
        mu]
      ≤ pairCovUpper := by
  let I := trackBThresholdExceedanceIndicator core M buffer j N
  let I' := trackBThresholdExceedanceIndicator core M buffer j N'
  have hmem : MemLp I 2 mu :=
    memLp_trackBThresholdExceedanceIndicator core M buffer hmeas j N
  have hmem' : MemLp I' 2 mu :=
    memLp_trackBThresholdExceedanceIndicator core M buffer hmeas j N'
  have hcov :
      cov[I, I'; mu] =
        mu.real (trackBThresholdPairExceedanceEvent core M buffer j N N') -
          mu.real (trackBThresholdExceedanceEvent core M buffer j N) *
            mu.real (trackBThresholdExceedanceEvent core M buffer j N') := by
    rw [ProbabilityTheory.covariance_eq_sub hmem hmem']
    simp only [I, I', Pi.mul_apply]
    change
      (∫ omega,
        trackBThresholdExceedanceIndicator core M buffer j N omega *
          trackBThresholdExceedanceIndicator core M buffer j N' omega ∂mu) -
        (∫ omega, trackBThresholdExceedanceIndicator core M buffer j N omega ∂mu) *
          ∫ omega, trackBThresholdExceedanceIndicator core M buffer j N' omega ∂mu =
        mu.real (trackBThresholdPairExceedanceEvent core M buffer j N N') -
          mu.real (trackBThresholdExceedanceEvent core M buffer j N) *
            mu.real (trackBThresholdExceedanceEvent core M buffer j N')
    rw [integral_trackBThresholdExceedanceIndicator_mul
      core M buffer hmeas j N N']
    rw [integral_trackBThresholdExceedanceIndicator
      core M buffer hmeas j N]
    rw [integral_trackBThresholdExceedanceIndicator
      core M buffer hmeas j N']
  rw [hcov]
  exact hpair

/-- Pointwise expansion of the abstract Track B threshold exceedance count as
a finite sum of event indicators. -/
theorem trackBThresholdExceedanceCountReal_eq_sum_indicator
    (testSet : ℕ → Finset ℕ)
    (core : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (j : ℕ) (omega : Omega) :
    trackBThresholdExceedanceCountReal testSet core M buffer j omega =
      ∑ N ∈ testSet j,
        (trackBThresholdExceedanceEvent core M buffer j N).indicator
          (fun _ : Omega => (1 : ℝ)) omega := by
  classical
  unfold trackBThresholdExceedanceCountReal trackBThresholdExceedanceSet
  rw [Finset.card_filter]
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun N hN => ?_
  by_cases h : M j + buffer j ≤ core omega j N
  · simp [trackBThresholdExceedanceEvent, h]
  · simp [trackBThresholdExceedanceEvent, h]

/-- Pointwise square expansion of the abstract Track B threshold exceedance
count as a double sum of pair-event indicators. -/
theorem trackBThresholdExceedanceCountReal_sq_eq_sum_pair_indicator
    (testSet : ℕ → Finset ℕ)
    (core : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ) (j : ℕ) (omega : Omega) :
    (trackBThresholdExceedanceCountReal testSet core M buffer j omega) ^ 2 =
      ∑ N ∈ testSet j, ∑ N' ∈ testSet j,
        (trackBThresholdPairExceedanceEvent core M buffer j N N').indicator
          (fun _ : Omega => (1 : ℝ)) omega := by
  classical
  rw [trackBThresholdExceedanceCountReal_eq_sum_indicator]
  rw [pow_two, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun N hN => ?_
  refine Finset.sum_congr rfl fun N' hN' => ?_
  by_cases hNω :
      omega ∈ trackBThresholdExceedanceEvent core M buffer j N
  · by_cases hN'ω :
        omega ∈ trackBThresholdExceedanceEvent core M buffer j N'
    · simp [trackBThresholdPairExceedanceEvent, hNω, hN'ω]
    · simp [trackBThresholdPairExceedanceEvent, hNω, hN'ω]
  · simp [trackBThresholdPairExceedanceEvent, hNω]

/-- Integrability of the abstract threshold exceedance count. -/
theorem integrable_trackBThresholdExceedanceCountReal
    (testSet : ℕ → Finset ℕ)
    (core : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ)
    (hmeas :
      ∀ j N, MeasurableSet
        (trackBThresholdExceedanceEvent core M buffer j N))
    (j : ℕ) :
    Integrable
      (trackBThresholdExceedanceCountReal testSet core M buffer j)
      mu := by
  classical
  rw [show
      trackBThresholdExceedanceCountReal testSet core M buffer j =
        fun omega =>
          ∑ N ∈ testSet j,
            (trackBThresholdExceedanceEvent core M buffer j N).indicator
              (fun _ : Omega => (1 : ℝ)) omega by
        funext omega
        exact trackBThresholdExceedanceCountReal_eq_sum_indicator
          testSet core M buffer j omega]
  refine integrable_finset_sum (testSet j) ?_
  intro N hN
  exact (integrable_const (1 : ℝ)).indicator (hmeas j N)

/-- Integrability of the square of the abstract threshold exceedance count. -/
theorem integrable_trackBThresholdExceedanceCountReal_sq
    (testSet : ℕ → Finset ℕ)
    (core : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ)
    (hmeas :
      ∀ j N, MeasurableSet
        (trackBThresholdExceedanceEvent core M buffer j N))
    (j : ℕ) :
    Integrable
      (fun omega =>
        (trackBThresholdExceedanceCountReal
          testSet core M buffer j omega) ^ 2)
      mu := by
  classical
  rw [show
      (fun omega =>
        (trackBThresholdExceedanceCountReal
          testSet core M buffer j omega) ^ 2) =
        fun omega =>
          ∑ N ∈ testSet j, ∑ N' ∈ testSet j,
            (trackBThresholdPairExceedanceEvent core M buffer j N N').indicator
              (fun _ : Omega => (1 : ℝ)) omega by
        funext omega
        exact trackBThresholdExceedanceCountReal_sq_eq_sum_pair_indicator
          testSet core M buffer j omega]
  refine integrable_finset_sum (testSet j) ?_
  intro N hN
  refine integrable_finset_sum (testSet j) ?_
  intro N' hN'
  exact
    (integrable_const (1 : ℝ)).indicator
      (measurableSet_trackBThresholdPairExceedanceEvent
        core M buffer hmeas j N N')

/-- First-moment identity for the abstract threshold exceedance count. -/
theorem integral_trackBThresholdExceedanceCountReal
    (testSet : ℕ → Finset ℕ)
    (core : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ)
    (hmeas :
      ∀ j N, MeasurableSet
        (trackBThresholdExceedanceEvent core M buffer j N))
    (j : ℕ) :
    (∫ omega,
      trackBThresholdExceedanceCountReal
        testSet core M buffer j omega ∂mu)
      =
    ∑ N ∈ testSet j,
      mu.real (trackBThresholdExceedanceEvent core M buffer j N) := by
  classical
  rw [show
      (fun omega =>
        trackBThresholdExceedanceCountReal
          testSet core M buffer j omega) =
        fun omega =>
          ∑ N ∈ testSet j,
            (trackBThresholdExceedanceEvent core M buffer j N).indicator
              (fun _ : Omega => (1 : ℝ)) omega by
        funext omega
        exact trackBThresholdExceedanceCountReal_eq_sum_indicator
          testSet core M buffer j omega]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun N hN => ?_
    exact MeasureTheory.integral_indicator_one (hmeas j N)
  · intro N hN
    exact (integrable_const (1 : ℝ)).indicator (hmeas j N)

/-- Raw second-moment identity for the abstract threshold exceedance count. -/
theorem integral_trackBThresholdExceedanceCountReal_sq
    (testSet : ℕ → Finset ℕ)
    (core : Omega → ℕ → ℕ → ℝ)
    (M buffer : ℕ → ℝ)
    (hmeas :
      ∀ j N, MeasurableSet
        (trackBThresholdExceedanceEvent core M buffer j N))
    (j : ℕ) :
    (∫ omega,
      (trackBThresholdExceedanceCountReal
        testSet core M buffer j omega) ^ 2 ∂mu)
      =
    ∑ N ∈ testSet j, ∑ N' ∈ testSet j,
      mu.real (trackBThresholdPairExceedanceEvent core M buffer j N N') := by
  classical
  rw [show
      (fun omega =>
        (trackBThresholdExceedanceCountReal
          testSet core M buffer j omega) ^ 2) =
        fun omega =>
          ∑ N ∈ testSet j, ∑ N' ∈ testSet j,
            (trackBThresholdPairExceedanceEvent core M buffer j N N').indicator
              (fun _ : Omega => (1 : ℝ)) omega by
        funext omega
        exact trackBThresholdExceedanceCountReal_sq_eq_sum_pair_indicator
          testSet core M buffer j omega]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun N hN => ?_
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun N' hN' => ?_
      exact
        MeasureTheory.integral_indicator_one
          (measurableSet_trackBThresholdPairExceedanceEvent
            core M buffer hmeas j N N')
    · intro N' hN'
      exact
        (integrable_const (1 : ℝ)).indicator
          (measurableSet_trackBThresholdPairExceedanceEvent
            core M buffer hmeas j N N')
  · intro N hN
    refine integrable_finset_sum (testSet j) ?_
    intro N' hN'
    exact
      (integrable_const (1 : ℝ)).indicator
        (measurableSet_trackBThresholdPairExceedanceEvent
          core M buffer hmeas j N N')

/-- Centered-square integrability from first and second moment integrability. -/
theorem integrable_centered_square_of_integrable_sq
    (D : Omega → ℝ)
    (hD_int : Integrable D mu)
    (hD2_int : Integrable (fun omega => D omega ^ 2) mu) :
    Integrable
      (fun omega => (D omega - ∫ omega', D omega' ∂mu) ^ 2)
      mu := by
  let m : ℝ := ∫ omega, D omega ∂mu
  have hmajor_int :
      Integrable (fun omega => 2 * (D omega ^ 2 + m ^ 2)) mu := by
    exact (hD2_int.add (integrable_const (m ^ 2))).const_mul 2
  refine Integrable.mono' hmajor_int ?_ ?_
  · exact
      (((hD_int.sub (integrable_const m)).aemeasurable.pow_const 2).aestronglyMeasurable)
  · filter_upwards [] with omega
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (D omega - m) ^ 2)]
    nlinarith [sq_nonneg (D omega - m), sq_nonneg (D omega + m)]

/-- One- and two-point tail probability package for the sparse Track B
threshold core. -/
structure TrackBThresholdTailProbabilityCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  core : Omega → ℕ → ℕ → ℝ
  remainder : Omega → ℕ → ℕ → ℝ
  good : ℕ → Set Omega
  r : ℕ → ℕ
  failGood : ℕ → ℝ≥0∞
  failOverlap : ℕ → ℝ≥0∞
  tailLower : ℕ → ℕ → ℝ
  pairUpper : ℕ → ℕ → ℕ → ℝ
  countMean : ℕ → ℝ
  countRawSecond : ℕ → ℝ
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  absorb :
    ∀ omega j N, N ∈ testSet j →
      M j + buffer j ≤ core omega j N →
      -buffer j ≤ remainder omega j N →
      M j ≤ normSum omega N
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  exceedance_measurable :
    ∀ j N, MeasurableSet
      (trackBThresholdExceedanceEvent core M buffer j N)
  countMean_le_tailLower_sum :
    ∀ j,
      countMean j ≤
        ∑ N ∈ testSet j, tailLower j N
  pairUpper_sum_le_countRawSecond :
    ∀ j,
      (∑ N ∈ testSet j, ∑ N' ∈ testSet j, pairUpper j N N')
        ≤ countRawSecond j
  tailLower_le_prob :
    ∀ (j N : ℕ), N ∈ testSet j →
      tailLower j N ≤
        mu.real (trackBThresholdExceedanceEvent core M buffer j N)
  pair_prob_le_pairUpper :
    ∀ (j N N' : ℕ), N ∈ testSet j → N' ∈ testSet j →
      mu.real (trackBThresholdPairExceedanceEvent core M buffer j N N')
        ≤ pairUpper j N N'
  fail_summable :
    (∑' j,
      (failGood j +
        ENNReal.ofReal (4 * (4 * countRawSecond j) / countMean j ^ 2) +
        failOverlap j)) ≠ ⊤
  prob_good_compl :
    ∀ j, mu (good j)ᶜ ≤ failGood j
  prob_overlap_many :
    ∀ j,
      mu
          (trackBThresholdOverlapMany testSet core remainder M buffer r j) ≤
        failOverlap j

/-- Tail-probability packages specialize to the final sparse threshold
abundance certificate. -/
noncomputable def trackBThresholdAbundanceCertificate_of_tailProbability
    (h : TrackBThresholdTailProbabilityCertificate) :
    TrackBThresholdAbundanceCertificate where
  lo := h.lo
  hi := h.hi
  M := h.M
  buffer := h.buffer
  testSet := h.testSet
  core := h.core
  remainder := h.remainder
  good := h.good
  r := h.r
  failGood := h.failGood
  failOverlap := h.failOverlap
  countMean := h.countMean
  countSecond := fun j => 4 * h.countRawSecond j
  r_pos := h.r_pos
  countMean_pos := h.countMean_pos
  r_le_half_countMean := h.r_le_half_countMean
  testSet_in_block := h.testSet_in_block
  absorb := h.absorb
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  count_centered_second_integrable := by
    intro j
    let D : Omega → ℝ :=
      trackBThresholdExceedanceCountReal h.testSet h.core h.M h.buffer j
    exact
      integrable_centered_square_of_integrable_sq
        (D := D)
        (integrable_trackBThresholdExceedanceCountReal
          h.testSet h.core h.M h.buffer h.exceedance_measurable j)
        (integrable_trackBThresholdExceedanceCountReal_sq
          h.testSet h.core h.M h.buffer h.exceedance_measurable j)
  count_mean_lower := by
    intro j
    calc
      h.countMean j
          ≤ ∑ N ∈ h.testSet j, h.tailLower j N :=
            h.countMean_le_tailLower_sum j
      _ ≤
          ∑ N ∈ h.testSet j,
            mu.real
              (trackBThresholdExceedanceEvent h.core h.M h.buffer j N) := by
            refine Finset.sum_le_sum fun N hN => ?_
            exact h.tailLower_le_prob j N hN
      _ =
          ∫ omega,
            trackBThresholdExceedanceCountReal
              h.testSet h.core h.M h.buffer j omega ∂mu := by
            exact
              (integral_trackBThresholdExceedanceCountReal
                h.testSet h.core h.M h.buffer h.exceedance_measurable j).symm
  count_centered_second_upper := by
    intro j
    let D : Omega → ℝ :=
      trackBThresholdExceedanceCountReal h.testSet h.core h.M h.buffer j
    have hraw :
        (∫ omega, D omega ^ 2 ∂mu) ≤ h.countRawSecond j := by
      calc
        (∫ omega, D omega ^ 2 ∂mu)
            =
            ∑ N ∈ h.testSet j, ∑ N' ∈ h.testSet j,
              mu.real
                (trackBThresholdPairExceedanceEvent
                  h.core h.M h.buffer j N N') :=
              integral_trackBThresholdExceedanceCountReal_sq
                h.testSet h.core h.M h.buffer h.exceedance_measurable j
        _ ≤
            ∑ N ∈ h.testSet j, ∑ N' ∈ h.testSet j,
              h.pairUpper j N N' := by
              refine Finset.sum_le_sum fun N hN => ?_
              refine Finset.sum_le_sum fun N' hN' => ?_
              exact h.pair_prob_le_pairUpper j N N' hN hN'
        _ ≤ h.countRawSecond j :=
              h.pairUpper_sum_le_countRawSecond j
    calc
      (∫ omega,
          (D omega - ∫ omega', D omega' ∂mu) ^ 2 ∂mu)
          ≤ 4 * ∫ omega, D omega ^ 2 ∂mu :=
            centered_second_le_four_raw_second
              (D := D)
              (integrable_trackBThresholdExceedanceCountReal
                h.testSet h.core h.M h.buffer h.exceedance_measurable j)
              (integrable_trackBThresholdExceedanceCountReal_sq
                h.testSet h.core h.M h.buffer h.exceedance_measurable j)
      _ ≤ 4 * h.countRawSecond j := by
            exact mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 4)
  fail_summable := h.fail_summable
  prob_good_compl := h.prob_good_compl
  prob_overlap_many := h.prob_overlap_many

/-- Direct closure from a pointwise sparse tail-probability package. -/
theorem erdos1144_of_trackBThresholdTailProbabilityCertificate
    (h : TrackBThresholdTailProbabilityCertificate) :
    Erdos1144 :=
  erdos1144_of_trackBThresholdAbundanceCertificate
    (trackBThresholdAbundanceCertificate_of_tailProbability h)

/-- Uniform sparse threshold tail package.  This is the shape expected from
the schedule in `notes/1144/Block_theorem.md`: a common one-point lower tail,
a diagonal one-point upper tail, and a common off-diagonal pair upper tail. -/
structure TrackBThresholdUniformTailProbabilityCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  core : Omega → ℕ → ℕ → ℝ
  remainder : Omega → ℕ → ℕ → ℝ
  good : ℕ → Set Omega
  r : ℕ → ℕ
  failGood : ℕ → ℝ≥0∞
  failOverlap : ℕ → ℝ≥0∞
  beta : ℕ → ℝ
  tailUpper : ℕ → ℝ
  pairUpper : ℕ → ℝ
  countMean : ℕ → ℝ
  countRawSecond : ℕ → ℝ
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  absorb :
    ∀ omega j N, N ∈ testSet j →
      M j + buffer j ≤ core omega j N →
      -buffer j ≤ remainder omega j N →
      M j ≤ normSum omega N
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  exceedance_measurable :
    ∀ j N, MeasurableSet
      (trackBThresholdExceedanceEvent core M buffer j N)
  countMean_le_beta_sum :
    ∀ j,
      countMean j ≤
        ∑ _N ∈ testSet j, beta j
  pairBudget_le_countRawSecond :
    ∀ j,
      (∑ N ∈ testSet j, ∑ N' ∈ testSet j,
        if N = N' then tailUpper j else pairUpper j)
        ≤ countRawSecond j
  beta_le_tail_prob :
    ∀ (j N : ℕ), N ∈ testSet j →
      beta j ≤
        mu.real (trackBThresholdExceedanceEvent core M buffer j N)
  tail_prob_le_tailUpper :
    ∀ (j N : ℕ), N ∈ testSet j →
      mu.real (trackBThresholdExceedanceEvent core M buffer j N)
        ≤ tailUpper j
  offdiag_pair_prob_le_pairUpper :
    ∀ (j N N' : ℕ), N ∈ testSet j → N' ∈ testSet j → N ≠ N' →
      mu.real (trackBThresholdPairExceedanceEvent core M buffer j N N')
        ≤ pairUpper j
  fail_summable :
    (∑' j,
      (failGood j +
        ENNReal.ofReal (4 * (4 * countRawSecond j) / countMean j ^ 2) +
        failOverlap j)) ≠ ⊤
  prob_good_compl :
    ∀ j, mu (good j)ᶜ ≤ failGood j
  prob_overlap_many :
    ∀ j,
      mu
          (trackBThresholdOverlapMany testSet core remainder M buffer r j) ≤
        failOverlap j

/-- Uniform tail packages imply the non-uniform sparse tail package. -/
noncomputable def trackBThresholdTailProbabilityCertificate_of_uniform
    (h : TrackBThresholdUniformTailProbabilityCertificate) :
    TrackBThresholdTailProbabilityCertificate where
  lo := h.lo
  hi := h.hi
  M := h.M
  buffer := h.buffer
  testSet := h.testSet
  core := h.core
  remainder := h.remainder
  good := h.good
  r := h.r
  failGood := h.failGood
  failOverlap := h.failOverlap
  tailLower := fun j _N => h.beta j
  pairUpper := fun j N N' =>
    if N = N' then h.tailUpper j else h.pairUpper j
  countMean := h.countMean
  countRawSecond := h.countRawSecond
  r_pos := h.r_pos
  countMean_pos := h.countMean_pos
  r_le_half_countMean := h.r_le_half_countMean
  testSet_in_block := h.testSet_in_block
  absorb := h.absorb
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  exceedance_measurable := h.exceedance_measurable
  countMean_le_tailLower_sum := h.countMean_le_beta_sum
  pairUpper_sum_le_countRawSecond := h.pairBudget_le_countRawSecond
  tailLower_le_prob := h.beta_le_tail_prob
  pair_prob_le_pairUpper := by
    intro j N N' hN hN'
    by_cases hEq : N = N'
    · subst N'
      have hsubset :
          trackBThresholdPairExceedanceEvent h.core h.M h.buffer j N N ⊆
            trackBThresholdExceedanceEvent h.core h.M h.buffer j N := by
        intro omega homega
        exact homega.1
      have hdiag :
          mu.real
              (trackBThresholdPairExceedanceEvent h.core h.M h.buffer j N N)
            ≤
          mu.real
              (trackBThresholdExceedanceEvent h.core h.M h.buffer j N) :=
        measureReal_mono hsubset
      simpa using hdiag.trans (h.tail_prob_le_tailUpper j N hN)
    · simpa [hEq] using h.offdiag_pair_prob_le_pairUpper j N N' hN hN' hEq
  fail_summable := h.fail_summable
  prob_good_compl := h.prob_good_compl
  prob_overlap_many := h.prob_overlap_many

/-- Uniform sparse tail packages are enough for Erdős #1144 through the active
Track B threshold-abundance bridge. -/
theorem erdos1144_of_trackBThresholdUniformTailProbabilityCertificate
    (h : TrackBThresholdUniformTailProbabilityCertificate) :
    Erdos1144 :=
  erdos1144_of_trackBThresholdAbundanceCertificate
    (trackBThresholdAbundanceCertificate_of_tailProbability
      (trackBThresholdTailProbabilityCertificate_of_uniform h))

/-- Uniform sparse threshold package using centered indicator covariance
bounds instead of a raw second moment.  This is the adapter needed for the
Track B constant-tail schedule: diagonal terms are controlled by one-point
upper bounds, and off-diagonal terms by centered pair covariance errors. -/
structure TrackBThresholdUniformCovarianceTailCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  core : Omega → ℕ → ℕ → ℝ
  remainder : Omega → ℕ → ℕ → ℝ
  good : ℕ → Set Omega
  r : ℕ → ℕ
  failGood : ℕ → ℝ≥0∞
  failOverlap : ℕ → ℝ≥0∞
  beta : ℕ → ℝ
  tailUpper : ℕ → ℝ
  pairCovUpper : ℕ → ℝ
  countMean : ℕ → ℝ
  countSecond : ℕ → ℝ
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  absorb :
    ∀ omega j N, N ∈ testSet j →
      M j + buffer j ≤ core omega j N →
      -buffer j ≤ remainder omega j N →
      M j ≤ normSum omega N
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  exceedance_measurable :
    ∀ j N, MeasurableSet
      (trackBThresholdExceedanceEvent core M buffer j N)
  countMean_le_beta_sum :
    ∀ j,
      countMean j ≤
        ∑ _N ∈ testSet j, beta j
  covarianceBudget_le_countSecond :
    ∀ j,
      (∑ N ∈ testSet j, ∑ N' ∈ testSet j,
        if N = N' then tailUpper j else pairCovUpper j)
        ≤ countSecond j
  beta_le_tail_prob :
    ∀ (j N : ℕ), N ∈ testSet j →
      beta j ≤
        mu.real (trackBThresholdExceedanceEvent core M buffer j N)
  tail_prob_le_tailUpper :
    ∀ (j N : ℕ), N ∈ testSet j →
      mu.real (trackBThresholdExceedanceEvent core M buffer j N)
        ≤ tailUpper j
  offdiag_pair_cov_le_pairCovUpper :
    ∀ (j N N' : ℕ), N ∈ testSet j → N' ∈ testSet j → N ≠ N' →
      mu.real (trackBThresholdPairExceedanceEvent core M buffer j N N') -
          mu.real (trackBThresholdExceedanceEvent core M buffer j N) *
            mu.real (trackBThresholdExceedanceEvent core M buffer j N')
        ≤ pairCovUpper j
  fail_summable :
    (∑' j,
      (failGood j +
        ENNReal.ofReal (4 * countSecond j / countMean j ^ 2) +
        failOverlap j)) ≠ ⊤
  prob_good_compl :
    ∀ j, mu (good j)ᶜ ≤ failGood j
  prob_overlap_many :
    ∀ j,
      mu
          (trackBThresholdOverlapMany testSet core remainder M buffer r j) ≤
        failOverlap j

/-- Centered covariance tail packages specialize directly to the sparse
threshold-abundance certificate. -/
noncomputable def trackBThresholdAbundanceCertificate_of_covarianceTail
    (h : TrackBThresholdUniformCovarianceTailCertificate) :
    TrackBThresholdAbundanceCertificate where
  lo := h.lo
  hi := h.hi
  M := h.M
  buffer := h.buffer
  testSet := h.testSet
  core := h.core
  remainder := h.remainder
  good := h.good
  r := h.r
  failGood := h.failGood
  failOverlap := h.failOverlap
  countMean := h.countMean
  countSecond := h.countSecond
  r_pos := h.r_pos
  countMean_pos := h.countMean_pos
  r_le_half_countMean := h.r_le_half_countMean
  testSet_in_block := h.testSet_in_block
  absorb := h.absorb
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  count_centered_second_integrable := by
    intro j
    let D : Omega → ℝ :=
      trackBThresholdExceedanceCountReal h.testSet h.core h.M h.buffer j
    exact
      integrable_centered_square_of_integrable_sq
        (D := D)
        (integrable_trackBThresholdExceedanceCountReal
          h.testSet h.core h.M h.buffer h.exceedance_measurable j)
        (integrable_trackBThresholdExceedanceCountReal_sq
          h.testSet h.core h.M h.buffer h.exceedance_measurable j)
  count_mean_lower := by
    intro j
    calc
      h.countMean j
          ≤ ∑ N ∈ h.testSet j, h.beta j :=
            h.countMean_le_beta_sum j
      _ ≤
          ∑ N ∈ h.testSet j,
            mu.real
              (trackBThresholdExceedanceEvent h.core h.M h.buffer j N) := by
            refine Finset.sum_le_sum fun N hN => ?_
            exact h.beta_le_tail_prob j N hN
      _ =
          ∫ omega,
            trackBThresholdExceedanceCountReal
              h.testSet h.core h.M h.buffer j omega ∂mu := by
            exact
              (integral_trackBThresholdExceedanceCountReal
                h.testSet h.core h.M h.buffer h.exceedance_measurable j).symm
  count_centered_second_upper := by
    intro j
    let D : Omega → ℝ :=
      trackBThresholdExceedanceCountReal h.testSet h.core h.M h.buffer j
    let I : ℕ → Omega → ℝ :=
      fun N => trackBThresholdExceedanceIndicator h.core h.M h.buffer j N
    have hDae : AEMeasurable D mu :=
      (integrable_trackBThresholdExceedanceCountReal
        h.testSet h.core h.M h.buffer h.exceedance_measurable j).aemeasurable
    calc
      (∫ omega, (D omega - ∫ omega', D omega' ∂mu) ^ 2 ∂mu)
          =
          Var[D; mu] := by
            exact (ProbabilityTheory.variance_eq_integral hDae).symm
      _ =
          Var[(fun omega => ∑ N ∈ h.testSet j, I N omega); mu] := by
            congr 1
            funext omega
            exact
              trackBThresholdExceedanceCountReal_eq_sum_indicator
                h.testSet h.core h.M h.buffer j omega
      _ =
          ∑ N ∈ h.testSet j, ∑ N' ∈ h.testSet j,
            cov[I N, I N'; mu] := by
            exact
              ProbabilityTheory.variance_fun_sum'
                (μ := mu) (s := h.testSet j) (X := I)
                (fun N hN =>
                  memLp_trackBThresholdExceedanceIndicator
                    h.core h.M h.buffer h.exceedance_measurable j N)
      _ ≤
          ∑ N ∈ h.testSet j, ∑ N' ∈ h.testSet j,
            if N = N' then h.tailUpper j else h.pairCovUpper j := by
            refine Finset.sum_le_sum fun N hN => ?_
            refine Finset.sum_le_sum fun N' hN' => ?_
            by_cases hEq : N = N'
            · subst N'
              simpa using
                covariance_trackBThresholdExceedanceIndicator_self_le
                  h.core h.M h.buffer h.exceedance_measurable j N
                  (h.tailUpper j) (h.tail_prob_le_tailUpper j N hN)
            · simpa [hEq] using
                covariance_trackBThresholdExceedanceIndicator_le_of_pairCov
                  h.core h.M h.buffer h.exceedance_measurable j N N'
                  (h.pairCovUpper j)
                  (h.offdiag_pair_cov_le_pairCovUpper j N N' hN hN' hEq)
      _ ≤ h.countSecond j := h.covarianceBudget_le_countSecond j
  fail_summable := h.fail_summable
  prob_good_compl := h.prob_good_compl
  prob_overlap_many := h.prob_overlap_many

/-- Direct closure from a centered covariance sparse threshold package. -/
theorem erdos1144_of_trackBThresholdUniformCovarianceTailCertificate
    (h : TrackBThresholdUniformCovarianceTailCertificate) :
    Erdos1144 :=
  erdos1144_of_trackBThresholdAbundanceCertificate
    (trackBThresholdAbundanceCertificate_of_covarianceTail h)

end Problem1144
end Erdos
