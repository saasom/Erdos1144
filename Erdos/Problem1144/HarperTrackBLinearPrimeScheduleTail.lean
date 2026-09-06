import Erdos.Problem1144.HarperTrackBLinearPrimeScheduleScalar

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

namespace Erdos
namespace Problem1144

/-!
## Remaining concrete Gaussian-tail comparison fields

The scalar Gaussian-tail arithmetic for the concrete Track B schedule is proved
in `HarperTrackBLinearPrimeScheduleScalar`.  This file isolates the remaining
probabilistic content: comparison estimates for the actual masked fresh-prime
linear core.  Supplying this small structure is enough to build the full
`TrackBLinearPrimeScheduleGaussianTailFacts` object.
-/

/-- The concrete one-point upper tail bound is just the probability bound
`P(E) <= 1`, since the concrete `tailUpper` is `1`. -/
theorem trackBLinearPrimeConcrete_tail_prob_le_tailUpper
    (j N : ℕ)
    (_hN : N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point j) :
      mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              trackBLinearPrimeConcreteScheduleSpec.Q
              trackBLinearPrimeConcreteScheduleSpec.point
              trackBLinearPrimeConcreteScheduleSpec.freshLo
              trackBLinearPrimeConcreteScheduleSpec.freshHi
              trackBLinearPrimeConcreteScheduleSpec.good)
            trackBLinearPrimeConcreteScheduleSpec.M
            trackBLinearPrimeConcreteScheduleSpec.buffer j N)
        ≤ trackBLinearPrimeConcreteScheduleSpec.tailUpper j := by
  have hprob :
      mu
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              trackBLinearPrimeConcreteScheduleSpec.Q
              trackBLinearPrimeConcreteScheduleSpec.point
              trackBLinearPrimeConcreteScheduleSpec.freshLo
              trackBLinearPrimeConcreteScheduleSpec.freshHi
              trackBLinearPrimeConcreteScheduleSpec.good)
            trackBLinearPrimeConcreteScheduleSpec.M
            trackBLinearPrimeConcreteScheduleSpec.buffer j N)
        ≤ 1 := by
    simpa using
      (measure_mono
        (Set.subset_univ
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              trackBLinearPrimeConcreteScheduleSpec.Q
              trackBLinearPrimeConcreteScheduleSpec.point
              trackBLinearPrimeConcreteScheduleSpec.freshLo
              trackBLinearPrimeConcreteScheduleSpec.freshHi
              trackBLinearPrimeConcreteScheduleSpec.good)
            trackBLinearPrimeConcreteScheduleSpec.M
            trackBLinearPrimeConcreteScheduleSpec.buffer j N))).trans
        (by simp)
  exact
    (ENNReal.toReal_mono ENNReal.one_ne_top hprob).trans_eq
      (by simp [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteTailUpper])

/-- The concrete product lower comparison follows from the one-point lower
comparison.  With `gaussianTail = 1/2` and product slack `s = base^-10`,
the inequality is the elementary bound `(1/2 - s)^2 + s >= 1/4`. -/
theorem trackBLinearPrimeConcrete_tail_product_compare_lower
    (one_point_compare_lower :
      ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
          trackBLinearPrimeConcreteScheduleSpec.Q
          trackBLinearPrimeConcreteScheduleSpec.point j →
        trackBLinearPrimeConcreteScheduleSpec.gaussianTail j N -
            trackBLinearPrimeConcreteScheduleSpec.onePointSlack j ≤
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore
                trackBLinearPrimeConcreteScheduleSpec.Q
                trackBLinearPrimeConcreteScheduleSpec.point
                trackBLinearPrimeConcreteScheduleSpec.freshLo
                trackBLinearPrimeConcreteScheduleSpec.freshHi
                trackBLinearPrimeConcreteScheduleSpec.good)
              trackBLinearPrimeConcreteScheduleSpec.M
              trackBLinearPrimeConcreteScheduleSpec.buffer j N))
    (j N N' : ℕ)
    (hN : N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point j)
    (hN' : N' ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point j)
    (_hne : N ≠ N') :
      trackBLinearPrimeConcreteScheduleSpec.gaussianTail j N *
          trackBLinearPrimeConcreteScheduleSpec.gaussianTail j N'
        ≤
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore
                trackBLinearPrimeConcreteScheduleSpec.Q
                trackBLinearPrimeConcreteScheduleSpec.point
                trackBLinearPrimeConcreteScheduleSpec.freshLo
                trackBLinearPrimeConcreteScheduleSpec.freshHi
                trackBLinearPrimeConcreteScheduleSpec.good)
              trackBLinearPrimeConcreteScheduleSpec.M
              trackBLinearPrimeConcreteScheduleSpec.buffer j N) *
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore
                trackBLinearPrimeConcreteScheduleSpec.Q
                trackBLinearPrimeConcreteScheduleSpec.point
                trackBLinearPrimeConcreteScheduleSpec.freshLo
                trackBLinearPrimeConcreteScheduleSpec.freshHi
                trackBLinearPrimeConcreteScheduleSpec.good)
              trackBLinearPrimeConcreteScheduleSpec.M
              trackBLinearPrimeConcreteScheduleSpec.buffer j N') +
            trackBLinearPrimeConcreteScheduleSpec.productSlack j := by
  set s : ℝ := (((trackBLinearPrimeConcreteBase j : ℝ) ^ 10))⁻¹
  set p : ℝ :=
    mu.real
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeScheduledCore
          trackBLinearPrimeConcreteScheduleSpec.Q
          trackBLinearPrimeConcreteScheduleSpec.point
          trackBLinearPrimeConcreteScheduleSpec.freshLo
          trackBLinearPrimeConcreteScheduleSpec.freshHi
          trackBLinearPrimeConcreteScheduleSpec.good)
        trackBLinearPrimeConcreteScheduleSpec.M
        trackBLinearPrimeConcreteScheduleSpec.buffer j N)
  set q : ℝ :=
    mu.real
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeScheduledCore
          trackBLinearPrimeConcreteScheduleSpec.Q
          trackBLinearPrimeConcreteScheduleSpec.point
          trackBLinearPrimeConcreteScheduleSpec.freshLo
          trackBLinearPrimeConcreteScheduleSpec.freshHi
          trackBLinearPrimeConcreteScheduleSpec.good)
        trackBLinearPrimeConcreteScheduleSpec.M
        trackBLinearPrimeConcreteScheduleSpec.buffer j N')
  have hp : (1 : ℝ) / 2 - s ≤ p := by
    have hp0 := one_point_compare_lower j N hN
    change
      trackBLinearPrimeConcreteGaussianTail j N -
          trackBLinearPrimeConcreteOnePointSlack j ≤ p at hp0
    simpa [p, s, trackBLinearPrimeConcreteGaussianTail,
      trackBLinearPrimeConcreteOnePointSlack] using hp0
  have hq : (1 : ℝ) / 2 - s ≤ q := by
    have hq0 := one_point_compare_lower j N' hN'
    change
      trackBLinearPrimeConcreteGaussianTail j N' -
          trackBLinearPrimeConcreteOnePointSlack j ≤ q at hq0
    simpa [q, s, trackBLinearPrimeConcreteGaussianTail,
      trackBLinearPrimeConcreteOnePointSlack] using hq0
  have hs_le_quarter : s ≤ (1 : ℝ) / 4 := by
    simpa [s] using trackBLinearPrimeConcrete_inv_base_pow_ten_le_quarter j
  have hlow_nonneg : 0 ≤ (1 : ℝ) / 2 - s := by linarith
  have hp_nonneg : 0 ≤ p := le_trans hlow_nonneg hp
  have hmul : ((1 : ℝ) / 2 - s) * ((1 : ℝ) / 2 - s) ≤ p * q :=
    mul_le_mul hp hq hlow_nonneg hp_nonneg
  have halg : (1 : ℝ) / 2 * ((1 : ℝ) / 2) ≤
      ((1 : ℝ) / 2 - s) * ((1 : ℝ) / 2 - s) + s := by
    nlinarith [sq_nonneg s]
  have hfinal : (1 : ℝ) / 2 * ((1 : ℝ) / 2) ≤ p * q + s := by
    calc
      (1 : ℝ) / 2 * ((1 : ℝ) / 2)
          ≤ ((1 : ℝ) / 2 - s) * ((1 : ℝ) / 2 - s) + s := halg
      _ ≤ p * q + s := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmul s
  change
    trackBLinearPrimeConcreteGaussianTail j N *
        trackBLinearPrimeConcreteGaussianTail j N' ≤
      p * q + trackBLinearPrimeConcreteProductSlack j
  simpa [s, trackBLinearPrimeConcreteGaussianTail,
    trackBLinearPrimeConcreteProductSlack] using hfinal

/-- The only non-scalar fields still needed for concrete Gaussian tails. -/
structure TrackBLinearPrimeConcreteTailComparisonFacts where
  one_point_compare_lower :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point j →
      trackBLinearPrimeConcreteScheduleSpec.gaussianTail j N -
          trackBLinearPrimeConcreteScheduleSpec.onePointSlack j ≤
        mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              trackBLinearPrimeConcreteScheduleSpec.Q
              trackBLinearPrimeConcreteScheduleSpec.point
              trackBLinearPrimeConcreteScheduleSpec.freshLo
              trackBLinearPrimeConcreteScheduleSpec.freshHi
              trackBLinearPrimeConcreteScheduleSpec.good)
            trackBLinearPrimeConcreteScheduleSpec.M
            trackBLinearPrimeConcreteScheduleSpec.buffer j N)
  pair_compare_upper :
    ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point j →
      N' ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point j → N ≠ N' →
        mu.real
            (trackBThresholdPairExceedanceEvent
              (trackBLinearPrimeScheduledCore
                trackBLinearPrimeConcreteScheduleSpec.Q
                trackBLinearPrimeConcreteScheduleSpec.point
                trackBLinearPrimeConcreteScheduleSpec.freshLo
                trackBLinearPrimeConcreteScheduleSpec.freshHi
                trackBLinearPrimeConcreteScheduleSpec.good)
            trackBLinearPrimeConcreteScheduleSpec.M
            trackBLinearPrimeConcreteScheduleSpec.buffer j N N')
          ≤ trackBLinearPrimeConcreteScheduleSpec.gaussianPair j N N' +
            trackBLinearPrimeConcreteScheduleSpec.twoPointSlack j

/-- Assemble the concrete Gaussian-tail facts from the remaining comparison
fields plus scalar arithmetic. -/
def trackBLinearPrimeConcreteGaussianTailFacts_of_comparison
    (h : TrackBLinearPrimeConcreteTailComparisonFacts) :
    TrackBLinearPrimeScheduleGaussianTailFacts trackBLinearPrimeConcreteScheduleSpec where
  countMean_le_Q_beta := trackBLinearPrimeConcrete_countMean_le_Q_beta
  tailUpper_nonneg := trackBLinearPrimeConcrete_tailUpper_nonneg
  pairCovUpper_nonneg := trackBLinearPrimeConcrete_pairCovUpper_nonneg
  countSecond_budget := trackBLinearPrimeConcrete_countSecond_budget
  gaussian_one_point_lower := fun j N _hN =>
    trackBLinearPrimeConcrete_gaussian_one_point_lower j N
  one_point_compare_lower := h.one_point_compare_lower
  tail_prob_le_tailUpper := trackBLinearPrimeConcrete_tail_prob_le_tailUpper
  pair_compare_upper := h.pair_compare_upper
  gaussian_pair_cov_upper := fun j N N' _hN _hN' _hne =>
    trackBLinearPrimeConcrete_gaussian_pair_cov_upper j N N'
  tail_product_compare_lower :=
    trackBLinearPrimeConcrete_tail_product_compare_lower h.one_point_compare_lower
  pairCovBudget_le_pairCovUpper :=
    trackBLinearPrimeConcrete_pairCovBudget_le_pairCovUpper

/-- The concrete with-good one-point upper tail bound is again just the
probability bound `P(E) <= 1`, since `tailUpper = 1`. -/
theorem trackBLinearPrimeConcreteWithGood_tail_prob_le_tailUpper
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞)
    (j N : ℕ)
    (_hN : N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point j) :
      mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good)
            (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).M
            (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).buffer j N)
        ≤ (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).tailUpper j := by
  have hprob :
      mu
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good)
            (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).M
            (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).buffer j N)
        ≤ 1 := by
    simpa using
      (measure_mono
        (Set.subset_univ
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good)
            (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).M
            (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).buffer j N))).trans
        (by simp)
  exact
    (ENNReal.toReal_mono ENNReal.one_ne_top hprob).trans_eq
      (by simp [trackBLinearPrimeConcreteScheduleSpecWithGood,
        trackBLinearPrimeConcreteTailUpper])

/-- The concrete with-good product lower comparison follows from the one-point
lower comparison by the same elementary algebra as in the all-space wrapper. -/
theorem trackBLinearPrimeConcreteWithGood_tail_product_compare_lower
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞)
    (one_point_compare_lower :
      ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point j →
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).gaussianTail j N -
            (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).onePointSlack j ≤
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good)
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).M
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).buffer j N))
    (j N N' : ℕ)
    (hN : N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point j)
    (hN' : N' ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point j)
    (_hne : N ≠ N') :
      (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).gaussianTail j N *
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).gaussianTail j N'
        ≤
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good)
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).M
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).buffer j N) *
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good)
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).M
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).buffer j N') +
            (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).productSlack j := by
  set s : ℝ := (((trackBLinearPrimeConcreteBase j : ℝ) ^ 10))⁻¹
  set p : ℝ :=
    mu.real
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeScheduledCore
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good)
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).M
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).buffer j N)
  set q : ℝ :=
    mu.real
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeScheduledCore
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good)
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).M
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).buffer j N')
  have hp : (1 : ℝ) / 2 - s ≤ p := by
    have hp0 := one_point_compare_lower j N hN
    change
      trackBLinearPrimeConcreteGaussianTail j N -
          trackBLinearPrimeConcreteOnePointSlack j ≤ p at hp0
    simpa [p, s, trackBLinearPrimeConcreteGaussianTail,
      trackBLinearPrimeConcreteOnePointSlack] using hp0
  have hq : (1 : ℝ) / 2 - s ≤ q := by
    have hq0 := one_point_compare_lower j N' hN'
    change
      trackBLinearPrimeConcreteGaussianTail j N' -
          trackBLinearPrimeConcreteOnePointSlack j ≤ q at hq0
    simpa [q, s, trackBLinearPrimeConcreteGaussianTail,
      trackBLinearPrimeConcreteOnePointSlack] using hq0
  have hs_le_quarter : s ≤ (1 : ℝ) / 4 := by
    simpa [s] using trackBLinearPrimeConcrete_inv_base_pow_ten_le_quarter j
  have hlow_nonneg : 0 ≤ (1 : ℝ) / 2 - s := by linarith
  have hp_nonneg : 0 ≤ p := le_trans hlow_nonneg hp
  have hmul : ((1 : ℝ) / 2 - s) * ((1 : ℝ) / 2 - s) ≤ p * q :=
    mul_le_mul hp hq hlow_nonneg hp_nonneg
  have halg : (1 : ℝ) / 2 * ((1 : ℝ) / 2) ≤
      ((1 : ℝ) / 2 - s) * ((1 : ℝ) / 2 - s) + s := by
    nlinarith [sq_nonneg s]
  have hfinal : (1 : ℝ) / 2 * ((1 : ℝ) / 2) ≤ p * q + s := by
    calc
      (1 : ℝ) / 2 * ((1 : ℝ) / 2)
          ≤ ((1 : ℝ) / 2 - s) * ((1 : ℝ) / 2 - s) + s := halg
      _ ≤ p * q + s := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmul s
  change
    trackBLinearPrimeConcreteGaussianTail j N *
        trackBLinearPrimeConcreteGaussianTail j N' ≤
      p * q + trackBLinearPrimeConcreteProductSlack j
  simpa [s, trackBLinearPrimeConcreteGaussianTail,
    trackBLinearPrimeConcreteProductSlack] using hfinal

/-- The only non-scalar fields still needed for concrete Gaussian tails with a
configurable good event. -/
structure TrackBLinearPrimeConcreteWithGoodTailComparisonFacts
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) where
  one_point_compare_lower :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point j →
      (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).gaussianTail j N -
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).onePointSlack j ≤
        mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good)
            (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).M
            (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).buffer j N)
  pair_compare_upper :
    ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point j →
      N' ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point j →
      N ≠ N' →
        mu.real
            (trackBThresholdPairExceedanceEvent
              (trackBLinearPrimeScheduledCore
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good)
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).M
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).buffer j N N')
          ≤ (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).gaussianPair j N N' +
            (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).twoPointSlack j

/-- Assemble concrete with-good Gaussian-tail facts from the remaining
comparison fields plus scalar arithmetic. -/
def trackBLinearPrimeConcreteWithGoodGaussianTailFacts_of_comparison
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeConcreteWithGoodTailComparisonFacts good failGood) :
    TrackBLinearPrimeScheduleGaussianTailFacts
      (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood) where
  countMean_le_Q_beta := by
    intro j
    simpa [trackBLinearPrimeConcreteScheduleSpecWithGood,
      trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_countMean_le_Q_beta j
  tailUpper_nonneg := by
    intro j
    simpa [trackBLinearPrimeConcreteScheduleSpecWithGood,
      trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_tailUpper_nonneg j
  pairCovUpper_nonneg := by
    intro j
    simpa [trackBLinearPrimeConcreteScheduleSpecWithGood,
      trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_pairCovUpper_nonneg j
  countSecond_budget := by
    intro j
    simpa [trackBLinearPrimeConcreteScheduleSpecWithGood,
      trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_countSecond_budget j
  gaussian_one_point_lower := by
    intro j N hN
    simpa [trackBLinearPrimeConcreteScheduleSpecWithGood,
      trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_gaussian_one_point_lower j N
  one_point_compare_lower := h.one_point_compare_lower
  tail_prob_le_tailUpper :=
    trackBLinearPrimeConcreteWithGood_tail_prob_le_tailUpper good failGood
  pair_compare_upper := h.pair_compare_upper
  gaussian_pair_cov_upper := by
    intro j N N' hN hN' hne
    simpa [trackBLinearPrimeConcreteScheduleSpecWithGood,
      trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_gaussian_pair_cov_upper j N N'
  tail_product_compare_lower :=
    trackBLinearPrimeConcreteWithGood_tail_product_compare_lower
      good failGood h.one_point_compare_lower
  pairCovBudget_le_pairCovUpper := by
    intro j
    simpa [trackBLinearPrimeConcreteScheduleSpecWithGood,
      trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_pairCovBudget_le_pairCovUpper j

end Problem1144
end Erdos
