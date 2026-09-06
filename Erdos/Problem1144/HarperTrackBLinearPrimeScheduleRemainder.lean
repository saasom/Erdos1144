import Erdos.Problem1144.HarperTrackBLinearPrimeScheduleGeometry

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

namespace Erdos
namespace Problem1144

/-!
## Concrete selected-remainder wrapper

The scheduled bridge already reduces selected-overlap control to a one-point
bad-remainder estimate and a finite-union budget.  This file fixes the concrete
per-point budget `base^-8`; since the concrete mesh has `Q = base^4` points,
the union budget lands in the existing `failOverlap = base^-4`.
-/

/-- Concrete one-point bad-remainder budget for the scheduled mesh. -/
noncomputable def trackBLinearPrimeConcreteSingleRemainderFail (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹)

/-- The concrete threshold buffer is positive at every stage. -/
theorem trackBLinearPrimeConcreteBuffer_pos (j : ℕ) :
    0 < trackBLinearPrimeConcreteScheduleSpec.buffer j := by
  change 0 < trackBLinearPrimeConcreteBuffer j
  unfold trackBLinearPrimeConcreteBuffer
  have hM : 0 < trackBLinearPrimeConcreteM j := trackBLinearPrimeConcreteM_pos j
  linarith

/-- Real-valued scalar budget helper for the concrete remainder second-moment
interface.  Analytic estimates may prove the numerator bound before division
by `buffer_j^2`; this lemma converts it to the `ℝ≥0∞` one-point budget. -/
theorem trackBLinearPrimeConcrete_remainder_second_budget_of_real_bound
    (remainderSecond : ℕ → ℕ → ℝ) (j N : ℕ)
    (hsecond :
      remainderSecond j N ≤
        (trackBLinearPrimeConcreteScheduleSpec.buffer j) ^ 2 *
          (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹) :
    ENNReal.ofReal
        (remainderSecond j N / (trackBLinearPrimeConcreteScheduleSpec.buffer j) ^ 2)
      ≤ trackBLinearPrimeConcreteSingleRemainderFail j := by
  have hbuffer_sq :
      0 < (trackBLinearPrimeConcreteScheduleSpec.buffer j) ^ 2 :=
    pow_pos (trackBLinearPrimeConcreteBuffer_pos j) 2
  have hreal :
      remainderSecond j N / (trackBLinearPrimeConcreteScheduleSpec.buffer j) ^ 2 ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹ := by
    rw [div_le_iff₀ hbuffer_sq]
    simpa [mul_comm] using hsecond
  simpa [trackBLinearPrimeConcreteSingleRemainderFail] using
    ENNReal.ofReal_le_ofReal hreal

/-- The only analytic selected-remainder field still needed for the concrete
schedule. -/
structure TrackBLinearPrimeConcreteRemainderAnalyticFacts where
  one_point_remainder_bad :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point j →
      mu
          {omega |
            trackBLinearPrimeScheduledRemainder
                trackBLinearPrimeConcreteScheduleSpec.Q
                trackBLinearPrimeConcreteScheduleSpec.point
                trackBLinearPrimeConcreteScheduleSpec.freshLo
                trackBLinearPrimeConcreteScheduleSpec.freshHi
                trackBLinearPrimeConcreteScheduleSpec.good omega j N <
              -trackBLinearPrimeConcreteScheduleSpec.buffer j}
        ≤ trackBLinearPrimeConcreteSingleRemainderFail j

/-- Concrete selected-remainder input in the square-moment form produced by
boundary, flat-tail, and complete-transfer estimates. -/
structure TrackBLinearPrimeConcreteRemainderSecondMomentFacts where
  remainderSecond : ℕ → ℕ → ℝ
  second_integrable :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeScheduledRemainder
              trackBLinearPrimeConcreteScheduleSpec.Q
              trackBLinearPrimeConcreteScheduleSpec.point
              trackBLinearPrimeConcreteScheduleSpec.freshLo
              trackBLinearPrimeConcreteScheduleSpec.freshHi
              trackBLinearPrimeConcreteScheduleSpec.good omega j N) ^ 2) mu
  second_upper :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point j →
      (∫ omega,
          (trackBLinearPrimeScheduledRemainder
              trackBLinearPrimeConcreteScheduleSpec.Q
              trackBLinearPrimeConcreteScheduleSpec.point
              trackBLinearPrimeConcreteScheduleSpec.freshLo
              trackBLinearPrimeConcreteScheduleSpec.freshHi
              trackBLinearPrimeConcreteScheduleSpec.good omega j N) ^ 2 ∂mu)
        ≤ remainderSecond j N
  second_budget :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point j →
      ENNReal.ofReal
          (remainderSecond j N / (trackBLinearPrimeConcreteScheduleSpec.buffer j) ^ 2)
        ≤ trackBLinearPrimeConcreteSingleRemainderFail j

/-- The only analytic selected-remainder field still needed for the concrete
schedule with a configurable good event. -/
structure TrackBLinearPrimeConcreteWithGoodRemainderAnalyticFacts
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) where
  one_point_remainder_bad :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point j →
      mu
          {omega |
            trackBLinearPrimeScheduledRemainder
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi
                (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good omega j N <
              -(trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).buffer j}
        ≤ trackBLinearPrimeConcreteSingleRemainderFail j

/-- Concrete with-good selected-remainder input in square-moment form. -/
structure TrackBLinearPrimeConcreteWithGoodRemainderSecondMomentFacts
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) where
  remainderSecond : ℕ → ℕ → ℝ
  second_integrable :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeScheduledRemainder
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good omega j N) ^ 2)
        mu
  second_upper :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point j →
      (∫ omega,
          (trackBLinearPrimeScheduledRemainder
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good omega j N) ^ 2
          ∂mu)
        ≤ remainderSecond j N
  second_budget :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point j →
      ENNReal.ofReal
          (remainderSecond j N /
            ((trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).buffer j) ^ 2)
        ≤ trackBLinearPrimeConcreteSingleRemainderFail j

theorem trackBLinearPrimeConcrete_remainder_union_budget (j : ℕ) :
    (trackBLinearPrimeConcreteScheduleSpec.Q j) •
        trackBLinearPrimeConcreteSingleRemainderFail j ≤
      trackBLinearPrimeConcreteScheduleSpec.failOverlap j := by
  have hb_nonneg : 0 ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (by positivity) 8)
  have hreal :
      (trackBLinearPrimeConcreteQ j : ℝ) *
          (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹ =
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹ := by
    have hb0 : (trackBLinearPrimeConcreteBase j : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (trackBLinearPrimeConcreteBase_pos j))
    have hb4 : (trackBLinearPrimeConcreteBase j : ℝ) ^ 4 ≠ 0 := pow_ne_zero 4 hb0
    rw [trackBLinearPrimeConcreteQ]
    have hpow :
        (trackBLinearPrimeConcreteBase j : ℝ) ^ 8 =
          (trackBLinearPrimeConcreteBase j : ℝ) ^ 4 *
            (trackBLinearPrimeConcreteBase j : ℝ) ^ 4 := by
      rw [show 8 = 4 + 4 by norm_num, pow_add]
    rw [hpow, mul_inv_rev]
    field_simp [hb4]
    norm_num
  calc
    (trackBLinearPrimeConcreteScheduleSpec.Q j) •
        trackBLinearPrimeConcreteSingleRemainderFail j
        = ENNReal.ofReal
            ((trackBLinearPrimeConcreteQ j : ℝ) *
              (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹) := by
          change (trackBLinearPrimeConcreteQ j) •
              ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹) =
            ENNReal.ofReal
              ((trackBLinearPrimeConcreteQ j : ℝ) *
                (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹)
          rw [← ENNReal.ofReal_nsmul]
          simp [nsmul_eq_mul]
    _ = trackBLinearPrimeConcreteScheduleSpec.failOverlap j := by
          simp [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteFailOverlap,
            hreal]
    _ ≤ trackBLinearPrimeConcreteScheduleSpec.failOverlap j := le_rfl

/-- Assemble concrete selected-remainder facts from the remaining one-point
bad-remainder estimate plus the proved union budget. -/
def trackBLinearPrimeConcreteRemainderFacts_of_analytic
    (h : TrackBLinearPrimeConcreteRemainderAnalyticFacts) :
    TrackBLinearPrimeScheduleRemainderFacts trackBLinearPrimeConcreteScheduleSpec where
  singleFail := trackBLinearPrimeConcreteSingleRemainderFail
  one_point_remainder_bad := h.one_point_remainder_bad
  union_budget := trackBLinearPrimeConcrete_remainder_union_budget

/-- Assemble concrete selected-remainder facts from square-moment estimates. -/
def trackBLinearPrimeConcreteRemainderAnalyticFacts_of_secondMoment
    (h : TrackBLinearPrimeConcreteRemainderSecondMomentFacts) :
    TrackBLinearPrimeConcreteRemainderAnalyticFacts where
  one_point_remainder_bad := by
    intro j N hN
    exact
      (measure_trackBLinearPrimeScheduledRemainder_lt_neg_le_second
        trackBLinearPrimeConcreteScheduleSpec h.remainderSecond j N
        (trackBLinearPrimeConcreteBuffer_pos j)
        (h.second_integrable j N hN) (h.second_upper j N hN)).trans
        (h.second_budget j N hN)

/-- Directly assemble concrete schedule remainder facts from square moments. -/
def trackBLinearPrimeConcreteRemainderFacts_of_secondMoment
    (h : TrackBLinearPrimeConcreteRemainderSecondMomentFacts) :
    TrackBLinearPrimeScheduleRemainderFacts trackBLinearPrimeConcreteScheduleSpec :=
  trackBLinearPrimeConcreteRemainderFacts_of_analytic
    (trackBLinearPrimeConcreteRemainderAnalyticFacts_of_secondMoment h)

/-- Assemble concrete with-good selected-remainder facts from the remaining
one-point bad-remainder estimate plus the proved union budget. -/
def trackBLinearPrimeConcreteWithGoodRemainderFacts_of_analytic
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeConcreteWithGoodRemainderAnalyticFacts good failGood) :
    TrackBLinearPrimeScheduleRemainderFacts
      (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood) where
  singleFail := trackBLinearPrimeConcreteSingleRemainderFail
  one_point_remainder_bad := h.one_point_remainder_bad
  union_budget := trackBLinearPrimeConcrete_remainder_union_budget

/-- Assemble concrete with-good selected-remainder facts from square-moment
estimates. -/
def trackBLinearPrimeConcreteWithGoodRemainderAnalyticFacts_of_secondMoment
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeConcreteWithGoodRemainderSecondMomentFacts good failGood) :
    TrackBLinearPrimeConcreteWithGoodRemainderAnalyticFacts good failGood where
  one_point_remainder_bad := by
    intro j N hN
    exact
      (measure_trackBLinearPrimeScheduledRemainder_lt_neg_le_second
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood)
        h.remainderSecond j N (trackBLinearPrimeConcreteBuffer_pos j)
        (h.second_integrable j N hN) (h.second_upper j N hN)).trans
        (h.second_budget j N hN)

/-- Directly assemble concrete with-good schedule remainder facts from square
moments. -/
def trackBLinearPrimeConcreteWithGoodRemainderFacts_of_secondMoment
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeConcreteWithGoodRemainderSecondMomentFacts good failGood) :
    TrackBLinearPrimeScheduleRemainderFacts
      (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood) :=
  trackBLinearPrimeConcreteWithGoodRemainderFacts_of_analytic
    (trackBLinearPrimeConcreteWithGoodRemainderAnalyticFacts_of_secondMoment h)

end Problem1144
end Erdos
