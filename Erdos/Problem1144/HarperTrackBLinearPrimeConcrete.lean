import Erdos.Problem1144.HarperTrackBLinearPrimeScheduleRemainder

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

namespace Erdos
namespace Problem1144

/-!
## Concrete Track B analytic package

This is the final Lean-facing handoff for the current Track B route.  All
deterministic schedule arithmetic and certificate plumbing has been pushed
below this file.  The remaining analytic work is exactly the three fields in
`TrackBLinearPrimeConcreteAnalyticFacts`.
-/

/-- The complete remaining analytic package for the concrete fresh-prime Track
B schedule. -/
structure TrackBLinearPrimeConcreteAnalyticFacts where
  geometry : TrackBLinearPrimeConcreteGeometryAnalyticFacts
  tails : TrackBLinearPrimeConcreteTailComparisonFacts
  remainder : TrackBLinearPrimeConcreteRemainderAnalyticFacts

/-- Assemble the scheduled Gaussian-comparison certificate from the concrete
analytic package. -/
def trackBLinearPrimeScheduledGaussianComparisonCertificate_of_concreteAnalyticFacts
    (h : TrackBLinearPrimeConcreteAnalyticFacts) :
    TrackBLinearPrimeScheduledGaussianComparisonCertificate :=
  trackBLinearPrimeScheduledGaussianComparisonCertificate_of_scheduleFacts
    trackBLinearPrimeConcreteScheduleStageFacts
    trackBLinearPrimeConcreteScheduleGoodEventFacts
    (trackBLinearPrimeConcreteGeometryFacts_of_analytic h.geometry)
    (trackBLinearPrimeConcreteGaussianTailFacts_of_comparison h.tails)
    (trackBLinearPrimeConcreteRemainderFacts_of_analytic h.remainder)

/-- Track B closes Erdős #1144 once the concrete analytic package is supplied.

This theorem deliberately leaves `Final.lean` unchanged; it is the intended
rewiring point once the three analytic fields are actually proved. -/
theorem erdos1144_of_trackBLinearPrimeConcreteAnalyticFacts
    (h : TrackBLinearPrimeConcreteAnalyticFacts) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeScheduledGaussianComparisonCertificate
    (trackBLinearPrimeScheduledGaussianComparisonCertificate_of_concreteAnalyticFacts h)

/-- Variant of the concrete Track B endpoint allowing a genuine analytic good
event.  This is the preferred endpoint if the coefficient variance floor is
proved only on a high-probability geometry event rather than uniformly on all
of `Omega`. -/
theorem erdos1144_of_trackBLinearPrimeConcreteScheduleWithGoodFacts
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (hfail :
      (∑' j, (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).failGood j)
        ≠ ⊤)
    (good_measurable : ∀ j, MeasurableSet (good j))
    (prob_good_compl : ∀ j, mu (good j)ᶜ ≤ failGood j)
    (geom :
      TrackBLinearPrimeScheduleGeometryFacts
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood))
    (tails :
      TrackBLinearPrimeScheduleGaussianTailFacts
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood))
    (rem :
      TrackBLinearPrimeScheduleRemainderFacts
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood)) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeScheduleFacts
    (trackBLinearPrimeConcreteScheduleStageFactsWithGood good failGood hfail)
    (trackBLinearPrimeConcreteScheduleGoodEventFactsWithGood
      good failGood good_measurable prob_good_compl)
    geom tails rem

/-- Lean-facing analytic package for the concrete polynomial schedule with a
genuine good event.  This is the convenient target when the variance floor and
comparison estimates are proved on a high-probability geometry event. -/
structure TrackBLinearPrimeConcreteWithGoodAnalyticFacts where
  good : ℕ → Set Omega
  failGood : ℕ → ℝ≥0∞
  failGood_summable :
    (∑' j, (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).failGood j)
      ≠ ⊤
  good_measurable : ∀ j, MeasurableSet (good j)
  prob_good_compl : ∀ j, mu (good j)ᶜ ≤ failGood j
  geometry : TrackBLinearPrimeConcreteWithGoodGeometryAnalyticFacts good failGood
  tails : TrackBLinearPrimeConcreteWithGoodTailComparisonFacts good failGood
  remainder : TrackBLinearPrimeConcreteWithGoodRemainderAnalyticFacts good failGood

/-- Assemble the scheduled Gaussian-comparison certificate from the concrete
with-good analytic package. -/
def trackBLinearPrimeScheduledGaussianComparisonCertificate_of_concreteWithGoodAnalyticFacts
    (h : TrackBLinearPrimeConcreteWithGoodAnalyticFacts) :
    TrackBLinearPrimeScheduledGaussianComparisonCertificate :=
  trackBLinearPrimeScheduledGaussianComparisonCertificate_of_scheduleFacts
    (trackBLinearPrimeConcreteScheduleStageFactsWithGood
      h.good h.failGood h.failGood_summable)
    (trackBLinearPrimeConcreteScheduleGoodEventFactsWithGood
      h.good h.failGood h.good_measurable h.prob_good_compl)
    (trackBLinearPrimeConcreteWithGoodGeometryFacts_of_analytic h.geometry)
    (trackBLinearPrimeConcreteWithGoodGaussianTailFacts_of_comparison h.tails)
    (trackBLinearPrimeConcreteWithGoodRemainderFacts_of_analytic h.remainder)

/-- Track B closes Erdős #1144 from the concrete polynomial schedule with a
genuine high-probability good event. -/
theorem erdos1144_of_trackBLinearPrimeConcreteWithGoodAnalyticFacts
    (h : TrackBLinearPrimeConcreteWithGoodAnalyticFacts) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeScheduledGaussianComparisonCertificate
    (trackBLinearPrimeScheduledGaussianComparisonCertificate_of_concreteWithGoodAnalyticFacts h)

/-- Concrete Track B analytic package with the good event fixed to the
variance-floor event.  This removes the geometry variance-floor field itself:
the remaining geometry-side input is the probability bound for the complement
of `trackBLinearPrimeConcreteVarianceGood`. -/
structure TrackBLinearPrimeConcreteVarianceGoodAnalyticFacts where
  failGood : ℕ → ℝ≥0∞
  failGood_summable :
    (∑' j,
        (trackBLinearPrimeConcreteScheduleSpecWithGood
          trackBLinearPrimeConcreteVarianceGood failGood).failGood j) ≠ ⊤
  prob_variance_good_compl :
    ∀ j, mu (trackBLinearPrimeConcreteVarianceGood j)ᶜ ≤ failGood j
  tails :
    TrackBLinearPrimeConcreteWithGoodTailComparisonFacts
      trackBLinearPrimeConcreteVarianceGood failGood
  remainder :
    TrackBLinearPrimeConcreteWithGoodRemainderAnalyticFacts
      trackBLinearPrimeConcreteVarianceGood failGood

/-- Per-point budget used to control the variance-good complement by a finite
union over the concrete mesh.  It is numerically the same summable scale as the
selected-remainder one-point budget. -/
noncomputable def trackBLinearPrimeConcreteSingleVarianceFail (j : ℕ) : ℝ≥0∞ :=
  trackBLinearPrimeConcreteSingleRemainderFail j

/-- A one-point lower-tail interface for the concrete scheduled variance. -/
structure TrackBLinearPrimeConcreteVarianceGoodSinglePointFacts where
  one_point_variance_bad :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j →
      mu {omega : Omega |
          trackBLinearPrimeScheduledVariance
              trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
              trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi omega j N <
            trackBLinearPrimeConcreteV j}
        ≤ trackBLinearPrimeConcreteSingleVarianceFail j

/-- The current one-point variance-good budget `base^-8` is strictly below
`1/2` at every stage. -/
theorem trackBLinearPrimeConcreteSingleVarianceFail_lt_half (j : ℕ) :
    trackBLinearPrimeConcreteSingleVarianceFail j < ENNReal.ofReal ((1 : ℝ) / 2) := by
  have hb2 : (2 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
    exact_mod_cast trackBLinearPrimeConcreteBase_two_le j
  have hpow : (2 : ℝ) < (trackBLinearPrimeConcreteBase j : ℝ) ^ 8 := by
    have hmono :
        (2 : ℝ) ^ 8 ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 8 :=
      pow_le_pow_left₀ (by norm_num) hb2 8
    norm_num at hmono
    exact lt_of_lt_of_le (by norm_num) hmono
  have hpos : (0 : ℝ) < (trackBLinearPrimeConcreteBase j : ℝ) ^ 8 := by
    positivity
  have hinv :
      (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹ < (1 : ℝ) / 2 := by
    simpa [one_div] using
      (inv_lt_inv₀ hpos (by norm_num : (0 : ℝ) < 2)).mpr hpow
  unfold trackBLinearPrimeConcreteSingleVarianceFail
  unfold trackBLinearPrimeConcreteSingleRemainderFail
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).mpr hinv

/-- The current squarefree fresh-prime coefficient layer cannot satisfy the
`base^-8` one-point variance-good interface: its bad-variance probability is
at least `1/2` at a concrete mesh point, while the interface asks for a
strictly smaller budget. -/
theorem not_trackBLinearPrimeConcreteVarianceGoodSinglePointFacts :
    ¬ TrackBLinearPrimeConcreteVarianceGoodSinglePointFacts := by
  intro h
  let j : ℕ := 0
  have hr : 1 ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j := by
    rw [mem_trackBLinearPrimeMeshIndexSet]
    exact ⟨by norm_num, trackBLinearPrimeConcreteQ_pos j⟩
  have hN :
      trackBLinearPrimeConcretePoint j 1 ∈
        trackBLinearPrimeMeshTestSet
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j := by
    rw [mem_trackBLinearPrimeMeshTestSet]
    exact ⟨1, hr, rfl⟩
  have hlow :
      ENNReal.ofReal ((1 : ℝ) / 2) ≤
        mu {omega : Omega |
            trackBLinearPrimeScheduledVariance
              trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
              trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
              omega j (trackBLinearPrimeConcretePoint j 1) <
            trackBLinearPrimeConcreteV j} :=
    measure_trackBLinearPrimeConcrete_scheduledVariance_lt_V_ge_half j 1 hr
  have hup :
      mu {omega : Omega |
          trackBLinearPrimeScheduledVariance
            trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
            trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
            omega j (trackBLinearPrimeConcretePoint j 1) <
          trackBLinearPrimeConcreteV j}
        ≤ trackBLinearPrimeConcreteSingleVarianceFail j :=
    h.one_point_variance_bad j (trackBLinearPrimeConcretePoint j 1) hN
  exact
    (not_lt_of_ge (hlow.trans hup))
      (trackBLinearPrimeConcreteSingleVarianceFail_lt_half j)

/-- Summability of the concrete overlap budget, used as the variance-good
failure budget in the single-point variance route. -/
theorem trackBLinearPrimeConcreteFailOverlap_tsum_ne_top :
    (∑' j,
        (trackBLinearPrimeConcreteScheduleSpecWithGood
          trackBLinearPrimeConcreteVarianceGood
          trackBLinearPrimeConcreteFailOverlap).failGood j) ≠ ⊤ := by
  simpa [trackBLinearPrimeConcreteScheduleSpecWithGood, trackBLinearPrimeConcreteFailOverlap]
    using trackBLinearPrimeConcrete_inv_base_four_summable.tsum_ofReal_ne_top

/-- Bound the variance-good complement by the mesh cardinality times the
one-point variance-bad budget. -/
theorem prob_trackBLinearPrimeConcreteVarianceGood_compl_le_card_singleVariance
    (h : TrackBLinearPrimeConcreteVarianceGoodSinglePointFacts) (j : ℕ) :
    mu (trackBLinearPrimeConcreteVarianceGood j)ᶜ ≤
      (trackBLinearPrimeMeshTestSet
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j).card •
        trackBLinearPrimeConcreteSingleVarianceFail j := by
  calc
    mu (trackBLinearPrimeConcreteVarianceGood j)ᶜ
        ≤ ∑ N ∈ trackBLinearPrimeMeshTestSet
            trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j,
          mu {omega : Omega |
            trackBLinearPrimeScheduledVariance
                trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
                trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi omega j N <
              trackBLinearPrimeConcreteV j} :=
        measure_trackBLinearPrimeConcreteVarianceGood_compl_le_sum_single j
    _ ≤ ∑ N ∈ trackBLinearPrimeMeshTestSet
            trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j,
          trackBLinearPrimeConcreteSingleVarianceFail j := by
        exact Finset.sum_le_sum (fun N hN => h.one_point_variance_bad j N hN)
    _ = (trackBLinearPrimeMeshTestSet
            trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j).card •
          trackBLinearPrimeConcreteSingleVarianceFail j := by
        simp

/-- The one-point variance-bad interface gives the concrete `failOverlap`
budget for the variance-good complement. -/
theorem prob_trackBLinearPrimeConcreteVarianceGood_compl_le_failOverlap
    (h : TrackBLinearPrimeConcreteVarianceGoodSinglePointFacts) (j : ℕ) :
    mu (trackBLinearPrimeConcreteVarianceGood j)ᶜ ≤
      trackBLinearPrimeConcreteFailOverlap j := by
  have hcard :
      (trackBLinearPrimeMeshTestSet
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j).card =
        trackBLinearPrimeConcreteQ j := by
    refine trackBLinearPrimeMeshTestSet_card_of_injOn
      trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j ?_
    refine trackBLinearPrimeMesh_injOn_of_strict
      trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j ?_
    intro r s hr hs hrs
    exact trackBLinearPrimeConcrete_point_strict j hr hs hrs
  calc
    mu (trackBLinearPrimeConcreteVarianceGood j)ᶜ
        ≤ (trackBLinearPrimeMeshTestSet
            trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j).card •
          trackBLinearPrimeConcreteSingleVarianceFail j :=
        prob_trackBLinearPrimeConcreteVarianceGood_compl_le_card_singleVariance h j
    _ = trackBLinearPrimeConcreteScheduleSpec.Q j •
          trackBLinearPrimeConcreteSingleRemainderFail j := by
        rw [hcard]
        rfl
    _ ≤ trackBLinearPrimeConcreteScheduleSpec.failOverlap j :=
        trackBLinearPrimeConcrete_remainder_union_budget j
    _ = trackBLinearPrimeConcreteFailOverlap j := by
        rfl

/-- Assemble the variance-good analytic package from a one-point variance
lower-tail estimate, leaving only the tail-comparison and remainder estimates
as separate analytic inputs. -/
def trackBLinearPrimeConcreteVarianceGoodAnalyticFacts_of_singlePoint
    (variance : TrackBLinearPrimeConcreteVarianceGoodSinglePointFacts)
    (tails :
      TrackBLinearPrimeConcreteWithGoodTailComparisonFacts
        trackBLinearPrimeConcreteVarianceGood trackBLinearPrimeConcreteFailOverlap)
    (remainder :
      TrackBLinearPrimeConcreteWithGoodRemainderAnalyticFacts
        trackBLinearPrimeConcreteVarianceGood trackBLinearPrimeConcreteFailOverlap) :
    TrackBLinearPrimeConcreteVarianceGoodAnalyticFacts where
  failGood := trackBLinearPrimeConcreteFailOverlap
  failGood_summable := trackBLinearPrimeConcreteFailOverlap_tsum_ne_top
  prob_variance_good_compl :=
    prob_trackBLinearPrimeConcreteVarianceGood_compl_le_failOverlap variance
  tails := tails
  remainder := remainder

/-- Assemble the general with-good analytic package from the variance-good
specialization. -/
def trackBLinearPrimeConcreteWithGoodAnalyticFacts_of_varianceGood
    (h : TrackBLinearPrimeConcreteVarianceGoodAnalyticFacts) :
    TrackBLinearPrimeConcreteWithGoodAnalyticFacts where
  good := trackBLinearPrimeConcreteVarianceGood
  failGood := h.failGood
  failGood_summable := h.failGood_summable
  good_measurable := measurableSet_trackBLinearPrimeConcreteVarianceGood
  prob_good_compl := h.prob_variance_good_compl
  geometry :=
    trackBLinearPrimeConcreteWithGoodGeometryAnalyticFacts_of_varianceGood h.failGood
  tails := h.tails
  remainder := h.remainder

/-- Track B closes Erdős #1144 from the variance-good specialization of the
concrete polynomial schedule. -/
theorem erdos1144_of_trackBLinearPrimeConcreteVarianceGoodAnalyticFacts
    (h : TrackBLinearPrimeConcreteVarianceGoodAnalyticFacts) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeConcreteWithGoodAnalyticFacts
    (trackBLinearPrimeConcreteWithGoodAnalyticFacts_of_varianceGood h)

end Problem1144
end Erdos
