import Erdos.Problem1144.HarperTrackBLinearPrime

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

namespace Erdos
namespace Problem1144

/-!
## Schedule-spec wrapper for the Track B fresh-prime route

This module is intentionally thin.  It packages the remaining scalar schedule
obligations for the fresh-prime linear Track B proof, then assembles the
already-defined scheduled certificates from those pieces.

The point is to keep the final analytic package explicit: coefficient geometry,
linear Rademacher comparison, selected-remainder control, and summability remain
visible fields until they are proved for a concrete schedule.
-/

/-- Shared scheduled data for the fresh-prime linear Track B proof. -/
structure TrackBLinearPrimeScheduleSpec where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  Q : ℕ → ℕ
  point : ℕ → ℕ → ℕ
  freshLo : ℕ → ℕ → ℕ
  freshHi : ℕ → ℕ → ℕ
  good : ℕ → Set Omega
  r : ℕ → ℕ
  failGood : ℕ → ℝ≥0∞
  failOverlap : ℕ → ℝ≥0∞
  beta : ℕ → ℝ
  tailUpper : ℕ → ℝ
  pairCovUpper : ℕ → ℝ
  countMean : ℕ → ℝ
  countSecond : ℕ → ℝ
  V : ℕ → ℝ
  flat : ℕ → ℝ
  rho : ℕ → ℝ
  gaussianTail : ℕ → ℕ → ℝ
  gaussianPair : ℕ → ℕ → ℕ → ℝ
  onePointSlack : ℕ → ℝ
  twoPointSlack : ℕ → ℝ
  productSlack : ℕ → ℝ
  gaussianPairCovUpper : ℕ → ℝ

/-!
### Concrete polynomial schedule

The definitions below encode the schedule from the Track B proof collection in
integer-valued form, using the harmless shift `j + 2` to avoid small-index
degeneracies.  The remaining work is to prove the fact structures for this
specific `TrackBLinearPrimeScheduleSpec`.
-/

/-- Fixed large polynomial exponent used by the concrete Track B schedule. -/
def trackBLinearPrimeConcreteK : ℕ := 100

/-- Shifted stage parameter.  The shift avoids zero denominators and gives
positive mesh sizes from the first stage. -/
def trackBLinearPrimeConcreteBase (j : ℕ) : ℕ := j + 2

/-- Sparse mesh size `Q_j`. -/
def trackBLinearPrimeConcreteQ (j : ℕ) : ℕ :=
  trackBLinearPrimeConcreteBase j ^ 4

/-- First sparse point scale, corresponding to `t_{j,1}` in the paper notes. -/
def trackBLinearPrimeConcretePointScale (j : ℕ) : ℕ :=
  trackBLinearPrimeConcreteBase j ^ (30 * trackBLinearPrimeConcreteK)

/-- Sparse point ratio between consecutive mesh points. -/
def trackBLinearPrimeConcretePointRatio (j : ℕ) : ℕ :=
  trackBLinearPrimeConcreteBase j ^ (40 * trackBLinearPrimeConcreteK + 8)

/-- Concrete sparse test point. -/
def trackBLinearPrimeConcretePoint (j r : ℕ) : ℕ :=
  trackBLinearPrimeConcretePointScale j * trackBLinearPrimeConcretePointRatio j ^ r

/-- Lower endpoint of the stage block. -/
def trackBLinearPrimeConcreteLo (j : ℕ) : ℕ :=
  trackBLinearPrimeConcretePoint j 1

/-- Upper endpoint of the stage block. -/
def trackBLinearPrimeConcreteHi (j : ℕ) : ℕ :=
  trackBLinearPrimeConcretePoint j (trackBLinearPrimeConcreteQ j)

/-- Lower endpoint of the fresh-prime layer attached to mesh index `r`. -/
def trackBLinearPrimeConcreteFreshLo (j r : ℕ) : ℕ :=
  trackBLinearPrimeConcreteBase j ^ (28 * trackBLinearPrimeConcreteK) *
    trackBLinearPrimeConcretePointRatio j ^ r

/-- Upper endpoint of the fresh-prime layer attached to mesh index `r`. -/
def trackBLinearPrimeConcreteFreshHi (j r : ℕ) : ℕ :=
  trackBLinearPrimeConcreteBase j ^ (29 * trackBLinearPrimeConcreteK) *
    trackBLinearPrimeConcretePointRatio j ^ r

/-- Concrete variance floor target. -/
noncomputable def trackBLinearPrimeConcreteV (j : ℕ) : ℝ :=
  ((trackBLinearPrimeConcreteBase j : ℝ) ^ (20 * trackBLinearPrimeConcreteK))

/-- Concrete threshold level. -/
noncomputable def trackBLinearPrimeConcreteM (j : ℕ) : ℝ :=
  ((trackBLinearPrimeConcreteBase j : ℝ) ^ (10 * trackBLinearPrimeConcreteK - 2))

/-- Concrete threshold buffer. -/
noncomputable def trackBLinearPrimeConcreteBuffer (j : ℕ) : ℝ :=
  trackBLinearPrimeConcreteM j / 2

/-- Concrete overlap-count threshold. -/
def trackBLinearPrimeConcreteR (_j : ℕ) : ℕ :=
  1

/-- Concrete one-point lower-tail budget. -/
noncomputable def trackBLinearPrimeConcreteBeta (_j : ℕ) : ℝ :=
  (1 : ℝ) / 4

/-- Concrete diagonal tail upper bound. -/
noncomputable def trackBLinearPrimeConcreteTailUpper (_j : ℕ) : ℝ :=
  1

/-- Concrete off-diagonal centered covariance budget. -/
noncomputable def trackBLinearPrimeConcretePairCovUpper (j : ℕ) : ℝ :=
  2 * (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹

/-- Concrete expected-count lower budget. -/
noncomputable def trackBLinearPrimeConcreteCountMean (j : ℕ) : ℝ :=
  (trackBLinearPrimeConcreteQ j : ℝ) / 4

/-- Concrete centered second-moment budget for the threshold count. -/
noncomputable def trackBLinearPrimeConcreteCountSecond (j : ℕ) : ℝ :=
  (trackBLinearPrimeConcreteQ j : ℝ) +
    2 * (trackBLinearPrimeConcreteQ j : ℝ) ^ 2 *
      (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹

/-- Concrete coefficient flatness target. -/
noncomputable def trackBLinearPrimeConcreteFlat (j : ℕ) : ℝ :=
  (((trackBLinearPrimeConcreteBase j : ℝ) ^ trackBLinearPrimeConcreteK))⁻¹

/-- Concrete correlation target. -/
noncomputable def trackBLinearPrimeConcreteRho (j : ℕ) : ℝ :=
  (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹

/-- Concrete Gaussian one-point tail proxy. -/
noncomputable def trackBLinearPrimeConcreteGaussianTail (_j _N : ℕ) : ℝ :=
  (1 : ℝ) / 2

/-- Concrete Gaussian pair-tail proxy. -/
noncomputable def trackBLinearPrimeConcreteGaussianPair (j _N _N' : ℕ) : ℝ :=
  (1 : ℝ) / 4 + (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹

/-- Concrete one-point comparison slack. -/
noncomputable def trackBLinearPrimeConcreteOnePointSlack (j : ℕ) : ℝ :=
  (((trackBLinearPrimeConcreteBase j : ℝ) ^ 10))⁻¹

/-- Concrete two-point comparison slack. -/
noncomputable def trackBLinearPrimeConcreteTwoPointSlack (j : ℕ) : ℝ :=
  (((trackBLinearPrimeConcreteBase j : ℝ) ^ 10))⁻¹

/-- Concrete product-comparison slack. -/
noncomputable def trackBLinearPrimeConcreteProductSlack (j : ℕ) : ℝ :=
  (((trackBLinearPrimeConcreteBase j : ℝ) ^ 10))⁻¹

/-- Concrete Gaussian centered pair-covariance proxy. -/
noncomputable def trackBLinearPrimeConcreteGaussianPairCovUpper (j : ℕ) : ℝ :=
  (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹

/-- Concrete good-event failure budget.  The first schedule instantiation uses
the all-space good-event shortcut. -/
def trackBLinearPrimeConcreteFailGood (_j : ℕ) : ℝ≥0∞ :=
  0

/-- Concrete selected-overlap failure budget placeholder.  The analytic
remainder estimate should prove the corresponding one-point union bound. -/
noncomputable def trackBLinearPrimeConcreteFailOverlap (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹)

/-- Concrete Track B fresh-prime schedule spec. -/
noncomputable def trackBLinearPrimeConcreteScheduleSpec :
    TrackBLinearPrimeScheduleSpec where
  lo := trackBLinearPrimeConcreteLo
  hi := trackBLinearPrimeConcreteHi
  M := trackBLinearPrimeConcreteM
  buffer := trackBLinearPrimeConcreteBuffer
  Q := trackBLinearPrimeConcreteQ
  point := trackBLinearPrimeConcretePoint
  freshLo := trackBLinearPrimeConcreteFreshLo
  freshHi := trackBLinearPrimeConcreteFreshHi
  good := fun _j => Set.univ
  r := trackBLinearPrimeConcreteR
  failGood := trackBLinearPrimeConcreteFailGood
  failOverlap := trackBLinearPrimeConcreteFailOverlap
  beta := trackBLinearPrimeConcreteBeta
  tailUpper := trackBLinearPrimeConcreteTailUpper
  pairCovUpper := trackBLinearPrimeConcretePairCovUpper
  countMean := trackBLinearPrimeConcreteCountMean
  countSecond := trackBLinearPrimeConcreteCountSecond
  V := trackBLinearPrimeConcreteV
  flat := trackBLinearPrimeConcreteFlat
  rho := trackBLinearPrimeConcreteRho
  gaussianTail := trackBLinearPrimeConcreteGaussianTail
  gaussianPair := trackBLinearPrimeConcreteGaussianPair
  onePointSlack := trackBLinearPrimeConcreteOnePointSlack
  twoPointSlack := trackBLinearPrimeConcreteTwoPointSlack
  productSlack := trackBLinearPrimeConcreteProductSlack
  gaussianPairCovUpper := trackBLinearPrimeConcreteGaussianPairCovUpper

/-- Concrete Track B fresh-prime schedule data with a configurable good event
and good-event failure budget.  This keeps the polynomial mesh, thresholds,
fresh-prime layers, and scalar budgets fixed while allowing the analytic
variance floor to be proved on a genuine high-probability geometry event
instead of on all of `Omega`. -/
noncomputable def trackBLinearPrimeConcreteScheduleSpecWithGood
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) :
    TrackBLinearPrimeScheduleSpec where
  lo := trackBLinearPrimeConcreteLo
  hi := trackBLinearPrimeConcreteHi
  M := trackBLinearPrimeConcreteM
  buffer := trackBLinearPrimeConcreteBuffer
  Q := trackBLinearPrimeConcreteQ
  point := trackBLinearPrimeConcretePoint
  freshLo := trackBLinearPrimeConcreteFreshLo
  freshHi := trackBLinearPrimeConcreteFreshHi
  good := good
  r := trackBLinearPrimeConcreteR
  failGood := failGood
  failOverlap := trackBLinearPrimeConcreteFailOverlap
  beta := trackBLinearPrimeConcreteBeta
  tailUpper := trackBLinearPrimeConcreteTailUpper
  pairCovUpper := trackBLinearPrimeConcretePairCovUpper
  countMean := trackBLinearPrimeConcreteCountMean
  countSecond := trackBLinearPrimeConcreteCountSecond
  V := trackBLinearPrimeConcreteV
  flat := trackBLinearPrimeConcreteFlat
  rho := trackBLinearPrimeConcreteRho
  gaussianTail := trackBLinearPrimeConcreteGaussianTail
  gaussianPair := trackBLinearPrimeConcreteGaussianPair
  onePointSlack := trackBLinearPrimeConcreteOnePointSlack
  twoPointSlack := trackBLinearPrimeConcreteTwoPointSlack
  productSlack := trackBLinearPrimeConcreteProductSlack
  gaussianPairCovUpper := trackBLinearPrimeConcreteGaussianPairCovUpper

/-- The shifted concrete base is always positive. -/
theorem trackBLinearPrimeConcreteBase_pos (j : ℕ) :
    0 < trackBLinearPrimeConcreteBase j := by
  unfold trackBLinearPrimeConcreteBase
  omega

/-- The shifted concrete base is at least two. -/
theorem trackBLinearPrimeConcreteBase_two_le (j : ℕ) :
    2 ≤ trackBLinearPrimeConcreteBase j := by
  unfold trackBLinearPrimeConcreteBase
  omega

/-- The shifted concrete base is strictly larger than one. -/
theorem trackBLinearPrimeConcreteBase_one_lt (j : ℕ) :
    1 < trackBLinearPrimeConcreteBase j := by
  exact lt_of_lt_of_le (by norm_num) (trackBLinearPrimeConcreteBase_two_le j)

/-- The concrete mesh size is always positive. -/
theorem trackBLinearPrimeConcreteQ_pos (j : ℕ) :
    0 < trackBLinearPrimeConcreteQ j := by
  unfold trackBLinearPrimeConcreteQ
  exact pow_pos (trackBLinearPrimeConcreteBase_pos j) 4

/-- The concrete mesh size is uniformly at least sixteen. -/
theorem trackBLinearPrimeConcreteQ_ge_sixteen (j : ℕ) :
    16 ≤ trackBLinearPrimeConcreteQ j := by
  have hbase : 2 ≤ trackBLinearPrimeConcreteBase j :=
    trackBLinearPrimeConcreteBase_two_le j
  have hpow : 2 ^ 4 ≤ trackBLinearPrimeConcreteBase j ^ 4 :=
    pow_le_pow_left' hbase 4
  simpa [trackBLinearPrimeConcreteQ] using hpow

/-- The concrete overlap-count threshold is positive. -/
theorem trackBLinearPrimeConcrete_r_pos (j : ℕ) :
    0 < trackBLinearPrimeConcreteScheduleSpec.r j := by
  simp [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteR]

/-- The concrete count-mean budget is positive. -/
theorem trackBLinearPrimeConcrete_countMean_pos (j : ℕ) :
    0 < trackBLinearPrimeConcreteScheduleSpec.countMean j := by
  have hQ : (0 : ℝ) < (trackBLinearPrimeConcreteQ j : ℝ) :=
    by exact_mod_cast trackBLinearPrimeConcreteQ_pos j
  simp [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteCountMean, hQ]

/-- The concrete overlap threshold is below half the count-mean budget. -/
theorem trackBLinearPrimeConcrete_r_le_half_countMean (j : ℕ) :
    (trackBLinearPrimeConcreteScheduleSpec.r j : ℝ) ≤
      trackBLinearPrimeConcreteScheduleSpec.countMean j / 2 := by
  have hQ : (8 : ℝ) ≤ (trackBLinearPrimeConcreteQ j : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 8 ≤ 16) (trackBLinearPrimeConcreteQ_ge_sixteen j))
  simp [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteR,
    trackBLinearPrimeConcreteCountMean]
  linarith

/-- The concrete point ratio is strictly larger than one. -/
theorem trackBLinearPrimeConcretePointRatio_one_lt (j : ℕ) :
    1 < trackBLinearPrimeConcretePointRatio j := by
  unfold trackBLinearPrimeConcretePointRatio
  exact one_lt_pow₀ (trackBLinearPrimeConcreteBase_one_lt j) (by omega)

/-- The concrete point scale is positive. -/
theorem trackBLinearPrimeConcretePointScale_pos (j : ℕ) :
    0 < trackBLinearPrimeConcretePointScale j := by
  unfold trackBLinearPrimeConcretePointScale
  exact pow_pos (trackBLinearPrimeConcreteBase_pos j) _

/-- Concrete sparse points are monotone in the mesh index. -/
theorem trackBLinearPrimeConcrete_point_mono
    (j : ℕ) ⦃r s : ℕ⦄ (hrs : r ≤ s) :
    trackBLinearPrimeConcreteScheduleSpec.point j r ≤
      trackBLinearPrimeConcreteScheduleSpec.point j s := by
  have hratio_pos : 0 < trackBLinearPrimeConcretePointRatio j :=
    lt_trans Nat.zero_lt_one (trackBLinearPrimeConcretePointRatio_one_lt j)
  have hpow :
      trackBLinearPrimeConcretePointRatio j ^ r ≤
        trackBLinearPrimeConcretePointRatio j ^ s :=
    Nat.pow_le_pow_right hratio_pos hrs
  simpa [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcretePoint]
    using Nat.mul_le_mul_left (trackBLinearPrimeConcretePointScale j) hpow

/-- Concrete sparse points are strictly increasing in the mesh index. -/
theorem trackBLinearPrimeConcrete_point_strict
    (j : ℕ) ⦃r s : ℕ⦄
    (_hr :
      r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteScheduleSpec.Q j)
    (_hs :
      s ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteScheduleSpec.Q j)
    (hrs : r < s) :
    trackBLinearPrimeConcreteScheduleSpec.point j r <
      trackBLinearPrimeConcreteScheduleSpec.point j s := by
  have hpow :
      trackBLinearPrimeConcretePointRatio j ^ r <
        trackBLinearPrimeConcretePointRatio j ^ s :=
    Nat.pow_lt_pow_right (trackBLinearPrimeConcretePointRatio_one_lt j) hrs
  have hscale : 0 < trackBLinearPrimeConcretePointScale j :=
    trackBLinearPrimeConcretePointScale_pos j
  simpa [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcretePoint]
    using (Nat.mul_lt_mul_left hscale).mpr hpow

/-- The concrete point ratio is positive. -/
theorem trackBLinearPrimeConcretePointRatio_pos (j : ℕ) :
    0 < trackBLinearPrimeConcretePointRatio j :=
  lt_trans Nat.zero_lt_one (trackBLinearPrimeConcretePointRatio_one_lt j)

/-- The point-ratio exponent gap dominates one fresh-interval width. -/
theorem trackBLinearPrimeConcrete_basePowK_lt_pointRatio (j : ℕ) :
    trackBLinearPrimeConcreteBase j ^ trackBLinearPrimeConcreteK <
      trackBLinearPrimeConcretePointRatio j := by
  unfold trackBLinearPrimeConcretePointRatio
  exact Nat.pow_lt_pow_right (trackBLinearPrimeConcreteBase_one_lt j)
    (by norm_num [trackBLinearPrimeConcreteK])

/-- Concrete fresh-prime lower endpoints are monotone in the mesh index. -/
theorem trackBLinearPrimeConcrete_freshLo_mono
    (j : ℕ) ⦃r s : ℕ⦄ (hrs : r ≤ s) :
    trackBLinearPrimeConcreteFreshLo j r ≤ trackBLinearPrimeConcreteFreshLo j s := by
  have hratio_pos : 0 < trackBLinearPrimeConcretePointRatio j :=
    trackBLinearPrimeConcretePointRatio_pos j
  have hpow :
      trackBLinearPrimeConcretePointRatio j ^ r ≤
        trackBLinearPrimeConcretePointRatio j ^ s :=
    Nat.pow_le_pow_right hratio_pos hrs
  simpa [trackBLinearPrimeConcreteFreshLo]
    using
      Nat.mul_le_mul_left
        (trackBLinearPrimeConcreteBase j ^ (28 * trackBLinearPrimeConcreteK)) hpow

/-- Each concrete fresh-prime interval lies strictly before the next one. -/
theorem trackBLinearPrimeConcrete_freshHi_lt_freshLo_succ (j r : ℕ) :
    trackBLinearPrimeConcreteFreshHi j r <
      trackBLinearPrimeConcreteFreshLo j (r + 1) := by
  have hratio_pos : 0 < trackBLinearPrimeConcretePointRatio j :=
    trackBLinearPrimeConcretePointRatio_pos j
  have hsmall : trackBLinearPrimeConcreteBase j ^ trackBLinearPrimeConcreteK <
      trackBLinearPrimeConcretePointRatio j :=
    trackBLinearPrimeConcrete_basePowK_lt_pointRatio j
  have hprefix :
      trackBLinearPrimeConcreteBase j ^ (29 * trackBLinearPrimeConcreteK) <
        trackBLinearPrimeConcreteBase j ^ (28 * trackBLinearPrimeConcreteK) *
          trackBLinearPrimeConcretePointRatio j := by
    have hpow_eq :
        trackBLinearPrimeConcreteBase j ^ (29 * trackBLinearPrimeConcreteK) =
          trackBLinearPrimeConcreteBase j ^ (28 * trackBLinearPrimeConcreteK) *
            trackBLinearPrimeConcreteBase j ^ trackBLinearPrimeConcreteK := by
      have hexp :
          29 * trackBLinearPrimeConcreteK =
            28 * trackBLinearPrimeConcreteK + trackBLinearPrimeConcreteK := by
        norm_num [trackBLinearPrimeConcreteK]
      rw [hexp, pow_add]
    have hfactor_pos :
        0 < trackBLinearPrimeConcreteBase j ^ (28 * trackBLinearPrimeConcreteK) :=
      pow_pos (trackBLinearPrimeConcreteBase_pos j) _
    have hmul :=
      (Nat.mul_lt_mul_left hfactor_pos).mpr hsmall
    simpa [hpow_eq] using hmul
  have hratio_pow_pos : 0 < trackBLinearPrimeConcretePointRatio j ^ r :=
    pow_pos hratio_pos r
  have hmul :=
    (Nat.mul_lt_mul_right hratio_pow_pos).mpr hprefix
  simpa [trackBLinearPrimeConcreteFreshHi, trackBLinearPrimeConcreteFreshLo, pow_succ,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul

/-- Concrete fresh-prime intervals are pairwise disjoint at the endpoint level. -/
theorem trackBLinearPrimeConcrete_fresh_interval_disjoint
    (j r s : ℕ)
    (_hr :
      r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteScheduleSpec.Q j)
    (_hs :
      s ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteScheduleSpec.Q j)
    (hne : r ≠ s) :
    trackBLinearPrimeConcreteScheduleSpec.freshHi j r <
        trackBLinearPrimeConcreteScheduleSpec.freshLo j s ∨
      trackBLinearPrimeConcreteScheduleSpec.freshHi j s <
        trackBLinearPrimeConcreteScheduleSpec.freshLo j r := by
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · refine Or.inl ?_
    exact
      (trackBLinearPrimeConcrete_freshHi_lt_freshLo_succ j r).trans_le
        (trackBLinearPrimeConcrete_freshLo_mono j (Nat.succ_le_of_lt hrs))
  · refine Or.inr ?_
    exact
      (trackBLinearPrimeConcrete_freshHi_lt_freshLo_succ j s).trans_le
        (trackBLinearPrimeConcrete_freshLo_mono j (Nat.succ_le_of_lt hsr))

/-- The concrete test point is exactly the lower fresh endpoint times the
remaining `b^(2K)` divisor scale. -/
theorem trackBLinearPrimeConcrete_point_eq_freshLo_mul_divisorScale (j r : ℕ) :
    trackBLinearPrimeConcretePoint j r =
      trackBLinearPrimeConcreteFreshLo j r *
        trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) := by
  rw [trackBLinearPrimeConcretePoint, trackBLinearPrimeConcretePointScale,
    trackBLinearPrimeConcreteFreshLo]
  have hexp :
      30 * trackBLinearPrimeConcreteK =
        28 * trackBLinearPrimeConcreteK + 2 * trackBLinearPrimeConcreteK := by
    norm_num [trackBLinearPrimeConcreteK]
  rw [hexp, pow_add]
  let b28 := trackBLinearPrimeConcreteBase j ^ (28 * trackBLinearPrimeConcreteK)
  let b2 := trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK)
  let q := trackBLinearPrimeConcretePointRatio j ^ r
  change (b28 * b2) * q = (b28 * q) * b2
  rw [Nat.mul_assoc, Nat.mul_comm b2 q, ← Nat.mul_assoc]

/-- The concrete fresh lower endpoint is at least its base-power part. -/
theorem trackBLinearPrimeConcrete_basePow28K_le_freshLo (j r : ℕ) :
    trackBLinearPrimeConcreteBase j ^ (28 * trackBLinearPrimeConcreteK) ≤
      trackBLinearPrimeConcreteFreshLo j r := by
  have hratio_pow_pos : 0 < trackBLinearPrimeConcretePointRatio j ^ r :=
    pow_pos (trackBLinearPrimeConcretePointRatio_pos j) r
  simpa [trackBLinearPrimeConcreteFreshLo]
    using
      Nat.le_mul_of_pos_right
        (trackBLinearPrimeConcreteBase j ^ (28 * trackBLinearPrimeConcreteK))
        hratio_pow_pos

/-- Every concrete sparse point lies in the concrete stage block. -/
theorem trackBLinearPrimeConcrete_point_in_block
    (j r : ℕ)
    (hr :
      r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteScheduleSpec.Q j) :
    trackBLinearPrimeConcreteScheduleSpec.point j r ∈
      Finset.Icc
        (trackBLinearPrimeConcreteScheduleSpec.lo j)
        (trackBLinearPrimeConcreteScheduleSpec.hi j) := by
  rw [mem_trackBLinearPrimeMeshIndexSet] at hr
  rw [Finset.mem_Icc]
  constructor
  · simpa [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteLo]
      using trackBLinearPrimeConcrete_point_mono j hr.1
  · simpa [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteHi]
      using trackBLinearPrimeConcrete_point_mono j hr.2

/-- The shifted concrete base tends to infinity. -/
theorem trackBLinearPrimeConcreteBase_tendsto_atTop :
    Tendsto trackBLinearPrimeConcreteBase atTop atTop := by
  simpa [trackBLinearPrimeConcreteBase] using tendsto_add_atTop_nat 2

/-- The shifted base is bounded above by the concrete lower stage endpoint. -/
theorem trackBLinearPrimeConcreteBase_le_lo (j : ℕ) :
    trackBLinearPrimeConcreteBase j ≤ trackBLinearPrimeConcreteLo j := by
  have hbase_one : 1 ≤ trackBLinearPrimeConcreteBase j :=
    (trackBLinearPrimeConcreteBase_one_lt j).le
  have hbase_le_scale :
      trackBLinearPrimeConcreteBase j ≤ trackBLinearPrimeConcretePointScale j := by
    unfold trackBLinearPrimeConcretePointScale
    exact le_self_pow hbase_one (by norm_num [trackBLinearPrimeConcreteK])
  have hratio_pos : 0 < trackBLinearPrimeConcretePointRatio j :=
    lt_trans Nat.zero_lt_one (trackBLinearPrimeConcretePointRatio_one_lt j)
  have hscale_le_lo :
      trackBLinearPrimeConcretePointScale j ≤ trackBLinearPrimeConcreteLo j := by
    have hle :
        trackBLinearPrimeConcretePointScale j ≤
          trackBLinearPrimeConcretePointScale j * trackBLinearPrimeConcretePointRatio j :=
      Nat.le_mul_of_pos_right _ hratio_pos
    simpa [trackBLinearPrimeConcreteLo, trackBLinearPrimeConcretePoint] using hle
  exact le_trans hbase_le_scale hscale_le_lo

/-- The concrete lower stage endpoint tends to infinity. -/
theorem trackBLinearPrimeConcreteLo_tendsto_atTop :
    Tendsto trackBLinearPrimeConcreteLo atTop atTop :=
  tendsto_atTop_mono trackBLinearPrimeConcreteBase_le_lo
    trackBLinearPrimeConcreteBase_tendsto_atTop

/-- The concrete threshold level tends to infinity. -/
theorem trackBLinearPrimeConcreteM_tendsto_atTop :
    Tendsto trackBLinearPrimeConcreteM atTop atTop := by
  have hbaseR :
      Tendsto (fun j => (trackBLinearPrimeConcreteBase j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp trackBLinearPrimeConcreteBase_tendsto_atTop
  simpa [trackBLinearPrimeConcreteM]
    using
      (tendsto_pow_atTop
        (by norm_num [trackBLinearPrimeConcreteK] :
          10 * trackBLinearPrimeConcreteK - 2 ≠ 0)).comp hbaseR

/-- The concrete threshold is positive. -/
theorem trackBLinearPrimeConcreteM_pos (j : ℕ) :
    0 < trackBLinearPrimeConcreteM j := by
  unfold trackBLinearPrimeConcreteM
  have hbase : (0 : ℝ) < trackBLinearPrimeConcreteBase j := by
    exact_mod_cast trackBLinearPrimeConcreteBase_pos j
  exact pow_pos hbase _

/-- The concrete variance floor target is nonnegative. -/
theorem trackBLinearPrimeConcreteV_nonneg (j : ℕ) :
    0 ≤ trackBLinearPrimeConcreteV j := by
  unfold trackBLinearPrimeConcreteV
  positivity

/-- The concrete correlation target is nonnegative. -/
theorem trackBLinearPrimeConcreteRho_nonneg (j : ℕ) :
    0 ≤ trackBLinearPrimeConcreteRho j := by
  unfold trackBLinearPrimeConcreteRho
  positivity

/-- The concrete covariance budget is nonnegative. -/
theorem trackBLinearPrimeConcrete_rho_mul_V_nonneg (j : ℕ) :
    0 ≤ trackBLinearPrimeConcreteScheduleSpec.rho j *
      trackBLinearPrimeConcreteScheduleSpec.V j := by
  exact mul_nonneg (trackBLinearPrimeConcreteRho_nonneg j)
    (trackBLinearPrimeConcreteV_nonneg j)

/-- The concrete threshold plus buffer is positive. -/
theorem trackBLinearPrimeConcreteM_add_buffer_pos (j : ℕ) :
    0 < trackBLinearPrimeConcreteM j + trackBLinearPrimeConcreteBuffer j := by
  have hM : 0 < trackBLinearPrimeConcreteM j := trackBLinearPrimeConcreteM_pos j
  unfold trackBLinearPrimeConcreteBuffer
  linarith

/-- The shifted fourth-power reciprocal is summable. -/
theorem trackBLinearPrimeConcrete_inv_base_four_summable :
    Summable fun j : ℕ => (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹ := by
  have hbase : Summable fun n : ℕ => (((n : ℝ) ^ (4 : ℝ)))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 4)
  have hshift :
      Summable fun j : ℕ => ((((j + 2 : ℕ) : ℝ) ^ (4 : ℝ)))⁻¹ := by
    simpa [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff (f := fun n : ℕ => (((n : ℝ) ^ (4 : ℝ)))⁻¹) 2).mpr
        hbase
  simpa [trackBLinearPrimeConcreteBase, Real.rpow_natCast] using hshift

/-- The concrete Chebyshev count-budget term is an explicit shifted
fourth-power reciprocal. -/
theorem trackBLinearPrimeConcrete_countBudget_eq (j : ℕ) :
    4 * trackBLinearPrimeConcreteScheduleSpec.countSecond j /
        trackBLinearPrimeConcreteScheduleSpec.countMean j ^ 2 =
      192 * (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹ := by
  have hb0 : (trackBLinearPrimeConcreteBase j : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (trackBLinearPrimeConcreteBase_pos j))
  have hb : ((trackBLinearPrimeConcreteBase j : ℝ) ^ 4) ≠ 0 := pow_ne_zero 4 hb0
  simp [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteCountSecond,
    trackBLinearPrimeConcreteCountMean, trackBLinearPrimeConcreteQ]
  field_simp [hb]
  ring

/-- Summability of the concrete Chebyshev count-budget term. -/
theorem trackBLinearPrimeConcrete_countBudget_tsum_ne_top :
    (∑' j,
      ENNReal.ofReal
        (4 * trackBLinearPrimeConcreteScheduleSpec.countSecond j /
          trackBLinearPrimeConcreteScheduleSpec.countMean j ^ 2)) ≠ ⊤ := by
  have hs :
      Summable fun j : ℕ =>
        192 * (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹ :=
    trackBLinearPrimeConcrete_inv_base_four_summable.mul_left 192
  simpa [trackBLinearPrimeConcrete_countBudget_eq] using hs.tsum_ofReal_ne_top

/-- Summability of the combined concrete stage failure budget. -/
theorem trackBLinearPrimeConcrete_fail_summable :
    (∑' j,
      (trackBLinearPrimeConcreteScheduleSpec.failGood j +
        ENNReal.ofReal
          (4 * trackBLinearPrimeConcreteScheduleSpec.countSecond j /
            trackBLinearPrimeConcreteScheduleSpec.countMean j ^ 2) +
        trackBLinearPrimeConcreteScheduleSpec.failOverlap j)) ≠ ⊤ := by
  have hfirst :
      (∑' j,
        ENNReal.ofReal
          (4 * trackBLinearPrimeConcreteScheduleSpec.countSecond j /
            trackBLinearPrimeConcreteScheduleSpec.countMean j ^ 2)) ≠ ⊤ :=
    trackBLinearPrimeConcrete_countBudget_tsum_ne_top
  have hoverlap :
      (∑' j, trackBLinearPrimeConcreteScheduleSpec.failOverlap j) ≠ ⊤ := by
    simpa [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteFailOverlap]
      using trackBLinearPrimeConcrete_inv_base_four_summable.tsum_ofReal_ne_top
  have hgood :
      (∑' j, trackBLinearPrimeConcreteScheduleSpec.failGood j) ≠ ⊤ := by
    simp [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteFailGood]
  rw [ENNReal.tsum_add, ENNReal.tsum_add]
  simp only [ne_eq, ENNReal.add_eq_top, not_or]
  exact ⟨⟨hgood, hfirst⟩, hoverlap⟩

/-- Summability of the concrete stage failure budget with an arbitrary
summable good-event failure budget. -/
theorem trackBLinearPrimeConcrete_fail_summable_withGood
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞)
    (hgood :
      (∑' j, (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).failGood j)
        ≠ ⊤) :
    (∑' j,
      ((trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).failGood j +
        ENNReal.ofReal
          (4 * (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).countSecond j /
            (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).countMean j ^ 2) +
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).failOverlap j)) ≠ ⊤ := by
  have hfirst :
      (∑' j,
        ENNReal.ofReal
          (4 * (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).countSecond j /
            (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).countMean j ^ 2))
        ≠ ⊤ := by
    simpa [trackBLinearPrimeConcreteScheduleSpecWithGood,
      trackBLinearPrimeConcreteScheduleSpec]
      using trackBLinearPrimeConcrete_countBudget_tsum_ne_top
  have hoverlap :
      (∑' j, (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).failOverlap j)
        ≠ ⊤ := by
    simpa [trackBLinearPrimeConcreteScheduleSpecWithGood,
      trackBLinearPrimeConcreteFailOverlap]
      using trackBLinearPrimeConcrete_inv_base_four_summable.tsum_ofReal_ne_top
  rw [ENNReal.tsum_add, ENNReal.tsum_add]
  simp only [ne_eq, ENNReal.add_eq_top, not_or]
  exact ⟨⟨hgood, hfirst⟩, hoverlap⟩

/-- Deterministic stage and summability facts for a scheduled Track B spec. -/
structure TrackBLinearPrimeScheduleStageFacts
    (S : TrackBLinearPrimeScheduleSpec) where
  r_pos : ∀ j, 0 < S.r j
  countMean_pos : ∀ j, 0 < S.countMean j
  r_le_half_countMean : ∀ j, (S.r j : ℝ) ≤ S.countMean j / 2
  point_strict :
    ∀ j ⦃r s⦄, r ∈ trackBLinearPrimeMeshIndexSet S.Q j →
      s ∈ trackBLinearPrimeMeshIndexSet S.Q j → r < s → S.point j r < S.point j s
  point_in_block :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet S.Q j →
      S.point j r ∈ Finset.Icc (S.lo j) (S.hi j)
  lo_tendsto_atTop : Tendsto S.lo atTop atTop
  M_tendsto_atTop : Tendsto S.M atTop atTop
  fail_summable :
    (∑' j,
      (S.failGood j +
        ENNReal.ofReal (4 * S.countSecond j / S.countMean j ^ 2) +
        S.failOverlap j)) ≠ ⊤

/-- Stage facts for the concrete Track B linear-prime schedule. -/
noncomputable def trackBLinearPrimeConcreteScheduleStageFacts :
    TrackBLinearPrimeScheduleStageFacts trackBLinearPrimeConcreteScheduleSpec where
  r_pos := trackBLinearPrimeConcrete_r_pos
  countMean_pos := trackBLinearPrimeConcrete_countMean_pos
  r_le_half_countMean := trackBLinearPrimeConcrete_r_le_half_countMean
  point_strict := by
    intro j r s hr hs hrs
    exact trackBLinearPrimeConcrete_point_strict j hr hs hrs
  point_in_block := trackBLinearPrimeConcrete_point_in_block
  lo_tendsto_atTop := trackBLinearPrimeConcreteLo_tendsto_atTop
  M_tendsto_atTop := trackBLinearPrimeConcreteM_tendsto_atTop
  fail_summable := trackBLinearPrimeConcrete_fail_summable

/-- Deterministic stage facts for the concrete Track B schedule with a
configurable good event and summable good-event failure budget. -/
noncomputable def trackBLinearPrimeConcreteScheduleStageFactsWithGood
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞)
    (hfail :
      (∑' j, (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).failGood j)
        ≠ ⊤) :
    TrackBLinearPrimeScheduleStageFacts
      (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood) where
  r_pos := trackBLinearPrimeConcrete_r_pos
  countMean_pos := trackBLinearPrimeConcrete_countMean_pos
  r_le_half_countMean := trackBLinearPrimeConcrete_r_le_half_countMean
  point_strict := by
    intro j r s hr hs hrs
    exact trackBLinearPrimeConcrete_point_strict j hr hs hrs
  point_in_block := trackBLinearPrimeConcrete_point_in_block
  lo_tendsto_atTop := trackBLinearPrimeConcreteLo_tendsto_atTop
  M_tendsto_atTop := trackBLinearPrimeConcreteM_tendsto_atTop
  fail_summable := trackBLinearPrimeConcrete_fail_summable_withGood good failGood hfail

/-- Convert stage facts into the lower-level scheduled stage certificate. -/
noncomputable def TrackBLinearPrimeScheduleStageFacts.toStageCertificate
    {S : TrackBLinearPrimeScheduleSpec}
    (h : TrackBLinearPrimeScheduleStageFacts S) :
    TrackBLinearPrimeScheduledStageCertificate
      S.lo S.hi S.Q S.point S.M S.r S.failGood S.failOverlap
      S.countMean S.countSecond :=
  trackBLinearPrimeScheduledStageCertificate_of_pointwise
    h.r_pos h.countMean_pos h.r_le_half_countMean h.point_in_block
    h.lo_tendsto_atTop h.M_tendsto_atTop h.fail_summable

/-- Good-event measurability and exceptional-probability facts for a schedule. -/
structure TrackBLinearPrimeScheduleGoodEventFacts
    (S : TrackBLinearPrimeScheduleSpec) where
  good_measurable : ∀ j, MeasurableSet (S.good j)
  prob_good_compl : ∀ j, mu (S.good j)ᶜ ≤ S.failGood j

/-- Convert good-event facts into the lower-level good-event certificate. -/
noncomputable def TrackBLinearPrimeScheduleGoodEventFacts.toGoodEventCertificate
    {S : TrackBLinearPrimeScheduleSpec}
    (h : TrackBLinearPrimeScheduleGoodEventFacts S) :
    TrackBLinearPrimeScheduledGoodEventCertificate S.good S.failGood where
  good_measurable := h.good_measurable
  prob_good_compl := h.prob_good_compl

/-- Shortcut for schedules whose good event is all of `Omega` and whose
good-event failure budget is zero. -/
noncomputable def trackBLinearPrimeScheduleGoodEventFacts_univ
    (S : TrackBLinearPrimeScheduleSpec)
    (hgood : S.good = fun _j => Set.univ)
    (hfail : S.failGood = fun _j => 0) :
    TrackBLinearPrimeScheduleGoodEventFacts S where
  good_measurable := by
    intro j
    have hj : S.good j = Set.univ := by simp [hgood]
    rw [hj]
    exact MeasurableSet.univ
  prob_good_compl := by
    intro j
    have hgj : S.good j = Set.univ := by simp [hgood]
    have hfj : S.failGood j = 0 := by simp [hfail]
    rw [hgj, hfj]
    simp

/-- Direct constructor for schedules with a genuine analytic good event. -/
noncomputable def trackBLinearPrimeScheduleGoodEventFacts_of_measurable_prob
    (S : TrackBLinearPrimeScheduleSpec)
    (good_measurable : ∀ j, MeasurableSet (S.good j))
    (prob_good_compl : ∀ j, mu (S.good j)ᶜ ≤ S.failGood j) :
    TrackBLinearPrimeScheduleGoodEventFacts S where
  good_measurable := good_measurable
  prob_good_compl := prob_good_compl

/-- Good-event facts for the concrete schedule with a configurable analytic
good event and failure budget. -/
noncomputable def trackBLinearPrimeConcreteScheduleGoodEventFactsWithGood
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞)
    (good_measurable : ∀ j, MeasurableSet (good j))
    (prob_good_compl : ∀ j, mu (good j)ᶜ ≤ failGood j) :
    TrackBLinearPrimeScheduleGoodEventFacts
      (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood) :=
  trackBLinearPrimeScheduleGoodEventFacts_of_measurable_prob
    (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood)
    good_measurable prob_good_compl

/-- The concrete schedule uses the all-space good event. -/
theorem trackBLinearPrimeConcreteScheduleSpec_good :
    trackBLinearPrimeConcreteScheduleSpec.good = fun _j => Set.univ :=
  rfl

/-- The concrete schedule has zero good-event failure budget. -/
theorem trackBLinearPrimeConcreteScheduleSpec_failGood :
    trackBLinearPrimeConcreteScheduleSpec.failGood = fun _j => 0 :=
  rfl

/-- Good-event facts for the concrete schedule. -/
noncomputable def trackBLinearPrimeConcreteScheduleGoodEventFacts :
    TrackBLinearPrimeScheduleGoodEventFacts trackBLinearPrimeConcreteScheduleSpec :=
  trackBLinearPrimeScheduleGoodEventFacts_univ
    trackBLinearPrimeConcreteScheduleSpec
    trackBLinearPrimeConcreteScheduleSpec_good
    trackBLinearPrimeConcreteScheduleSpec_failGood

/-- Coefficient-geometry facts in the scalar form expected from the final
fresh-prime construction.  Flatness is reduced to the divisor-scale estimate,
and off-diagonal covariance is reduced to interval separation. -/
structure TrackBLinearPrimeScheduleGeometryFacts
    (S : TrackBLinearPrimeScheduleSpec) where
  variance_floor :
    ∀ omega j N, omega ∈ S.good j → N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      S.V j ≤
        trackBLinearPrimeScheduledVariance S.Q S.point S.freshLo S.freshHi omega j N
  coeff_div_bound :
    ∀ j N p, N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      p ∈ trackBLinearPrimeScheduledFreshSet S.Q S.point S.freshLo S.freshHi j N →
        ((N / p : ℕ) : ℝ) * (Real.sqrt ((p : ℕ) : ℝ))⁻¹ ≤ S.flat j
  fresh_interval_disjoint :
    ∀ j r s, r ∈ trackBLinearPrimeMeshIndexSet S.Q j →
      s ∈ trackBLinearPrimeMeshIndexSet S.Q j → r ≠ s →
        S.freshHi j r < S.freshLo j s ∨ S.freshHi j s < S.freshLo j r
  budget_nonneg : ∀ j, 0 ≤ S.rho j * S.V j

/-- Convert scalar geometry facts into the lower-level scheduled geometry
certificate. -/
noncomputable def TrackBLinearPrimeScheduleGeometryFacts.toGeometryCertificate
    {S : TrackBLinearPrimeScheduleSpec}
    (h : TrackBLinearPrimeScheduleGeometryFacts S) :
    TrackBLinearPrimeScheduledGeometryCertificate
      S.Q S.point S.freshLo S.freshHi S.good S.V S.flat S.rho :=
  trackBLinearPrimeScheduledGeometryCertificate_of_interval_disjoint_and_div
    h.variance_floor h.coeff_div_bound h.fresh_interval_disjoint h.budget_nonneg

/-- Coefficient-geometry facts in a direct flatness form.  This is the
preferred schedule-level interface when coefficient flatness is proved by a
genuine analytic good event or random-cancellation estimate rather than by the
crude divisor-support bound. -/
structure TrackBLinearPrimeScheduleDirectGeometryFacts
    (S : TrackBLinearPrimeScheduleSpec) where
  variance_floor :
    ∀ omega j N, omega ∈ S.good j → N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      S.V j ≤
        trackBLinearPrimeScheduledVariance S.Q S.point S.freshLo S.freshHi omega j N
  coeff_flat :
    ∀ omega j N p, omega ∈ S.good j → N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      p ∈ trackBLinearPrimeScheduledFreshSet S.Q S.point S.freshLo S.freshHi j N →
        |trackBLinearPrimeScheduledFreshCoeff S.Q S.point S.freshLo S.freshHi omega j N p|
          ≤ S.flat j
  fresh_interval_disjoint :
    ∀ j r s, r ∈ trackBLinearPrimeMeshIndexSet S.Q j →
      s ∈ trackBLinearPrimeMeshIndexSet S.Q j → r ≠ s →
        S.freshHi j r < S.freshLo j s ∨ S.freshHi j s < S.freshLo j r
  budget_nonneg : ∀ j, 0 ≤ S.rho j * S.V j

/-- Convert direct coefficient-geometry facts into the lower-level scheduled
geometry certificate. -/
noncomputable def TrackBLinearPrimeScheduleDirectGeometryFacts.toGeometryCertificate
    {S : TrackBLinearPrimeScheduleSpec}
    (h : TrackBLinearPrimeScheduleDirectGeometryFacts S) :
    TrackBLinearPrimeScheduledGeometryCertificate
      S.Q S.point S.freshLo S.freshHi S.good S.V S.flat S.rho :=
  trackBLinearPrimeScheduledGeometryCertificate_of_interval_disjoint
    h.variance_floor h.coeff_flat h.fresh_interval_disjoint h.budget_nonneg

/-- The divisor-support geometry interface is a special case of the direct
coefficient-flatness interface. -/
noncomputable def TrackBLinearPrimeScheduleGeometryFacts.toDirectGeometryFacts
    {S : TrackBLinearPrimeScheduleSpec}
    (h : TrackBLinearPrimeScheduleGeometryFacts S) :
    TrackBLinearPrimeScheduleDirectGeometryFacts S where
  variance_floor := h.variance_floor
  coeff_flat := by
    intro omega j N p hgood hN hp
    exact
      trackBLinearPrimeScheduledGeometryCertificate_of_interval_disjoint_and_div
        h.variance_floor h.coeff_div_bound h.fresh_interval_disjoint h.budget_nonneg
        |>.coeff_flat omega j N p hgood hN hp
  fresh_interval_disjoint := h.fresh_interval_disjoint
  budget_nonneg := h.budget_nonneg

/-- One-point and two-point comparison and threshold-count facts for the scheduled
fresh-prime core. -/
structure TrackBLinearPrimeScheduleGaussianTailFacts
    (S : TrackBLinearPrimeScheduleSpec) where
  countMean_le_Q_beta : ∀ j, S.countMean j ≤ (S.Q j : ℝ) * S.beta j
  tailUpper_nonneg : ∀ j, 0 ≤ S.tailUpper j
  pairCovUpper_nonneg : ∀ j, 0 ≤ S.pairCovUpper j
  countSecond_budget :
    ∀ j, (S.Q j : ℝ) * S.tailUpper j + (S.Q j : ℝ) ^ 2 * S.pairCovUpper j ≤
      S.countSecond j
  gaussian_one_point_lower :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      S.beta j + S.onePointSlack j ≤ S.gaussianTail j N
  one_point_compare_lower :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      S.gaussianTail j N - S.onePointSlack j ≤
        mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore S.Q S.point S.freshLo S.freshHi S.good)
            S.M S.buffer j N)
  tail_prob_le_tailUpper :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore S.Q S.point S.freshLo S.freshHi S.good)
            S.M S.buffer j N)
        ≤ S.tailUpper j
  pair_compare_upper :
    ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      N' ∈ trackBLinearPrimeMeshTestSet S.Q S.point j → N ≠ N' →
        mu.real
            (trackBThresholdPairExceedanceEvent
              (trackBLinearPrimeScheduledCore S.Q S.point S.freshLo S.freshHi S.good)
              S.M S.buffer j N N')
          ≤ S.gaussianPair j N N' + S.twoPointSlack j
  gaussian_pair_cov_upper :
    ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      N' ∈ trackBLinearPrimeMeshTestSet S.Q S.point j → N ≠ N' →
        S.gaussianPair j N N' - S.gaussianTail j N * S.gaussianTail j N'
          ≤ S.gaussianPairCovUpper j
  tail_product_compare_lower :
    ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      N' ∈ trackBLinearPrimeMeshTestSet S.Q S.point j → N ≠ N' →
        S.gaussianTail j N * S.gaussianTail j N'
          ≤
            mu.real
              (trackBThresholdExceedanceEvent
                (trackBLinearPrimeScheduledCore S.Q S.point S.freshLo S.freshHi S.good)
                S.M S.buffer j N) *
            mu.real
              (trackBThresholdExceedanceEvent
                (trackBLinearPrimeScheduledCore S.Q S.point S.freshLo S.freshHi S.good)
                S.M S.buffer j N') +
              S.productSlack j
  pairCovBudget_le_pairCovUpper :
    ∀ j,
      S.gaussianPairCovUpper j + S.twoPointSlack j + S.productSlack j
        ≤ S.pairCovUpper j

/-- Convert scalar Gaussian-tail facts into the lower-level scheduled
Gaussian-tail certificate.  Mesh injectivity is obtained from the strict point
growth stored in the stage facts. -/
noncomputable def TrackBLinearPrimeScheduleGaussianTailFacts.toGaussianTailCertificate
    {S : TrackBLinearPrimeScheduleSpec}
    (stage : TrackBLinearPrimeScheduleStageFacts S)
    (h : TrackBLinearPrimeScheduleGaussianTailFacts S) :
    TrackBLinearPrimeScheduledGaussianTailCertificate
      S.Q S.point S.freshLo S.freshHi S.good S.M S.buffer S.beta S.tailUpper
      S.pairCovUpper S.countMean S.countSecond S.gaussianTail S.gaussianPair
      S.onePointSlack S.twoPointSlack S.productSlack S.gaussianPairCovUpper :=
  trackBLinearPrimeScheduledGaussianTailCertificate_of_strict
    stage.point_strict h.countMean_le_Q_beta h.tailUpper_nonneg h.pairCovUpper_nonneg
    h.countSecond_budget h.gaussian_one_point_lower h.one_point_compare_lower
    h.tail_prob_le_tailUpper h.pair_compare_upper h.gaussian_pair_cov_upper
    h.tail_product_compare_lower h.pairCovBudget_le_pairCovUpper

/-- Selected-remainder facts in the one-point form expected from the final
linear-prime analysis. -/
structure TrackBLinearPrimeScheduleRemainderFacts
    (S : TrackBLinearPrimeScheduleSpec) where
  singleFail : ℕ → ℝ≥0∞
  one_point_remainder_bad :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      mu
          {omega |
            trackBLinearPrimeScheduledRemainder
                S.Q S.point S.freshLo S.freshHi S.good omega j N < -S.buffer j}
        ≤ singleFail j
  union_budget : ∀ j, (S.Q j) • singleFail j ≤ S.failOverlap j

/-- One-point lower-tail control for the scheduled formal remainder from its
second moment. -/
theorem measure_trackBLinearPrimeScheduledRemainder_lt_neg_le_second
    (S : TrackBLinearPrimeScheduleSpec)
    (remainderSecond : ℕ → ℕ → ℝ)
    (j N : ℕ)
    (hbuffer : 0 < S.buffer j)
    (hint :
      Integrable
        (fun omega =>
          (trackBLinearPrimeScheduledRemainder
              S.Q S.point S.freshLo S.freshHi S.good omega j N) ^ 2) mu)
    (hsecond :
      (∫ omega,
          (trackBLinearPrimeScheduledRemainder
              S.Q S.point S.freshLo S.freshHi S.good omega j N) ^ 2 ∂mu)
        ≤ remainderSecond j N) :
    mu
        {omega |
          trackBLinearPrimeScheduledRemainder
              S.Q S.point S.freshLo S.freshHi S.good omega j N < -S.buffer j}
      ≤ ENNReal.ofReal (remainderSecond j N / (S.buffer j) ^ 2) := by
  have hsubset :
      {omega |
        trackBLinearPrimeScheduledRemainder
            S.Q S.point S.freshLo S.freshHi S.good omega j N < -S.buffer j} ⊆
        {omega |
          S.buffer j <
            |trackBLinearPrimeScheduledRemainder
              S.Q S.point S.freshLo S.freshHi S.good omega j N|} := by
    intro omega hbad
    change
      trackBLinearPrimeScheduledRemainder
          S.Q S.point S.freshLo S.freshHi S.good omega j N < -S.buffer j at hbad
    have hlt_neg :
        S.buffer j <
          -trackBLinearPrimeScheduledRemainder
            S.Q S.point S.freshLo S.freshHi S.good omega j N := by
      linarith
    exact lt_of_lt_of_le hlt_neg (neg_le_abs _)
  calc
    mu
        {omega |
          trackBLinearPrimeScheduledRemainder
              S.Q S.point S.freshLo S.freshHi S.good omega j N < -S.buffer j}
        ≤ mu
            {omega |
              S.buffer j <
                |trackBLinearPrimeScheduledRemainder
                  S.Q S.point S.freshLo S.freshHi S.good omega j N|} :=
          measure_mono hsubset
    _ ≤ ENNReal.ofReal (remainderSecond j N / (S.buffer j) ^ 2) := by
          exact
            measure_abs_error_gt_le_second
              (E := fun omega =>
                trackBLinearPrimeScheduledRemainder
                  S.Q S.point S.freshLo S.freshHi S.good omega j N)
              (A := S.buffer j)
              (V := remainderSecond j N)
              hbuffer hint hsecond

/-- Selected-remainder facts in a second-moment form.  This is the natural
analytic shape for boundary, flat-tail, and complete-transfer estimates. -/
structure TrackBLinearPrimeScheduleRemainderSecondMomentFacts
    (S : TrackBLinearPrimeScheduleSpec) where
  singleFail : ℕ → ℝ≥0∞
  remainderSecond : ℕ → ℕ → ℝ
  buffer_pos : ∀ j, 0 < S.buffer j
  second_integrable :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeScheduledRemainder
              S.Q S.point S.freshLo S.freshHi S.good omega j N) ^ 2) mu
  second_upper :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      (∫ omega,
          (trackBLinearPrimeScheduledRemainder
              S.Q S.point S.freshLo S.freshHi S.good omega j N) ^ 2 ∂mu)
        ≤ remainderSecond j N
  second_budget :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet S.Q S.point j →
      ENNReal.ofReal (remainderSecond j N / (S.buffer j) ^ 2) ≤ singleFail j
  union_budget : ∀ j, (S.Q j) • singleFail j ≤ S.failOverlap j

/-- Convert scheduled second-moment selected-remainder facts into the
one-point probability form expected by the final schedule wrapper. -/
noncomputable def TrackBLinearPrimeScheduleRemainderSecondMomentFacts.toRemainderFacts
    {S : TrackBLinearPrimeScheduleSpec}
    (h : TrackBLinearPrimeScheduleRemainderSecondMomentFacts S) :
    TrackBLinearPrimeScheduleRemainderFacts S where
  singleFail := h.singleFail
  one_point_remainder_bad := by
    intro j N hN
    exact
      (measure_trackBLinearPrimeScheduledRemainder_lt_neg_le_second
        S h.remainderSecond j N (h.buffer_pos j)
        (h.second_integrable j N hN) (h.second_upper j N hN)).trans
        (h.second_budget j N hN)
  union_budget := h.union_budget

/-- Convert one-point selected-remainder facts into the lower-level scheduled
many-bad-remainders certificate. -/
noncomputable def TrackBLinearPrimeScheduleRemainderFacts.toRemainderCertificate
    {S : TrackBLinearPrimeScheduleSpec}
    (stage : TrackBLinearPrimeScheduleStageFacts S)
    (h : TrackBLinearPrimeScheduleRemainderFacts S) :
    TrackBLinearPrimeScheduledRemainderBadManyCertificate
      S.Q S.point S.freshLo S.freshHi S.good S.buffer S.r S.failOverlap :=
  trackBLinearPrimeScheduledRemainderBadManyCertificate_of_single_strict
    S.Q S.point S.freshLo S.freshHi S.good S.buffer S.r h.singleFail S.failOverlap
    stage.r_pos stage.point_strict h.one_point_remainder_bad h.union_budget

/-- Assemble the scheduled Gaussian-comparison certificate from the schedule
spec and the small fact groups.  This is the intended wiring point for the
remaining Track B analytic package. -/
noncomputable def trackBLinearPrimeScheduledGaussianComparisonCertificate_of_scheduleFacts
    {S : TrackBLinearPrimeScheduleSpec}
    (stage : TrackBLinearPrimeScheduleStageFacts S)
    (good : TrackBLinearPrimeScheduleGoodEventFacts S)
    (geom : TrackBLinearPrimeScheduleGeometryFacts S)
    (tails : TrackBLinearPrimeScheduleGaussianTailFacts S)
    (rem : TrackBLinearPrimeScheduleRemainderFacts S) :
    TrackBLinearPrimeScheduledGaussianComparisonCertificate :=
  trackBLinearPrimeScheduledGaussianComparisonCertificate_of_parts
    stage.toStageCertificate good.toGoodEventCertificate geom.toGeometryCertificate
    (tails.toGaussianTailCertificate stage) (rem.toRemainderCertificate stage)

/-- Assemble the scheduled Gaussian-comparison certificate from direct
coefficient-geometry facts.  Use this variant when flatness is proved
probabilistically or on a nontrivial good event instead of by the divisor-scale
support bound. -/
noncomputable def
    trackBLinearPrimeScheduledGaussianComparisonCertificate_of_scheduleDirectGeometryFacts
    {S : TrackBLinearPrimeScheduleSpec}
    (stage : TrackBLinearPrimeScheduleStageFacts S)
    (good : TrackBLinearPrimeScheduleGoodEventFacts S)
    (geom : TrackBLinearPrimeScheduleDirectGeometryFacts S)
    (tails : TrackBLinearPrimeScheduleGaussianTailFacts S)
    (rem : TrackBLinearPrimeScheduleRemainderFacts S) :
    TrackBLinearPrimeScheduledGaussianComparisonCertificate :=
  trackBLinearPrimeScheduledGaussianComparisonCertificate_of_parts
    stage.toStageCertificate good.toGoodEventCertificate geom.toGeometryCertificate
    (tails.toGaussianTailCertificate stage) (rem.toRemainderCertificate stage)

/-- Direct closure from a schedule spec whose remaining fact groups have been
proved.  `Final.lean` should keep using the old active route until this
certificate is instantiated for a concrete schedule. -/
theorem erdos1144_of_trackBLinearPrimeScheduleFacts
    {S : TrackBLinearPrimeScheduleSpec}
    (stage : TrackBLinearPrimeScheduleStageFacts S)
    (good : TrackBLinearPrimeScheduleGoodEventFacts S)
    (geom : TrackBLinearPrimeScheduleGeometryFacts S)
    (tails : TrackBLinearPrimeScheduleGaussianTailFacts S)
    (rem : TrackBLinearPrimeScheduleRemainderFacts S) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeScheduledGaussianComparisonCertificate
    (trackBLinearPrimeScheduledGaussianComparisonCertificate_of_scheduleFacts
      stage good geom tails rem)

/-- Direct closure from a schedule spec whose geometry facts are supplied in
the direct coefficient-flatness form. -/
theorem erdos1144_of_trackBLinearPrimeScheduleDirectGeometryFacts
    {S : TrackBLinearPrimeScheduleSpec}
    (stage : TrackBLinearPrimeScheduleStageFacts S)
    (good : TrackBLinearPrimeScheduleGoodEventFacts S)
    (geom : TrackBLinearPrimeScheduleDirectGeometryFacts S)
    (tails : TrackBLinearPrimeScheduleGaussianTailFacts S)
    (rem : TrackBLinearPrimeScheduleRemainderFacts S) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeScheduledGaussianComparisonCertificate
    (trackBLinearPrimeScheduledGaussianComparisonCertificate_of_scheduleDirectGeometryFacts
      stage good geom tails rem)

end Problem1144
end Erdos
