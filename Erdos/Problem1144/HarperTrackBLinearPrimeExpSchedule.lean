import Mathlib.Analysis.Complex.ExponentialBounds
import Erdos.Problem1144.HarperTrackBLinearPrimeScheduleScalar
import Erdos.Problem1144.RademacherConcentration

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

namespace Erdos
namespace Problem1144

/-- Deterministic `L^2` stability for the product/rough decomposition: if the
error energy is at most one quarter of the main energy, then the perturbed
energy keeps at least one quarter of the main energy. -/
theorem sum_sq_add_lower_of_four_error_energy_le_signal_energy {α : Type*}
    (s : Finset α) (A E : α → ℝ)
    (hE : 4 * (∑ i ∈ s, E i ^ 2) ≤ ∑ i ∈ s, A i ^ 2) :
    (1 / 4 : ℝ) * (∑ i ∈ s, A i ^ 2) ≤ ∑ i ∈ s, (A i + E i) ^ 2 := by
  let S : ℝ := ∑ i ∈ s, A i ^ 2
  let T : ℝ := ∑ i ∈ s, E i ^ 2
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun i _hi => sq_nonneg (A i))
  have hT_le : T ≤ (1 / 4 : ℝ) * S := by
    dsimp [S, T] at hE ⊢
    nlinarith
  have hpoint : ∀ i ∈ s, (1 / 2 : ℝ) * A i ^ 2 - E i ^ 2 ≤ (A i + E i) ^ 2 := by
    intro i _hi
    nlinarith [sq_nonneg (A i + 2 * E i)]
  have hsum :
      (∑ i ∈ s, ((1 / 2 : ℝ) * A i ^ 2 - E i ^ 2)) ≤
        ∑ i ∈ s, (A i + E i) ^ 2 :=
    Finset.sum_le_sum hpoint
  have hmain : (1 / 4 : ℝ) * S ≤ (1 / 2 : ℝ) * S - T := by
    nlinarith
  calc
    (1 / 4 : ℝ) * S ≤ (1 / 2 : ℝ) * S - T := hmain
    _ = ∑ i ∈ s, ((1 / 2 : ℝ) * A i ^ 2 - E i ^ 2) := by
      dsimp [S, T]
      rw [Finset.sum_sub_distrib]
      simp [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, (A i + E i) ^ 2 := hsum

/-!
## Exponential-endpoint Track B schedule skeleton

The proof collection uses logarithmic times `t_{j,r}` and actual endpoints
`N_{j,r} = floor(exp(t_{j,r}))`.  The first concrete Lean schedule used the
polynomial time scale as the endpoint itself.  This file starts a corrected
endpoint schedule by using `2 ^ t_{j,r}` as an integer exponential surrogate.

Deterministic stage, all-space good-event, fresh-layer separation, and
mesh-point layer rewrites are proved here.  The file also packages the scalar
Gaussian-tail arithmetic for the exponential endpoint schedule.  The actual
variance/flatness, Rademacher-comparison, and remainder estimates still need
analytic inputs for the corrected endpoint scale.
-/

/-- Logarithmic time scale for the exponential-endpoint schedule. -/
def trackBLinearPrimeExpTime (j r : ℕ) : ℕ :=
  trackBLinearPrimeConcretePoint j r

/-- Exponential endpoint surrogate corresponding to `N = exp(t)`. -/
def trackBLinearPrimeExpPoint (j r : ℕ) : ℕ :=
  2 ^ trackBLinearPrimeExpTime j r

/-- Exponential lower endpoint of the fresh-prime layer. -/
def trackBLinearPrimeExpFreshLo (j r : ℕ) : ℕ :=
  2 ^ (trackBLinearPrimeConcreteBase j ^ (28 * trackBLinearPrimeConcreteK) *
    trackBLinearPrimeConcretePointRatio j ^ r)

/-- Exponential upper endpoint of the fresh-prime layer. -/
def trackBLinearPrimeExpFreshHi (j r : ℕ) : ℕ :=
  2 ^ (trackBLinearPrimeConcreteBase j ^ (29 * trackBLinearPrimeConcreteK) *
    trackBLinearPrimeConcretePointRatio j ^ r)

/-- Lower block endpoint for the exponential schedule. -/
def trackBLinearPrimeExpLo (j : ℕ) : ℕ :=
  trackBLinearPrimeExpPoint j 1

/-- Upper block endpoint for the exponential schedule. -/
def trackBLinearPrimeExpHi (j : ℕ) : ℕ :=
  trackBLinearPrimeExpPoint j (trackBLinearPrimeConcreteQ j)

/-- Corrected exponential-endpoint schedule skeleton. -/
def trackBLinearPrimeExpScheduleSpec : TrackBLinearPrimeScheduleSpec where
  lo := trackBLinearPrimeExpLo
  hi := trackBLinearPrimeExpHi
  M := trackBLinearPrimeConcreteM
  buffer := trackBLinearPrimeConcreteBuffer
  Q := trackBLinearPrimeConcreteQ
  point := trackBLinearPrimeExpPoint
  freshLo := trackBLinearPrimeExpFreshLo
  freshHi := trackBLinearPrimeExpFreshHi
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

/-- Corrected exponential-endpoint schedule with a configurable analytic good
event and failure budget. -/
def trackBLinearPrimeExpScheduleSpecWithGood
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) :
    TrackBLinearPrimeScheduleSpec where
  lo := trackBLinearPrimeExpLo
  hi := trackBLinearPrimeExpHi
  M := trackBLinearPrimeConcreteM
  buffer := trackBLinearPrimeConcreteBuffer
  Q := trackBLinearPrimeConcreteQ
  point := trackBLinearPrimeExpPoint
  freshLo := trackBLinearPrimeExpFreshLo
  freshHi := trackBLinearPrimeExpFreshHi
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

/-- Mesh test set for the exponential schedule.  This abbreviation keeps the
geometry-good event statements small enough for Lean to normalize reliably. -/
def trackBLinearPrimeExpMeshTestSet (j : ℕ) : Finset ℕ :=
  trackBLinearPrimeMeshTestSet
    trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j

/-- Scheduled fresh-prime set for the exponential schedule. -/
def trackBLinearPrimeExpScheduledFreshSet (j N : ℕ) : Finset ℕ :=
  trackBLinearPrimeScheduledFreshSet
    trackBLinearPrimeExpScheduleSpec.Q
    trackBLinearPrimeExpScheduleSpec.point
    trackBLinearPrimeExpScheduleSpec.freshLo
    trackBLinearPrimeExpScheduleSpec.freshHi j N

/-- Scheduled fresh coefficient for the exponential schedule. -/
noncomputable def trackBLinearPrimeExpScheduledFreshCoeff
    (omega : Omega) (j N p : ℕ) : ℝ :=
  trackBLinearPrimeScheduledFreshCoeff
    trackBLinearPrimeExpScheduleSpec.Q
    trackBLinearPrimeExpScheduleSpec.point
    trackBLinearPrimeExpScheduleSpec.freshLo
    trackBLinearPrimeExpScheduleSpec.freshHi omega j N p

/-- Scheduled fresh-coefficient variance for the exponential schedule. -/
noncomputable def trackBLinearPrimeExpScheduledVariance
    (omega : Omega) (j N : ℕ) : ℝ :=
  trackBLinearPrimeScheduledVariance
    trackBLinearPrimeExpScheduleSpec.Q
    trackBLinearPrimeExpScheduleSpec.point
    trackBLinearPrimeExpScheduleSpec.freshLo
    trackBLinearPrimeExpScheduleSpec.freshHi omega j N

/-- Compact proposition for one exponential scheduled coefficient satisfying
the target flatness bound.  Keeping this as an alias avoids repeatedly
expanding the scheduled coefficient inside public geometry-good statements. -/
def trackBLinearPrimeExpScheduledCoeffFlat
    (omega : Omega) (j N p : ℕ) : Prop :=
  |trackBLinearPrimeExpScheduledFreshCoeff omega j N p| ≤
    trackBLinearPrimeExpScheduleSpec.flat j

theorem trackBLinearPrimeExpPoint_mono
    (j : ℕ) ⦃r s : ℕ⦄ (hrs : r ≤ s) :
    trackBLinearPrimeExpScheduleSpec.point j r ≤
      trackBLinearPrimeExpScheduleSpec.point j s := by
  have htime :
      trackBLinearPrimeExpTime j r ≤ trackBLinearPrimeExpTime j s := by
    simpa [trackBLinearPrimeExpTime, trackBLinearPrimeConcreteScheduleSpec]
      using trackBLinearPrimeConcrete_point_mono j hrs
  simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeExpPoint] using
    Nat.pow_le_pow_right (by norm_num : 0 < 2) htime

theorem trackBLinearPrimeExpPoint_strict
    (j : ℕ) ⦃r s : ℕ⦄
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j)
    (hs : s ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j)
    (hrs : r < s) :
    trackBLinearPrimeExpScheduleSpec.point j r <
      trackBLinearPrimeExpScheduleSpec.point j s := by
  have htime :
      trackBLinearPrimeExpTime j r < trackBLinearPrimeExpTime j s := by
    exact
      trackBLinearPrimeConcrete_point_strict j
        (by simpa [trackBLinearPrimeExpScheduleSpec] using hr)
        (by simpa [trackBLinearPrimeExpScheduleSpec] using hs) hrs
  simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeExpPoint] using
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) htime

theorem trackBLinearPrimeExpPoint_in_block
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j) :
    trackBLinearPrimeExpScheduleSpec.point j r ∈
      Finset.Icc (trackBLinearPrimeExpScheduleSpec.lo j)
        (trackBLinearPrimeExpScheduleSpec.hi j) := by
  rw [mem_trackBLinearPrimeMeshIndexSet] at hr
  rw [Finset.mem_Icc]
  constructor
  · simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeExpLo]
      using trackBLinearPrimeExpPoint_mono j hr.1
  · simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeExpHi]
      using trackBLinearPrimeExpPoint_mono j hr.2

theorem trackBLinearPrimeConcreteLo_le_expLo (j : ℕ) :
    trackBLinearPrimeConcreteLo j ≤ trackBLinearPrimeExpLo j := by
  have htime_le :
      trackBLinearPrimeConcreteLo j ≤ 2 ^ trackBLinearPrimeConcreteLo j :=
    (trackBLinearPrimeConcreteLo j).lt_two_pow_self.le
  simpa [trackBLinearPrimeExpLo, trackBLinearPrimeExpPoint, trackBLinearPrimeExpTime,
    trackBLinearPrimeConcreteLo] using htime_le

theorem trackBLinearPrimeExpLo_tendsto_atTop :
    Tendsto trackBLinearPrimeExpLo atTop atTop :=
  tendsto_atTop_mono trackBLinearPrimeConcreteLo_le_expLo
    trackBLinearPrimeConcreteLo_tendsto_atTop

theorem trackBLinearPrimeExpScheduleSpec_good :
    trackBLinearPrimeExpScheduleSpec.good = fun _j => Set.univ :=
  rfl

theorem trackBLinearPrimeExpScheduleSpec_failGood :
    trackBLinearPrimeExpScheduleSpec.failGood = fun _j => 0 :=
  rfl

/-- Exponential fresh-prime lower endpoints are monotone in the mesh index. -/
theorem trackBLinearPrimeExpFreshLo_mono
    (j : ℕ) ⦃r s : ℕ⦄ (hrs : r ≤ s) :
    trackBLinearPrimeExpFreshLo j r ≤ trackBLinearPrimeExpFreshLo j s := by
  have hraw :
      trackBLinearPrimeConcreteFreshLo j r ≤ trackBLinearPrimeConcreteFreshLo j s :=
    trackBLinearPrimeConcrete_freshLo_mono j hrs
  simpa [trackBLinearPrimeExpFreshLo, trackBLinearPrimeConcreteFreshLo] using
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hraw

/-- Each exponential fresh-prime interval lies strictly before the next one. -/
theorem trackBLinearPrimeExpFreshHi_lt_freshLo_succ (j r : ℕ) :
    trackBLinearPrimeExpFreshHi j r < trackBLinearPrimeExpFreshLo j (r + 1) := by
  have hraw :
      trackBLinearPrimeConcreteFreshHi j r <
        trackBLinearPrimeConcreteFreshLo j (r + 1) :=
    trackBLinearPrimeConcrete_freshHi_lt_freshLo_succ j r
  simpa [trackBLinearPrimeExpFreshHi, trackBLinearPrimeExpFreshLo,
    trackBLinearPrimeConcreteFreshHi, trackBLinearPrimeConcreteFreshLo] using
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) hraw

/-- Exponential fresh-prime intervals are pairwise disjoint in explicit form. -/
theorem trackBLinearPrimeExpFresh_interval_disjoint_explicit
    (j r s : ℕ)
    (_hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j)
    (_hs : s ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j)
    (hne : r ≠ s) :
    trackBLinearPrimeExpFreshHi j r < trackBLinearPrimeExpFreshLo j s ∨
      trackBLinearPrimeExpFreshHi j s < trackBLinearPrimeExpFreshLo j r := by
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · refine Or.inl ?_
    exact
      (trackBLinearPrimeExpFreshHi_lt_freshLo_succ j r).trans_le
        (trackBLinearPrimeExpFreshLo_mono j (Nat.succ_le_of_lt hrs))
  · refine Or.inr ?_
    exact
      (trackBLinearPrimeExpFreshHi_lt_freshLo_succ j s).trans_le
        (trackBLinearPrimeExpFreshLo_mono j (Nat.succ_le_of_lt hsr))

/-- Exponential fresh-prime intervals are pairwise disjoint in schedule form. -/
theorem trackBLinearPrimeExp_fresh_interval_disjoint
    (j r s : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j)
    (hs : s ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j)
    (hne : r ≠ s) :
    trackBLinearPrimeExpScheduleSpec.freshHi j r <
        trackBLinearPrimeExpScheduleSpec.freshLo j s ∨
      trackBLinearPrimeExpScheduleSpec.freshHi j s <
        trackBLinearPrimeExpScheduleSpec.freshLo j r := by
  simpa [trackBLinearPrimeExpScheduleSpec] using
    trackBLinearPrimeExpFresh_interval_disjoint_explicit j r s
      (by simpa [trackBLinearPrimeExpScheduleSpec] using hr)
      (by simpa [trackBLinearPrimeExpScheduleSpec] using hs) hne

/-- The exponential schedule uses the same nonnegative covariance budget as the
concrete scalar schedule. -/
theorem trackBLinearPrimeExp_rho_mul_V_nonneg (j : ℕ) :
    0 ≤ trackBLinearPrimeExpScheduleSpec.rho j * trackBLinearPrimeExpScheduleSpec.V j := by
  simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteScheduleSpec] using
    trackBLinearPrimeConcrete_rho_mul_V_nonneg j

/-- The exponential scheduled fresh set at a mesh point is exactly the single
fresh-prime layer attached to that mesh index. -/
theorem trackBLinearPrimeExp_scheduledFreshSet_eq_layer
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j) :
    trackBLinearPrimeScheduledFreshSet
        trackBLinearPrimeExpScheduleSpec.Q
        trackBLinearPrimeExpScheduleSpec.point
        trackBLinearPrimeExpScheduleSpec.freshLo
        trackBLinearPrimeExpScheduleSpec.freshHi
        j (trackBLinearPrimeExpScheduleSpec.point j r) =
      trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) := by
  refine trackBLinearPrimeScheduledFreshSet_eq_layer_of_unique hr ?_
  intro s hs hpoint
  have hinj :
      Set.InjOn (trackBLinearPrimeExpScheduleSpec.point j)
        (trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j : Set ℕ) := by
    refine trackBLinearPrimeMesh_injOn_of_strict
      trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j ?_
    intro a b ha hb hab
    exact trackBLinearPrimeExpPoint_strict j ha hb hab
  exact hinj (by simpa using hs) (by simpa using hr) hpoint

/-- Exponential scheduled variance at a mesh point, rewritten over the explicit
fresh-prime layer attached to that mesh index. -/
theorem trackBLinearPrimeExp_scheduledVariance_eq_layer
    (omega : Omega) (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j) :
    trackBLinearPrimeScheduledVariance
        trackBLinearPrimeExpScheduleSpec.Q
        trackBLinearPrimeExpScheduleSpec.point
        trackBLinearPrimeExpScheduleSpec.freshLo
        trackBLinearPrimeExpScheduleSpec.freshHi
        omega j (trackBLinearPrimeExpScheduleSpec.point j r) =
      ∑ p ∈
        trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
        (trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p) ^ 2 := by
  unfold trackBLinearPrimeScheduledVariance trackBLinearPrimeVariance
  rw [trackBLinearPrimeExp_scheduledFreshSet_eq_layer j r hr]

/-- Expected exponential scheduled variance at a mesh point, rewritten over the
single explicit fresh-prime layer attached to that mesh index. -/
theorem integral_trackBLinearPrimeExp_scheduledVariance_eq_layer
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j) :
    ∫ omega,
        trackBLinearPrimeScheduledVariance
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu =
      ∑ p ∈
        trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
        ∑ m ∈
          trackBSquarefreeFreshCoeffSupport
            (trackBFreshPrimeLayer
              (trackBLinearPrimeExpScheduleSpec.freshLo j r)
              (trackBLinearPrimeExpScheduleSpec.freshHi j r))
            (trackBLinearPrimeExpScheduleSpec.point j r) p,
          ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2 := by
  rw [integral_trackBLinearPrimeScheduledVariance_eq]
  rw [trackBLinearPrimeExp_scheduledFreshSet_eq_layer j r hr]

/-- Explicit fresh-prime layer for the exponential schedule at mesh index `r`. -/
def trackBLinearPrimeExpFreshLayer (j r : ℕ) : Finset ℕ :=
  trackBFreshPrimeLayer
    (trackBLinearPrimeExpScheduleSpec.freshLo j r)
    (trackBLinearPrimeExpScheduleSpec.freshHi j r)

/-- Coefficient support for a fixed exponential fresh-prime layer. -/
noncomputable def trackBLinearPrimeExpLayerCoeffSupport (j r p : ℕ) : Finset ℕ :=
  trackBSquarefreeFreshCoeffSupport
    (trackBLinearPrimeExpFreshLayer j r)
    (trackBLinearPrimeExpScheduleSpec.point j r) p

/-- A boundary-safe sub-support for the exponential layer.  It keeps only
coefficients `m` for which the stronger estimate `freshHi * m <= N` holds, so
`p * m <= N` follows uniformly for every fresh prime `p <= freshHi`. -/
noncomputable def trackBLinearPrimeExpSupportBulk (j r p : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.Icc 1 (trackBLinearPrimeExpScheduleSpec.point j r)).filter fun m =>
      Squarefree m ∧ ¬ (p ∣ m) ∧ trackBNoFreshFactor (trackBLinearPrimeExpFreshLayer j r) m ∧
        trackBLinearPrimeExpScheduleSpec.freshHi j r * m ≤
          trackBLinearPrimeExpScheduleSpec.point j r

/-- The boundary-safe bulk set is contained in the exact Lean coefficient
support. -/
theorem trackBLinearPrimeExpSupportBulk_subset_layerCoeffSupport
    {j r p : ℕ} (hp : p ∈ trackBLinearPrimeExpFreshLayer j r) :
    trackBLinearPrimeExpSupportBulk j r p ⊆
      trackBLinearPrimeExpLayerCoeffSupport j r p := by
  classical
  intro m hm
  rw [trackBLinearPrimeExpSupportBulk, Finset.mem_filter] at hm
  rcases hm with ⟨hmIcc, hsq, hp_not_dvd, hnoFresh, hhi_mul⟩
  rw [Finset.mem_Icc] at hmIcc
  have hp_hi :
      p ≤ trackBLinearPrimeExpScheduleSpec.freshHi j r := by
    simpa [trackBLinearPrimeExpFreshLayer] using
      (mem_trackBFreshPrimeLayer.mp hp).2.1
  have hp_prime : Nat.Prime p := by
    exact (mem_trackBFreshPrimeLayer.mp hp).2.2
  have hpm_le :
      p * m ≤ trackBLinearPrimeExpScheduleSpec.point j r := by
    exact (Nat.mul_le_mul_right m hp_hi).trans hhi_mul
  have hm_div :
      m ≤ trackBLinearPrimeExpScheduleSpec.point j r / p := by
    exact (Nat.le_div_iff_mul_le hp_prime.pos).mpr (by simpa [Nat.mul_comm] using hpm_le)
  exact
    mem_trackBSquarefreeFreshCoeffSupport.mpr
      ⟨hmIcc.1, hm_div, hsq, hp_not_dvd, hnoFresh, hpm_le⟩

/-- Reciprocal mass of one coefficient support in the exponential fresh-prime
layer. -/
noncomputable def trackBLinearPrimeExpSupportReciprocalMass (j r p : ℕ) : ℝ :=
  ∑ m ∈ trackBLinearPrimeExpLayerCoeffSupport j r p, (m : ℝ)⁻¹

/-- Reciprocal mass of an arbitrary finite natural-number set.  This is useful
when an analytic proof lower-bounds the exact support by working on a cleaner
subset first. -/
noncomputable def trackBLinearPrimeExpReciprocalMassOn (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, (n : ℝ)⁻¹

/-- Reciprocal mass of a finite natural-number set is nonnegative. -/
theorem trackBLinearPrimeExpReciprocalMassOn_nonneg (S : Finset ℕ) :
    0 ≤ trackBLinearPrimeExpReciprocalMassOn S := by
  unfold trackBLinearPrimeExpReciprocalMassOn
  exact Finset.sum_nonneg fun n _hn => inv_nonneg.mpr (Nat.cast_nonneg n)

/-- Reciprocal mass is monotone under finite-set inclusion. -/
theorem trackBLinearPrimeExpReciprocalMassOn_mono
    {S T : Finset ℕ} (hST : S ⊆ T) :
    trackBLinearPrimeExpReciprocalMassOn S ≤ trackBLinearPrimeExpReciprocalMassOn T := by
  unfold trackBLinearPrimeExpReciprocalMassOn
  exact
    Finset.sum_le_sum_of_subset_of_nonneg hST
      (by
        intro n _hnT _hnS
        exact inv_nonneg.mpr (Nat.cast_nonneg n))

/-- Boundary-safe sifted core used for support-bulk lower bounds.  Compared
with `trackBLinearPrimeExpSupportBulk`, this set removes the redundant
`p ∤ m` condition and uses the uniform cutoff `N / freshHi`, so it is
independent of the particular fresh prime `p`. -/
noncomputable def trackBLinearPrimeExpSupportBulkSieveCore (j r : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.Icc 1
      (trackBLinearPrimeExpScheduleSpec.point j r /
        trackBLinearPrimeExpScheduleSpec.freshHi j r)).filter fun m =>
      Squarefree m ∧ trackBNoFreshFactor (trackBLinearPrimeExpFreshLayer j r) m

/-- The p-independent sifted core is contained in every p-coordinate
boundary-safe support bulk. -/
theorem trackBLinearPrimeExpSupportBulkSieveCore_subset_supportBulk
    {j r p : ℕ} (hp : p ∈ trackBLinearPrimeExpFreshLayer j r) :
    trackBLinearPrimeExpSupportBulkSieveCore j r ⊆
      trackBLinearPrimeExpSupportBulk j r p := by
  classical
  intro m hm
  rw [trackBLinearPrimeExpSupportBulkSieveCore, Finset.mem_filter] at hm
  rcases hm with ⟨hmIcc, hsq, hnoFresh⟩
  rw [Finset.mem_Icc] at hmIcc
  rw [trackBLinearPrimeExpSupportBulk, Finset.mem_filter, Finset.mem_Icc]
  have hhi_pos : 0 < trackBLinearPrimeExpScheduleSpec.freshHi j r := by
    simp [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeExpFreshHi]
  have hhi_mul :
      trackBLinearPrimeExpScheduleSpec.freshHi j r * m ≤
        trackBLinearPrimeExpScheduleSpec.point j r := by
    have hmul :
        m * trackBLinearPrimeExpScheduleSpec.freshHi j r ≤
          trackBLinearPrimeExpScheduleSpec.point j r :=
      (Nat.le_div_iff_mul_le hhi_pos).mp hmIcc.2
    simpa [Nat.mul_comm] using hmul
  have hm_le_point : m ≤ trackBLinearPrimeExpScheduleSpec.point j r :=
    hmIcc.2.trans (Nat.div_le_self _ _)
  have hp_not_dvd : ¬p ∣ m := by
    intro hp_dvd
    have hp_prime : Nat.Prime p := (mem_trackBFreshPrimeLayer.mp hp).2.2
    have hp_kernel : p ∈ sfKernel m :=
      (mem_sfKernel_iff_dvd_of_squarefree hsq hp_prime).mpr hp_dvd
    exact (Finset.disjoint_left.mp hnoFresh hp_kernel hp).elim
  exact ⟨⟨hmIcc.1, hm_le_point⟩, hsq, hp_not_dvd, hnoFresh, hhi_mul⟩

/-- Trivial harmonic upper set for a coefficient support: forget squarefreeness,
freshness, and divisibility, keeping only the interval `1 <= m <= N / p`. -/
noncomputable def trackBLinearPrimeExpSupportHarmonicUpper (j r p : ℕ) : ℝ :=
  trackBLinearPrimeExpReciprocalMassOn
    (Finset.Icc 1 (trackBLinearPrimeExpScheduleSpec.point j r / p))

/-- The trivial harmonic upper mass is nonnegative. -/
theorem trackBLinearPrimeExpSupportHarmonicUpper_nonneg (j r p : ℕ) :
    0 ≤ trackBLinearPrimeExpSupportHarmonicUpper j r p := by
  unfold trackBLinearPrimeExpSupportHarmonicUpper
  exact trackBLinearPrimeExpReciprocalMassOn_nonneg _

/-- The exact coefficient support is contained in its trivial harmonic
interval. -/
theorem trackBLinearPrimeExpLayerCoeffSupport_subset_harmonicUpperSet
    (j r p : ℕ) :
    trackBLinearPrimeExpLayerCoeffSupport j r p ⊆
      Finset.Icc 1 (trackBLinearPrimeExpScheduleSpec.point j r / p) := by
  intro m hm
  have hmem :
      m ∈
        trackBSquarefreeFreshCoeffSupport
          (trackBLinearPrimeExpFreshLayer j r)
          (trackBLinearPrimeExpScheduleSpec.point j r) p := by
    simpa [trackBLinearPrimeExpLayerCoeffSupport] using hm
  rw [Finset.mem_Icc]
  exact ⟨(mem_trackBSquarefreeFreshCoeffSupport.mp hmem).1,
    (mem_trackBSquarefreeFreshCoeffSupport.mp hmem).2.1⟩

/-- The exact support reciprocal mass is bounded by the trivial harmonic
interval upper bound. -/
theorem trackBLinearPrimeExpSupportReciprocalMass_le_harmonicUpper
    (j r p : ℕ) :
    trackBLinearPrimeExpSupportReciprocalMass j r p ≤
      trackBLinearPrimeExpSupportHarmonicUpper j r p := by
  simpa [trackBLinearPrimeExpSupportReciprocalMass,
    trackBLinearPrimeExpSupportHarmonicUpper] using
    trackBLinearPrimeExpReciprocalMassOn_mono
      (trackBLinearPrimeExpLayerCoeffSupport_subset_harmonicUpperSet j r p)

/-- Reciprocal-prime mass of the exponential fresh-prime layer. -/
noncomputable def trackBLinearPrimeExpFreshPrimeReciprocalMass (j r : ℕ) : ℝ :=
  ∑ p ∈ trackBLinearPrimeExpFreshLayer j r, (p : ℝ)⁻¹

/-- Deterministic weighted reciprocal mass whose value is the expected layer
variance.  This is the paper-side scalar target for rough/sieve estimates. -/
noncomputable def trackBLinearPrimeExpLayerWeightedSupportMass (j r : ℕ) : ℝ :=
  ∑ p ∈ trackBLinearPrimeExpFreshLayer j r,
    (p : ℝ)⁻¹ * trackBLinearPrimeExpSupportReciprocalMass j r p

/-- A uniform lower bound for every coefficient-support reciprocal mass gives
a lower bound for the weighted support mass by the fresh-prime reciprocal mass. -/
theorem trackBLinearPrimeExp_supportFloor_mul_primeMass_le_weightedSupportMass
    (supportFloor : ℕ → ℕ → ℝ) (j r : ℕ)
    (hsupport :
      ∀ p, p ∈ trackBLinearPrimeExpFreshLayer j r →
        supportFloor j r ≤ trackBLinearPrimeExpSupportReciprocalMass j r p) :
    supportFloor j r * trackBLinearPrimeExpFreshPrimeReciprocalMass j r ≤
      trackBLinearPrimeExpLayerWeightedSupportMass j r := by
  classical
  calc
    supportFloor j r * trackBLinearPrimeExpFreshPrimeReciprocalMass j r
        = ∑ p ∈ trackBLinearPrimeExpFreshLayer j r,
            supportFloor j r * (p : ℝ)⁻¹ := by
          simp [trackBLinearPrimeExpFreshPrimeReciprocalMass, Finset.mul_sum]
    _ = ∑ p ∈ trackBLinearPrimeExpFreshLayer j r,
          (p : ℝ)⁻¹ * supportFloor j r := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          ring
    _ ≤ trackBLinearPrimeExpLayerWeightedSupportMass j r := by
          unfold trackBLinearPrimeExpLayerWeightedSupportMass
          refine Finset.sum_le_sum ?_
          intro p hp
          exact mul_le_mul_of_nonneg_left (hsupport p hp)
            (inv_nonneg.mpr (by exact_mod_cast Nat.zero_le p))

/-- Exact diagonal second-moment mass in the form produced directly by the
existing squarefree coefficient orthogonality lemma. -/
noncomputable def trackBLinearPrimeExpLayerSecondMomentMass (j r : ℕ) : ℝ :=
  ∑ p ∈ trackBLinearPrimeExpFreshLayer j r,
    ∑ m ∈ trackBLinearPrimeExpLayerCoeffSupport j r p,
      ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2

/-- Exact second-moment mass of a single coefficient in one exponential layer. -/
noncomputable def trackBLinearPrimeExpLayerCoeffSecondMass (j r p : ℕ) : ℝ :=
  ∑ m ∈ trackBLinearPrimeExpLayerCoeffSupport j r p,
    ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2

/-- One square-root coefficient weight has square `1 / (p*m)`. -/
theorem trackBLinearPrimeExp_sqrt_weight_sq_eq_inv_mul_inv
    {p m : ℕ} (hp : Nat.Prime p) (hm : 0 < m) :
    ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2 = (p : ℝ)⁻¹ * (m : ℝ)⁻¹ := by
  have hpm_nat_pos : 0 < p * m := Nat.mul_pos hp.pos hm
  have hpm_pos : (0 : ℝ) < ((p * m : ℕ) : ℝ) := by exact_mod_cast hpm_nat_pos
  have hsqrt_sq :
      (Real.sqrt (((p * m : ℕ) : ℝ))) ^ 2 = ((p * m : ℕ) : ℝ) := by
    simpa using Real.sq_sqrt (le_of_lt hpm_pos)
  calc
    ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2
        = (((p * m : ℕ) : ℝ))⁻¹ := by
          rw [inv_pow, hsqrt_sq]
    _ = ((p : ℝ) * (m : ℝ))⁻¹ := by
          simp
    _ = (p : ℝ)⁻¹ * (m : ℝ)⁻¹ := by
          rw [mul_inv_rev]
          ring

/-- The second moment of one coefficient is `(1 / p)` times the reciprocal
mass of its coefficient support. -/
theorem trackBLinearPrimeExpLayerCoeffSecondMass_eq_prime_inv_mul_supportReciprocalMass
    {j r p : ℕ} (hp : p ∈ trackBLinearPrimeExpFreshLayer j r) :
    trackBLinearPrimeExpLayerCoeffSecondMass j r p =
      (p : ℝ)⁻¹ * trackBLinearPrimeExpSupportReciprocalMass j r p := by
  classical
  unfold trackBLinearPrimeExpLayerCoeffSecondMass
  unfold trackBLinearPrimeExpSupportReciprocalMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hp_prime : Nat.Prime p := (mem_trackBFreshPrimeLayer.mp hp).2.2
  have hm_pos : 0 < m := trackBSquarefreeFreshCoeffSupport_pos hm
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    trackBLinearPrimeExp_sqrt_weight_sq_eq_inv_mul_inv hp_prime hm_pos

/-- The two deterministic expressions for expected exponential layer variance
agree.  This theorem is the bridge between Lean's square-root coefficient
formula and paper-side reciprocal-mass estimates. -/
theorem trackBLinearPrimeExpLayerSecondMomentMass_eq_weightedSupportMass
    (j r : ℕ) :
    trackBLinearPrimeExpLayerSecondMomentMass j r =
      trackBLinearPrimeExpLayerWeightedSupportMass j r := by
  classical
  unfold trackBLinearPrimeExpLayerSecondMomentMass
  unfold trackBLinearPrimeExpLayerWeightedSupportMass
  unfold trackBLinearPrimeExpSupportReciprocalMass
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp_prime : Nat.Prime p := (mem_trackBFreshPrimeLayer.mp hp).2.2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hm_pos : 0 < m := trackBSquarefreeFreshCoeffSupport_pos hm
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    trackBLinearPrimeExp_sqrt_weight_sq_eq_inv_mul_inv hp_prime hm_pos

/-- The expected scheduled variance at a mesh point is exactly the deterministic
weighted support mass. -/
theorem integral_trackBLinearPrimeExp_scheduledVariance_eq_weightedSupportMass
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j) :
    ∫ omega,
        trackBLinearPrimeScheduledVariance
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu =
      trackBLinearPrimeExpLayerWeightedSupportMass j r := by
  calc
    ∫ omega,
        trackBLinearPrimeScheduledVariance
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu
        = trackBLinearPrimeExpLayerSecondMomentMass j r := by
          simpa [trackBLinearPrimeExpLayerSecondMomentMass,
            trackBLinearPrimeExpFreshLayer, trackBLinearPrimeExpLayerCoeffSupport] using
            integral_trackBLinearPrimeExp_scheduledVariance_eq_layer j r hr
    _ = trackBLinearPrimeExpLayerWeightedSupportMass j r :=
        trackBLinearPrimeExpLayerSecondMomentMass_eq_weightedSupportMass j r

/-- Deterministic lower bound on the expected layer variance.  This is meant to
be supplied by reciprocal-prime and no-fresh squarefree reciprocal-mass
estimates, not by probabilistic concentration. -/
structure TrackBLinearPrimeExpLayerMeanLowerFacts where
  mean_ge_two_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r

/-- Deterministic lower floor for the expected layer variance.  Unlike
`TrackBLinearPrimeExpLayerMeanLowerFacts`, this retains the actual scalar floor
so concentration estimates can use it in their Chebyshev denominator. -/
structure TrackBLinearPrimeExpLayerMeanFloorFacts where
  meanFloor : ℕ → ℕ → ℝ
  mean_floor_ge_two_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤ meanFloor j r
  mean_floor_le_mean :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      meanFloor j r ≤ trackBLinearPrimeExpLayerWeightedSupportMass j r

/-- A retained mean floor implies the older minimal mean-lower package. -/
def trackBLinearPrimeExpLayerMeanLowerFacts_of_meanFloor
    (h : TrackBLinearPrimeExpLayerMeanFloorFacts) :
    TrackBLinearPrimeExpLayerMeanLowerFacts where
  mean_ge_two_V := by
    intro j r hr
    exact (h.mean_floor_ge_two_V j r hr).trans (h.mean_floor_le_mean j r hr)

/-- Sieve-facing deterministic inputs for the expected layer-variance lower
bound.  The support floor should come from the no-fresh squarefree reciprocal
mass estimate, and the scalar product lower bound should come from combining it
with the fresh-prime reciprocal mass estimate. -/
structure TrackBLinearPrimeExpLayerReciprocalMassFacts where
  supportFloor : ℕ → ℕ → ℝ
  support_mass_lower :
    ∀ j r p, p ∈ trackBLinearPrimeExpFreshLayer j r →
      supportFloor j r ≤ trackBLinearPrimeExpSupportReciprocalMass j r p
  scalar_mass_lower :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        supportFloor j r * trackBLinearPrimeExpFreshPrimeReciprocalMass j r

/-- More separated deterministic reciprocal-mass inputs.  This is the
paper-facing version: prove a no-fresh support floor, prove a fresh-prime
reciprocal-mass floor, then check the scalar product clears `2 * V_j`. -/
structure TrackBLinearPrimeExpLayerSeparatedReciprocalMassFacts where
  supportFloor : ℕ → ℕ → ℝ
  primeMassFloor : ℕ → ℕ → ℝ
  supportFloor_nonneg :
    ∀ j r, 0 ≤ supportFloor j r
  support_mass_lower :
    ∀ j r p, p ∈ trackBLinearPrimeExpFreshLayer j r →
      supportFloor j r ≤ trackBLinearPrimeExpSupportReciprocalMass j r p
  prime_mass_lower :
    ∀ j r, primeMassFloor j r ≤ trackBLinearPrimeExpFreshPrimeReciprocalMass j r
  scalar_floor_lower :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        supportFloor j r * primeMassFloor j r

/-- Concrete no-fresh support reciprocal-mass floor for the exponential layer.
The scale records a fixed-constant fraction of the expected `b^(29K) R^r` mass
after the no-fresh Euler-product loss. -/
noncomputable def trackBLinearPrimeExpSupportMassFloor (j r : ℕ) : ℝ :=
  (1 : ℝ) / 64 *
    ((trackBLinearPrimeConcreteBase j : ℝ) ^ (29 * trackBLinearPrimeConcreteK) *
      (trackBLinearPrimeConcretePointRatio j : ℝ) ^ r)

/-- Conservative fresh-prime reciprocal-mass floor.  The actual analytic mass
should be logarithmic in the stage base, so `1` leaves substantial slack. -/
noncomputable def trackBLinearPrimeExpPrimeMassFloor (_j _r : ℕ) : ℝ :=
  1

/-- The retained deterministic mean floor generated by the named support and
fresh-prime reciprocal-mass floors.  This is the denominator to use in the
current mean-floor concentration route. -/
noncomputable def trackBLinearPrimeExpConcreteMeanFloor (j r : ℕ) : ℝ :=
  trackBLinearPrimeExpSupportMassFloor j r *
    trackBLinearPrimeExpPrimeMassFloor j r

/-- The concrete support-mass floor is nonnegative. -/
theorem trackBLinearPrimeExpSupportMassFloor_nonneg (j r : ℕ) :
    0 ≤ trackBLinearPrimeExpSupportMassFloor j r := by
  unfold trackBLinearPrimeExpSupportMassFloor
  positivity

/-- Elementary scalar slack for the named concrete reciprocal-mass floors:
even a `1/64` fraction of `b^(29K) R^r` dominates `2 * b^(20K)`. -/
theorem trackBLinearPrimeExp_concreteFloor_scalar_lower
    (j r : ℕ)
    (_hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j) :
    2 * trackBLinearPrimeExpScheduleSpec.V j ≤
      trackBLinearPrimeExpSupportMassFloor j r *
        trackBLinearPrimeExpPrimeMassFloor j r := by
  have hnat :
      128 * trackBLinearPrimeConcreteBase j ^ (20 * trackBLinearPrimeConcreteK) ≤
        trackBLinearPrimeConcreteBase j ^ (29 * trackBLinearPrimeConcreteK) *
          trackBLinearPrimeConcretePointRatio j ^ r := by
    have hb2 : 2 ≤ trackBLinearPrimeConcreteBase j :=
      trackBLinearPrimeConcreteBase_two_le j
    have hb1 : 1 ≤ trackBLinearPrimeConcreteBase j := le_trans (by norm_num) hb2
    have h128 : 128 ≤ trackBLinearPrimeConcreteBase j ^ 7 := by
      have hpow :
          2 ^ 7 ≤ trackBLinearPrimeConcreteBase j ^ 7 :=
        pow_le_pow_left' hb2 7
      simpa using hpow
    have hgap :
        7 + 20 * trackBLinearPrimeConcreteK ≤ 29 * trackBLinearPrimeConcreteK := by
      norm_num [trackBLinearPrimeConcreteK]
    have hleft :
        128 * trackBLinearPrimeConcreteBase j ^ (20 * trackBLinearPrimeConcreteK) ≤
          trackBLinearPrimeConcreteBase j ^ 7 *
            trackBLinearPrimeConcreteBase j ^ (20 * trackBLinearPrimeConcreteK) :=
      Nat.mul_le_mul_right _ h128
    have hpow :
        trackBLinearPrimeConcreteBase j ^ 7 *
            trackBLinearPrimeConcreteBase j ^ (20 * trackBLinearPrimeConcreteK) ≤
          trackBLinearPrimeConcreteBase j ^ (29 * trackBLinearPrimeConcreteK) := by
      calc
        trackBLinearPrimeConcreteBase j ^ 7 *
            trackBLinearPrimeConcreteBase j ^ (20 * trackBLinearPrimeConcreteK)
            = trackBLinearPrimeConcreteBase j ^
                (7 + 20 * trackBLinearPrimeConcreteK) := by
              rw [← pow_add]
        _ ≤ trackBLinearPrimeConcreteBase j ^ (29 * trackBLinearPrimeConcreteK) :=
            pow_le_pow_right' hb1 hgap
    have hratio_pos : 0 < trackBLinearPrimeConcretePointRatio j ^ r :=
      pow_pos (trackBLinearPrimeConcretePointRatio_pos j) r
    exact (hleft.trans hpow).trans (Nat.le_mul_of_pos_right _ hratio_pos)
  have hreal :
      (128 : ℝ) *
          ((trackBLinearPrimeConcreteBase j : ℝ) ^ (20 * trackBLinearPrimeConcreteK)) ≤
        (trackBLinearPrimeConcreteBase j : ℝ) ^ (29 * trackBLinearPrimeConcreteK) *
          (trackBLinearPrimeConcretePointRatio j : ℝ) ^ r := by
    exact_mod_cast hnat
  change
    2 * ((trackBLinearPrimeConcreteBase j : ℝ) ^ (20 * trackBLinearPrimeConcreteK)) ≤
      ((1 : ℝ) / 64 *
        ((trackBLinearPrimeConcreteBase j : ℝ) ^ (29 * trackBLinearPrimeConcreteK) *
          (trackBLinearPrimeConcretePointRatio j : ℝ) ^ r)) * 1
  rw [mul_one]
  nlinarith

/-- First-pass small-prime product floor for the product/rough route.  This
corresponds to the analytic choice `log y = base^(2K)`, with two powers of
`base^K` of lower-tail slack below the typical small-product size. -/
noncomputable def trackBLinearPrimeExpProductRoughSmallFloor (j : ℕ) : ℝ :=
  (((trackBLinearPrimeConcreteBase j : ℝ) ^ (4 * trackBLinearPrimeConcreteK)))⁻¹

/-- First-pass rough-energy floor after removing the `base^(2K)` small-prime
reciprocal mass from the full `base^(29K) R^r` support scale. -/
noncomputable def trackBLinearPrimeExpProductRoughRoughFloor (j r : ℕ) : ℝ :=
  (1 : ℝ) / 64 *
    ((trackBLinearPrimeConcreteBase j : ℝ) ^ (27 * trackBLinearPrimeConcreteK) *
      (trackBLinearPrimeConcretePointRatio j : ℝ) ^ r)

/-- The first-pass small-prime product floor is nonnegative. -/
theorem trackBLinearPrimeExpProductRoughSmallFloor_nonneg (j : ℕ) :
    0 ≤ trackBLinearPrimeExpProductRoughSmallFloor j := by
  unfold trackBLinearPrimeExpProductRoughSmallFloor
  positivity

/-- Exact logarithm of the fixed small-prime product floor used by Packet C. -/
theorem trackBLinearPrimeExpProductRoughSmallFloor_log_eq (j : ℕ) :
    Real.log (trackBLinearPrimeExpProductRoughSmallFloor j) =
      -(4 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) := by
  unfold trackBLinearPrimeExpProductRoughSmallFloor trackBLinearPrimeConcreteK
  rw [Real.log_inv, Real.log_pow]
  ring

/-- The fixed Packet C small-prime product floor satisfies the log bound
expected by the small-product tail adapter. -/
theorem trackBLinearPrimeExpProductRoughSmallFloor_log_le (j : ℕ) :
    Real.log (trackBLinearPrimeExpProductRoughSmallFloor j) ≤
      -(4 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) := by
  rw [trackBLinearPrimeExpProductRoughSmallFloor_log_eq]

/-- The first-pass product/rough floors clear the `4V_j` scalar requirement in
the product/rough `V_j`-error wrapper. -/
theorem trackBLinearPrimeExp_productRoughFloor_ge_four_V
    (j r : ℕ)
    (_hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j) :
    4 * trackBLinearPrimeExpScheduleSpec.V j ≤
      trackBLinearPrimeExpProductRoughSmallFloor j *
        trackBLinearPrimeExpProductRoughRoughFloor j r := by
  have hnat :
      256 * trackBLinearPrimeConcreteBase j ^ (20 * trackBLinearPrimeConcreteK) ≤
        trackBLinearPrimeConcreteBase j ^ (23 * trackBLinearPrimeConcreteK) *
          trackBLinearPrimeConcretePointRatio j ^ r := by
    have hb2 : 2 ≤ trackBLinearPrimeConcreteBase j :=
      trackBLinearPrimeConcreteBase_two_le j
    have hb1 : 1 ≤ trackBLinearPrimeConcreteBase j := le_trans (by norm_num) hb2
    have h256 : 256 ≤ trackBLinearPrimeConcreteBase j ^ 8 := by
      have hpow :
          2 ^ 8 ≤ trackBLinearPrimeConcreteBase j ^ 8 :=
        pow_le_pow_left' hb2 8
      simpa using hpow
    have hgap :
        8 + 20 * trackBLinearPrimeConcreteK ≤ 23 * trackBLinearPrimeConcreteK := by
      norm_num [trackBLinearPrimeConcreteK]
    have hleft :
        256 * trackBLinearPrimeConcreteBase j ^ (20 * trackBLinearPrimeConcreteK) ≤
          trackBLinearPrimeConcreteBase j ^ 8 *
            trackBLinearPrimeConcreteBase j ^ (20 * trackBLinearPrimeConcreteK) :=
      Nat.mul_le_mul_right _ h256
    have hpow :
        trackBLinearPrimeConcreteBase j ^ 8 *
            trackBLinearPrimeConcreteBase j ^ (20 * trackBLinearPrimeConcreteK) ≤
          trackBLinearPrimeConcreteBase j ^ (23 * trackBLinearPrimeConcreteK) := by
      calc
        trackBLinearPrimeConcreteBase j ^ 8 *
            trackBLinearPrimeConcreteBase j ^ (20 * trackBLinearPrimeConcreteK)
            = trackBLinearPrimeConcreteBase j ^
                (8 + 20 * trackBLinearPrimeConcreteK) := by
              rw [← pow_add]
        _ ≤ trackBLinearPrimeConcreteBase j ^ (23 * trackBLinearPrimeConcreteK) :=
            pow_le_pow_right' hb1 hgap
    have hratio_pos : 0 < trackBLinearPrimeConcretePointRatio j ^ r :=
      pow_pos (trackBLinearPrimeConcretePointRatio_pos j) r
    exact (hleft.trans hpow).trans (Nat.le_mul_of_pos_right _ hratio_pos)
  have hreal :
      (256 : ℝ) *
          ((trackBLinearPrimeConcreteBase j : ℝ) ^ (20 * trackBLinearPrimeConcreteK)) ≤
        (trackBLinearPrimeConcreteBase j : ℝ) ^ (23 * trackBLinearPrimeConcreteK) *
          (trackBLinearPrimeConcretePointRatio j : ℝ) ^ r := by
    exact_mod_cast hnat
  have hbpos :
      0 < (trackBLinearPrimeConcreteBase j : ℝ) ^ (4 * trackBLinearPrimeConcreteK) := by
    have hbase : (0 : ℝ) < trackBLinearPrimeConcreteBase j := by
      exact_mod_cast trackBLinearPrimeConcreteBase_pos j
    exact pow_pos hbase (4 * trackBLinearPrimeConcreteK)
  have hbase_ne :
      (trackBLinearPrimeConcreteBase j : ℝ) ^ (4 * trackBLinearPrimeConcreteK) ≠ 0 :=
    ne_of_gt hbpos
  have hpow_split :
      (trackBLinearPrimeConcreteBase j : ℝ) ^ (27 * trackBLinearPrimeConcreteK) =
        (trackBLinearPrimeConcreteBase j : ℝ) ^ (4 * trackBLinearPrimeConcreteK) *
          (trackBLinearPrimeConcreteBase j : ℝ) ^ (23 * trackBLinearPrimeConcreteK) := by
    rw [show 27 * trackBLinearPrimeConcreteK =
        4 * trackBLinearPrimeConcreteK + 23 * trackBLinearPrimeConcreteK by
      norm_num [trackBLinearPrimeConcreteK], pow_add]
  have hmain :
      4 * ((trackBLinearPrimeConcreteBase j : ℝ) ^ (20 * trackBLinearPrimeConcreteK)) ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^
              (4 * trackBLinearPrimeConcreteK)))⁻¹ *
          ((1 : ℝ) / 64 *
            ((trackBLinearPrimeConcreteBase j : ℝ) ^ (27 * trackBLinearPrimeConcreteK) *
              (trackBLinearPrimeConcretePointRatio j : ℝ) ^ r)) := by
    rw [hpow_split]
    field_simp [hbase_ne]
    nlinarith [hreal]
  change
    4 * ((trackBLinearPrimeConcreteBase j : ℝ) ^ (20 * trackBLinearPrimeConcreteK)) ≤
      (((trackBLinearPrimeConcreteBase j : ℝ) ^
            (4 * trackBLinearPrimeConcreteK)))⁻¹ *
        ((1 : ℝ) / 64 *
          ((trackBLinearPrimeConcreteBase j : ℝ) ^ (27 * trackBLinearPrimeConcreteK) *
            (trackBLinearPrimeConcretePointRatio j : ℝ) ^ r))
  exact hmain

/-- Concrete-floor analytic facts.  The remaining mathematical work is now
only the no-fresh support reciprocal-mass lower bound and the fresh-prime
reciprocal-mass lower bound for the named floors above. -/
structure TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts where
  support_mass_lower :
    ∀ j r p, p ∈ trackBLinearPrimeExpFreshLayer j r →
      trackBLinearPrimeExpSupportMassFloor j r ≤
        trackBLinearPrimeExpSupportReciprocalMass j r p
  prime_mass_lower :
    ∀ j r,
      trackBLinearPrimeExpPrimeMassFloor j r ≤
        trackBLinearPrimeExpFreshPrimeReciprocalMass j r

/-- Subset version of the concrete-floor mass facts.  An analytic proof may
choose convenient finite subsets of the coefficient support and fresh-prime
layer, prove the reciprocal-mass lower bounds there, and let Lean lift them to
the exact support by monotonicity. -/
structure TrackBLinearPrimeExpConcreteFloorSubsetMassFacts where
  supportSubset : ℕ → ℕ → ℕ → Finset ℕ
  primeSubset : ℕ → ℕ → Finset ℕ
  supportSubset_subset :
    ∀ j r p, p ∈ trackBLinearPrimeExpFreshLayer j r →
      supportSubset j r p ⊆ trackBLinearPrimeExpLayerCoeffSupport j r p
  primeSubset_subset :
    ∀ j r, primeSubset j r ⊆ trackBLinearPrimeExpFreshLayer j r
  supportSubset_mass_lower :
    ∀ j r p, p ∈ trackBLinearPrimeExpFreshLayer j r →
      trackBLinearPrimeExpSupportMassFloor j r ≤
        trackBLinearPrimeExpReciprocalMassOn (supportSubset j r p)
  primeSubset_mass_lower :
    ∀ j r,
      trackBLinearPrimeExpPrimeMassFloor j r ≤
        trackBLinearPrimeExpReciprocalMassOn (primeSubset j r)

/-- Concrete mass facts using the canonical boundary-safe support bulk and an
analyst-chosen fresh-prime subset. -/
structure TrackBLinearPrimeExpSupportBulkMassFacts where
  primeSubset : ℕ → ℕ → Finset ℕ
  primeSubset_subset :
    ∀ j r, primeSubset j r ⊆ trackBLinearPrimeExpFreshLayer j r
  supportBulk_mass_lower :
    ∀ j r p, p ∈ trackBLinearPrimeExpFreshLayer j r →
      trackBLinearPrimeExpSupportMassFloor j r ≤
        trackBLinearPrimeExpReciprocalMassOn (trackBLinearPrimeExpSupportBulk j r p)
  primeSubset_mass_lower :
    ∀ j r,
      trackBLinearPrimeExpPrimeMassFloor j r ≤
        trackBLinearPrimeExpReciprocalMassOn (primeSubset j r)

/-- Support-side half of the boundary-safe bulk mass facts.  This can be
proved independently of the fresh-prime reciprocal-mass lower bound. -/
structure TrackBLinearPrimeExpSupportBulkSupportMassFacts where
  supportBulk_mass_lower :
    ∀ j r p, p ∈ trackBLinearPrimeExpFreshLayer j r →
      trackBLinearPrimeExpSupportMassFloor j r ≤
        trackBLinearPrimeExpReciprocalMassOn (trackBLinearPrimeExpSupportBulk j r p)

/-- Cleaner p-independent support-bulk lower-bound target.  A finite sieve
estimate can work on `trackBLinearPrimeExpSupportBulkSieveCore`; Lean then
lifts it to every p-coordinate support bulk by monotonicity. -/
structure TrackBLinearPrimeExpSupportBulkSieveCoreMassFacts where
  supportBulkSieveCore_mass_lower :
    ∀ j r,
      trackBLinearPrimeExpSupportMassFloor j r ≤
        trackBLinearPrimeExpReciprocalMassOn (trackBLinearPrimeExpSupportBulkSieveCore j r)

/-- A p-independent sifted-core lower bound supplies the support-side
boundary-safe bulk mass facts. -/
def trackBLinearPrimeExpSupportBulkSupportMassFacts_of_sieveCore
    (h : TrackBLinearPrimeExpSupportBulkSieveCoreMassFacts) :
    TrackBLinearPrimeExpSupportBulkSupportMassFacts where
  supportBulk_mass_lower := by
    intro j r p hp
    exact (h.supportBulkSieveCore_mass_lower j r).trans
      (trackBLinearPrimeExpReciprocalMassOn_mono
        (trackBLinearPrimeExpSupportBulkSieveCore_subset_supportBulk hp))

/-- Fresh-prime reciprocal-mass half of the boundary-safe bulk mass facts,
allowing the analytic proof to choose any convenient finite prime subset. -/
structure TrackBLinearPrimeExpFreshPrimeMassFacts where
  primeSubset : ℕ → ℕ → Finset ℕ
  primeSubset_subset :
    ∀ j r, primeSubset j r ⊆ trackBLinearPrimeExpFreshLayer j r
  primeSubset_mass_lower :
    ∀ j r,
      trackBLinearPrimeExpPrimeMassFloor j r ≤
        trackBLinearPrimeExpReciprocalMassOn (primeSubset j r)

/-- Full-layer version of the fresh-prime reciprocal-mass fact.  This is the
paper-facing target when the estimate is proved directly for the entire fresh
prime layer. -/
structure TrackBLinearPrimeExpFreshLayerPrimeMassFacts where
  freshPrime_mass_lower :
    ∀ j r,
      trackBLinearPrimeExpPrimeMassFloor j r ≤
        trackBLinearPrimeExpFreshPrimeReciprocalMass j r

/-- Interval-prime version of the fresh-layer reciprocal-mass target.  This is
the shape produced by a standard Mertens/PNT estimate over the explicit
integer interval. -/
structure TrackBLinearPrimeExpFreshLayerIntervalMassFacts where
  freshPrime_interval_mass_lower :
    ∀ j r,
      trackBLinearPrimeExpPrimeMassFloor j r ≤
        ∑ p ∈
          (Finset.Icc (trackBLinearPrimeExpFreshLo j r)
            (trackBLinearPrimeExpFreshHi j r)).filter Nat.Prime,
          (p : ℝ)⁻¹

/-- A standard interval-prime reciprocal-mass lower bound supplies the exact
fresh-layer mass facts used by the product/rough route. -/
def trackBLinearPrimeExpFreshLayerPrimeMassFacts_of_intervalMass
    (h : TrackBLinearPrimeExpFreshLayerIntervalMassFacts) :
    TrackBLinearPrimeExpFreshLayerPrimeMassFacts where
  freshPrime_mass_lower := by
    intro j r
    simpa [trackBLinearPrimeExpFreshPrimeReciprocalMass,
      trackBLinearPrimeExpFreshLayer, trackBFreshPrimeLayer, trackBLinearPrimeExpScheduleSpec]
      using h.freshPrime_interval_mass_lower j r

/-- A full fresh-prime-layer lower bound is a fresh-prime subset lower bound. -/
def trackBLinearPrimeExpFreshPrimeMassFacts_of_freshLayer
    (h : TrackBLinearPrimeExpFreshLayerPrimeMassFacts) :
    TrackBLinearPrimeExpFreshPrimeMassFacts where
  primeSubset := trackBLinearPrimeExpFreshLayer
  primeSubset_subset := by
    intro j r
    exact fun _p hp => hp
  primeSubset_mass_lower := by
    intro j r
    simpa [trackBLinearPrimeExpFreshPrimeReciprocalMass,
      trackBLinearPrimeExpReciprocalMassOn] using h.freshPrime_mass_lower j r

/-- Combine the independently proved support-bulk and fresh-prime mass facts
into the existing boundary-safe support-bulk package. -/
def trackBLinearPrimeExpSupportBulkMassFacts_of_support_and_prime
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hprime : TrackBLinearPrimeExpFreshPrimeMassFacts) :
    TrackBLinearPrimeExpSupportBulkMassFacts where
  primeSubset := hprime.primeSubset
  primeSubset_subset := hprime.primeSubset_subset
  supportBulk_mass_lower := hsupport.supportBulk_mass_lower
  primeSubset_mass_lower := hprime.primeSubset_mass_lower

/-- Combine support-bulk mass with a direct full-layer fresh-prime reciprocal
mass estimate. -/
def trackBLinearPrimeExpSupportBulkMassFacts_of_support_and_freshLayer
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hprime : TrackBLinearPrimeExpFreshLayerPrimeMassFacts) :
    TrackBLinearPrimeExpSupportBulkMassFacts :=
  trackBLinearPrimeExpSupportBulkMassFacts_of_support_and_prime hsupport
    (trackBLinearPrimeExpFreshPrimeMassFacts_of_freshLayer hprime)

/-- Boundary-safe support-bulk mass facts imply the generic subset-mass facts. -/
def trackBLinearPrimeExpConcreteFloorSubsetMassFacts_of_supportBulk
    (h : TrackBLinearPrimeExpSupportBulkMassFacts) :
    TrackBLinearPrimeExpConcreteFloorSubsetMassFacts where
  supportSubset := trackBLinearPrimeExpSupportBulk
  primeSubset := h.primeSubset
  supportSubset_subset := by
    intro j r p hp
    exact trackBLinearPrimeExpSupportBulk_subset_layerCoeffSupport hp
  primeSubset_subset := h.primeSubset_subset
  supportSubset_mass_lower := h.supportBulk_mass_lower
  primeSubset_mass_lower := h.primeSubset_mass_lower

/-- Subset reciprocal-mass lower bounds imply the exact concrete-floor mass
facts. -/
def trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_subsetMass
    (h : TrackBLinearPrimeExpConcreteFloorSubsetMassFacts) :
    TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts where
  support_mass_lower := by
    intro j r p hp
    exact le_trans (h.supportSubset_mass_lower j r p hp)
      (by
        simpa [trackBLinearPrimeExpReciprocalMassOn,
          trackBLinearPrimeExpSupportReciprocalMass] using
          trackBLinearPrimeExpReciprocalMassOn_mono (h.supportSubset_subset j r p hp))
  prime_mass_lower := by
    intro j r
    exact le_trans (h.primeSubset_mass_lower j r)
      (by
        simpa [trackBLinearPrimeExpReciprocalMassOn,
          trackBLinearPrimeExpFreshPrimeReciprocalMass] using
          trackBLinearPrimeExpReciprocalMassOn_mono (h.primeSubset_subset j r))

/-- Boundary-safe support-bulk mass facts imply the exact concrete-floor mass
facts. -/
def trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_supportBulk
    (h : TrackBLinearPrimeExpSupportBulkMassFacts) :
    TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts :=
  trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_subsetMass
    (trackBLinearPrimeExpConcreteFloorSubsetMassFacts_of_supportBulk h)

/-- The concrete-floor package is a special case of the separated
reciprocal-mass interface. -/
def trackBLinearPrimeExpLayerSeparatedReciprocalMassFacts_of_concreteFloors
    (h : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts) :
    TrackBLinearPrimeExpLayerSeparatedReciprocalMassFacts where
  supportFloor := trackBLinearPrimeExpSupportMassFloor
  primeMassFloor := trackBLinearPrimeExpPrimeMassFloor
  supportFloor_nonneg := trackBLinearPrimeExpSupportMassFloor_nonneg
  support_mass_lower := h.support_mass_lower
  prime_mass_lower := h.prime_mass_lower
  scalar_floor_lower := trackBLinearPrimeExp_concreteFloor_scalar_lower

/-- Subset-mass facts also specialize the separated reciprocal-mass interface. -/
def trackBLinearPrimeExpLayerSeparatedReciprocalMassFacts_of_subsetMass
    (h : TrackBLinearPrimeExpConcreteFloorSubsetMassFacts) :
    TrackBLinearPrimeExpLayerSeparatedReciprocalMassFacts :=
  trackBLinearPrimeExpLayerSeparatedReciprocalMassFacts_of_concreteFloors
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_subsetMass h)

/-- Boundary-safe support-bulk mass facts also specialize the separated
reciprocal-mass interface. -/
def trackBLinearPrimeExpLayerSeparatedReciprocalMassFacts_of_supportBulk
    (h : TrackBLinearPrimeExpSupportBulkMassFacts) :
    TrackBLinearPrimeExpLayerSeparatedReciprocalMassFacts :=
  trackBLinearPrimeExpLayerSeparatedReciprocalMassFacts_of_subsetMass
    (trackBLinearPrimeExpConcreteFloorSubsetMassFacts_of_supportBulk h)

/-- Separated support and fresh-prime reciprocal-mass estimates imply the
combined reciprocal-mass facts. -/
def trackBLinearPrimeExpLayerReciprocalMassFacts_of_separated
    (h : TrackBLinearPrimeExpLayerSeparatedReciprocalMassFacts) :
    TrackBLinearPrimeExpLayerReciprocalMassFacts where
  supportFloor := h.supportFloor
  support_mass_lower := h.support_mass_lower
  scalar_mass_lower := by
    intro j r hr
    exact le_trans (h.scalar_floor_lower j r hr)
      (mul_le_mul_of_nonneg_left (h.prime_mass_lower j r) (h.supportFloor_nonneg j r))

/-- Reciprocal-prime mass plus no-fresh support-mass lower bounds imply the
expected layer-variance lower bound. -/
def trackBLinearPrimeExpLayerMeanLowerFacts_of_reciprocalMass
    (h : TrackBLinearPrimeExpLayerReciprocalMassFacts) :
    TrackBLinearPrimeExpLayerMeanLowerFacts where
  mean_ge_two_V := by
    intro j r hr
    exact le_trans (h.scalar_mass_lower j r hr)
      (trackBLinearPrimeExp_supportFloor_mul_primeMass_le_weightedSupportMass
        h.supportFloor j r (h.support_mass_lower j r))

/-- Fully separated reciprocal-mass estimates imply the expected layer-variance
lower bound. -/
def trackBLinearPrimeExpLayerMeanLowerFacts_of_separatedReciprocalMass
    (h : TrackBLinearPrimeExpLayerSeparatedReciprocalMassFacts) :
    TrackBLinearPrimeExpLayerMeanLowerFacts :=
  trackBLinearPrimeExpLayerMeanLowerFacts_of_reciprocalMass
    (trackBLinearPrimeExpLayerReciprocalMassFacts_of_separated h)

/-- Separated support and fresh-prime reciprocal-mass estimates retain the
explicit product floor for later concentration estimates. -/
def trackBLinearPrimeExpLayerMeanFloorFacts_of_separatedReciprocalMass
    (h : TrackBLinearPrimeExpLayerSeparatedReciprocalMassFacts) :
    TrackBLinearPrimeExpLayerMeanFloorFacts where
  meanFloor := fun j r => h.supportFloor j r * h.primeMassFloor j r
  mean_floor_ge_two_V := h.scalar_floor_lower
  mean_floor_le_mean := by
    intro j r _hr
    exact le_trans
      (mul_le_mul_of_nonneg_left (h.prime_mass_lower j r) (h.supportFloor_nonneg j r))
      (trackBLinearPrimeExp_supportFloor_mul_primeMass_le_weightedSupportMass
        h.supportFloor j r (h.support_mass_lower j r))

/-- The named concrete reciprocal-mass floors imply the expected
layer-variance lower bound once their two analytic mass estimates are proved. -/
def trackBLinearPrimeExpLayerMeanLowerFacts_of_concreteFloors
    (h : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts) :
    TrackBLinearPrimeExpLayerMeanLowerFacts :=
  trackBLinearPrimeExpLayerMeanLowerFacts_of_separatedReciprocalMass
    (trackBLinearPrimeExpLayerSeparatedReciprocalMassFacts_of_concreteFloors h)

/-- Subset-mass facts imply the expected layer-variance lower bound. -/
def trackBLinearPrimeExpLayerMeanLowerFacts_of_subsetMass
    (h : TrackBLinearPrimeExpConcreteFloorSubsetMassFacts) :
    TrackBLinearPrimeExpLayerMeanLowerFacts :=
  trackBLinearPrimeExpLayerMeanLowerFacts_of_concreteFloors
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_subsetMass h)

/-- Boundary-safe support-bulk mass facts imply the expected layer-variance
lower bound. -/
def trackBLinearPrimeExpLayerMeanLowerFacts_of_supportBulk
    (h : TrackBLinearPrimeExpSupportBulkMassFacts) :
    TrackBLinearPrimeExpLayerMeanLowerFacts :=
  trackBLinearPrimeExpLayerMeanLowerFacts_of_subsetMass
    (trackBLinearPrimeExpConcreteFloorSubsetMassFacts_of_supportBulk h)

/-- The named concrete reciprocal-mass floors retain their explicit product
floor for later concentration estimates. -/
def trackBLinearPrimeExpLayerMeanFloorFacts_of_concreteFloors
    (h : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts) :
    TrackBLinearPrimeExpLayerMeanFloorFacts :=
  trackBLinearPrimeExpLayerMeanFloorFacts_of_separatedReciprocalMass
    (trackBLinearPrimeExpLayerSeparatedReciprocalMassFacts_of_concreteFloors h)

/-- Subset-mass facts retain the concrete product floor for concentration
estimates. -/
def trackBLinearPrimeExpLayerMeanFloorFacts_of_subsetMass
    (h : TrackBLinearPrimeExpConcreteFloorSubsetMassFacts) :
    TrackBLinearPrimeExpLayerMeanFloorFacts :=
  trackBLinearPrimeExpLayerMeanFloorFacts_of_concreteFloors
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_subsetMass h)

/-- Boundary-safe support-bulk mass facts retain the concrete product floor for
concentration estimates. -/
def trackBLinearPrimeExpLayerMeanFloorFacts_of_supportBulk
    (h : TrackBLinearPrimeExpSupportBulkMassFacts) :
    TrackBLinearPrimeExpLayerMeanFloorFacts :=
  trackBLinearPrimeExpLayerMeanFloorFacts_of_subsetMass
    (trackBLinearPrimeExpConcreteFloorSubsetMassFacts_of_supportBulk h)

/-- Named-floor version of the concrete reciprocal-mass mean-floor package.
Using this avoids dependent-type friction when analytic variance estimates are
stated directly against `trackBLinearPrimeExpConcreteMeanFloor`. -/
def trackBLinearPrimeExpConcreteMeanFloorFacts_of_concreteFloors
    (h : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts) :
    TrackBLinearPrimeExpLayerMeanFloorFacts where
  meanFloor := trackBLinearPrimeExpConcreteMeanFloor
  mean_floor_ge_two_V := by
    intro j r hr
    simpa [trackBLinearPrimeExpConcreteMeanFloor] using
      trackBLinearPrimeExp_concreteFloor_scalar_lower j r hr
  mean_floor_le_mean := by
    intro j r hr
    simpa [trackBLinearPrimeExpConcreteMeanFloor] using
      (trackBLinearPrimeExpLayerMeanFloorFacts_of_concreteFloors h).mean_floor_le_mean
        j r hr

/-- Named-floor version of the subset-mass mean-floor package. -/
def trackBLinearPrimeExpConcreteMeanFloorFacts_of_subsetMass
    (h : TrackBLinearPrimeExpConcreteFloorSubsetMassFacts) :
    TrackBLinearPrimeExpLayerMeanFloorFacts :=
  trackBLinearPrimeExpConcreteMeanFloorFacts_of_concreteFloors
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_subsetMass h)

/-- Named-floor version of the boundary-safe support-bulk mean-floor package. -/
def trackBLinearPrimeExpConcreteMeanFloorFacts_of_supportBulk
    (h : TrackBLinearPrimeExpSupportBulkMassFacts) :
    TrackBLinearPrimeExpLayerMeanFloorFacts :=
  trackBLinearPrimeExpConcreteMeanFloorFacts_of_subsetMass
    (trackBLinearPrimeExpConcreteFloorSubsetMassFacts_of_supportBulk h)

/-- Consequence of the deterministic mass facts in the integral language. -/
theorem integral_trackBLinearPrimeExp_scheduledVariance_ge_two_V_of_meanLower
    (h : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j) :
    2 * trackBLinearPrimeExpScheduleSpec.V j ≤
      ∫ omega,
        trackBLinearPrimeScheduledVariance
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu := by
  simpa [integral_trackBLinearPrimeExp_scheduledVariance_eq_weightedSupportMass j r hr]
    using h.mean_ge_two_V j r hr

/-- Stage facts for the exponential-endpoint schedule skeleton. -/
def trackBLinearPrimeExpScheduleStageFacts :
    TrackBLinearPrimeScheduleStageFacts trackBLinearPrimeExpScheduleSpec where
  r_pos := by
    simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteScheduleSpec]
      using trackBLinearPrimeConcrete_r_pos
  countMean_pos := by
    simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteScheduleSpec]
      using trackBLinearPrimeConcrete_countMean_pos
  r_le_half_countMean := by
    simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteScheduleSpec]
      using trackBLinearPrimeConcrete_r_le_half_countMean
  point_strict := trackBLinearPrimeExpPoint_strict
  point_in_block := trackBLinearPrimeExpPoint_in_block
  lo_tendsto_atTop := trackBLinearPrimeExpLo_tendsto_atTop
  M_tendsto_atTop := by
    simpa [trackBLinearPrimeExpScheduleSpec] using trackBLinearPrimeConcreteM_tendsto_atTop
  fail_summable := by
    simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteScheduleSpec]
      using trackBLinearPrimeConcrete_fail_summable

/-- Stage facts for the exponential-endpoint schedule with a configurable
analytic good event. -/
def trackBLinearPrimeExpScheduleStageFactsWithGood
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞)
    (hfail :
      (∑' j, (trackBLinearPrimeExpScheduleSpecWithGood good failGood).failGood j)
        ≠ ⊤) :
    TrackBLinearPrimeScheduleStageFacts
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood) where
  r_pos := by
    simpa [trackBLinearPrimeExpScheduleSpecWithGood, trackBLinearPrimeConcreteScheduleSpec]
      using trackBLinearPrimeConcrete_r_pos
  countMean_pos := by
    simpa [trackBLinearPrimeExpScheduleSpecWithGood, trackBLinearPrimeConcreteScheduleSpec]
      using trackBLinearPrimeConcrete_countMean_pos
  r_le_half_countMean := by
    simpa [trackBLinearPrimeExpScheduleSpecWithGood, trackBLinearPrimeConcreteScheduleSpec]
      using trackBLinearPrimeConcrete_r_le_half_countMean
  point_strict := by
    intro j r s hr hs hrs
    exact
      trackBLinearPrimeExpPoint_strict j
        (by simpa [trackBLinearPrimeExpScheduleSpecWithGood] using hr)
        (by simpa [trackBLinearPrimeExpScheduleSpecWithGood] using hs) hrs
  point_in_block := by
    intro j r hr
    simpa [trackBLinearPrimeExpScheduleSpecWithGood] using
      trackBLinearPrimeExpPoint_in_block j r
        (by simpa [trackBLinearPrimeExpScheduleSpecWithGood] using hr)
  lo_tendsto_atTop := by
    simpa [trackBLinearPrimeExpScheduleSpecWithGood] using
      trackBLinearPrimeExpLo_tendsto_atTop
  M_tendsto_atTop := by
    simpa [trackBLinearPrimeExpScheduleSpecWithGood] using
      trackBLinearPrimeConcreteM_tendsto_atTop
  fail_summable := by
    have hfail_concrete :
        (∑' j, (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).failGood j)
          ≠ ⊤ := by
      simpa [trackBLinearPrimeExpScheduleSpecWithGood,
        trackBLinearPrimeConcreteScheduleSpecWithGood] using hfail
    simpa [trackBLinearPrimeExpScheduleSpecWithGood,
      trackBLinearPrimeConcreteScheduleSpecWithGood, trackBLinearPrimeConcreteScheduleSpec]
      using trackBLinearPrimeConcrete_fail_summable_withGood good failGood hfail_concrete

/-- All-space good-event facts for the exponential-endpoint schedule skeleton. -/
def trackBLinearPrimeExpScheduleGoodEventFacts :
    TrackBLinearPrimeScheduleGoodEventFacts trackBLinearPrimeExpScheduleSpec :=
  trackBLinearPrimeScheduleGoodEventFacts_univ
    trackBLinearPrimeExpScheduleSpec
    trackBLinearPrimeExpScheduleSpec_good
    trackBLinearPrimeExpScheduleSpec_failGood

/-- Good-event facts for the exponential-endpoint schedule with a configurable
analytic good event and failure budget. -/
noncomputable def trackBLinearPrimeExpScheduleGoodEventFactsWithGood
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞)
    (good_measurable : ∀ j, MeasurableSet (good j))
    (prob_good_compl : ∀ j, mu (good j)ᶜ ≤ failGood j) :
    TrackBLinearPrimeScheduleGoodEventFacts
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood) :=
  trackBLinearPrimeScheduleGoodEventFacts_of_measurable_prob
    (trackBLinearPrimeExpScheduleSpecWithGood good failGood)
    good_measurable prob_good_compl

/-- The remaining coefficient-geometry inputs for the exponential-endpoint
schedule.  Interval separation and budget nonnegativity are deterministic and
are added by `trackBLinearPrimeExpScheduleDirectGeometryFacts_of_analytic`. -/
structure TrackBLinearPrimeExpScheduleDirectGeometryAnalyticFacts where
  variance_floor :
    ∀ omega j N,
      omega ∈ trackBLinearPrimeExpScheduleSpec.good j →
      N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeScheduledVariance
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi omega j N
  coeff_flat :
    ∀ omega j N p,
      omega ∈ trackBLinearPrimeExpScheduleSpec.good j →
      N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      p ∈ trackBLinearPrimeScheduledFreshSet
        trackBLinearPrimeExpScheduleSpec.Q
        trackBLinearPrimeExpScheduleSpec.point
        trackBLinearPrimeExpScheduleSpec.freshLo
        trackBLinearPrimeExpScheduleSpec.freshHi j N →
      |trackBLinearPrimeScheduledFreshCoeff
        trackBLinearPrimeExpScheduleSpec.Q
        trackBLinearPrimeExpScheduleSpec.point
        trackBLinearPrimeExpScheduleSpec.freshLo
        trackBLinearPrimeExpScheduleSpec.freshHi omega j N p| ≤
        trackBLinearPrimeExpScheduleSpec.flat j

/-- Layer-indexed version of the exponential variance-floor input. -/
structure TrackBLinearPrimeExpScheduleLayerVarianceDirectGeometryAnalyticFacts where
  variance_layer_floor :
    ∀ omega j r,
      r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
        trackBLinearPrimeExpScheduleSpec.V j ≤
          ∑ p ∈
            trackBFreshPrimeLayer
              (trackBLinearPrimeExpScheduleSpec.freshLo j r)
              (trackBLinearPrimeExpScheduleSpec.freshHi j r),
            (trackBLinearPrimeScheduledFreshCoeff
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) p) ^ 2
  coeff_flat :
    ∀ omega j N p,
      omega ∈ trackBLinearPrimeExpScheduleSpec.good j →
      N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      p ∈ trackBLinearPrimeScheduledFreshSet
        trackBLinearPrimeExpScheduleSpec.Q
        trackBLinearPrimeExpScheduleSpec.point
        trackBLinearPrimeExpScheduleSpec.freshLo
        trackBLinearPrimeExpScheduleSpec.freshHi j N →
      |trackBLinearPrimeScheduledFreshCoeff
        trackBLinearPrimeExpScheduleSpec.Q
        trackBLinearPrimeExpScheduleSpec.point
        trackBLinearPrimeExpScheduleSpec.freshLo
        trackBLinearPrimeExpScheduleSpec.freshHi omega j N p| ≤
        trackBLinearPrimeExpScheduleSpec.flat j

/-- Convert a layer-indexed exponential variance floor into the all-space
direct geometry analytic field. -/
def trackBLinearPrimeExpScheduleDirectGeometryAnalyticFacts_of_layerVariance
    (h : TrackBLinearPrimeExpScheduleLayerVarianceDirectGeometryAnalyticFacts) :
    TrackBLinearPrimeExpScheduleDirectGeometryAnalyticFacts where
  variance_floor := by
    intro omega j N _hgood hN
    rcases mem_trackBLinearPrimeMeshTestSet.mp hN with ⟨r, hr, hpoint⟩
    subst N
    rw [trackBLinearPrimeExp_scheduledVariance_eq_layer omega j r hr]
    exact h.variance_layer_floor omega j r hr
  coeff_flat := h.coeff_flat

/-- Assemble exponential-endpoint direct geometry facts from the two analytic
fields that remain after deterministic interval and budget plumbing. -/
def trackBLinearPrimeExpScheduleDirectGeometryFacts_of_analytic
    (h : TrackBLinearPrimeExpScheduleDirectGeometryAnalyticFacts) :
    TrackBLinearPrimeScheduleDirectGeometryFacts trackBLinearPrimeExpScheduleSpec where
  variance_floor := h.variance_floor
  coeff_flat := h.coeff_flat
  fresh_interval_disjoint := trackBLinearPrimeExp_fresh_interval_disjoint
  budget_nonneg := trackBLinearPrimeExp_rho_mul_V_nonneg

/-- Predicate form of the exponential variance-floor good event. -/
def trackBLinearPrimeExpVarianceGoodPred (omega : Omega) (j : ℕ) : Prop :=
  ∀ N, N ∈ trackBLinearPrimeExpMeshTestSet j →
    trackBLinearPrimeExpScheduleSpec.V j ≤
      trackBLinearPrimeExpScheduledVariance omega j N

/-- One test-point component of the exponential variance-floor good event. -/
noncomputable def trackBLinearPrimeExpVarianceGoodPoint (j N : ℕ) : Set Omega :=
  {omega : Omega |
    N ∈ trackBLinearPrimeExpMeshTestSet j →
      trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpScheduledVariance omega j N}

/-- Exponential variance-floor good event: every scheduled test point at stage
`j` has coefficient square-sum at least the target `V_j`. -/
noncomputable def trackBLinearPrimeExpVarianceGood (j : ℕ) : Set Omega :=
  ⋂ N : ℕ, trackBLinearPrimeExpVarianceGoodPoint j N

/-- Predicate form of the exponential coefficient-flatness good event. -/
def trackBLinearPrimeExpFlatGoodPred (omega : Omega) (j : ℕ) : Prop :=
  ∀ N, N ∈ trackBLinearPrimeExpMeshTestSet j →
    ∀ p, p ∈ trackBLinearPrimeExpScheduledFreshSet j N →
      trackBLinearPrimeExpScheduledCoeffFlat omega j N p

/-- One coefficient component of the exponential coefficient-flatness good event. -/
noncomputable def trackBLinearPrimeExpFlatGoodPoint (j N p : ℕ) : Set Omega :=
  {omega : Omega |
    N ∈ trackBLinearPrimeExpMeshTestSet j →
      p ∈ trackBLinearPrimeExpScheduledFreshSet j N →
        trackBLinearPrimeExpScheduledCoeffFlat omega j N p}

/-- Exponential coefficient-flatness good event: every scheduled coefficient at
stage `j` is at most the target flatness scale. -/
noncomputable def trackBLinearPrimeExpFlatGood (j : ℕ) : Set Omega :=
  ⋂ N : ℕ, ⋂ p : ℕ, trackBLinearPrimeExpFlatGoodPoint j N p

/-- Named complement of the exponential flat-good event.  It is kept
irreducible so later probability bounds do not repeatedly unfold the full
coefficient-flatness event in public theorem statements. -/
@[irreducible] noncomputable def trackBLinearPrimeExpFlatGoodCompl (j : ℕ) : Set Omega :=
  (trackBLinearPrimeExpFlatGood j)ᶜ

/-- Exponential geometry good event, strong enough to supply the full direct
coefficient-geometry facts. -/
noncomputable def trackBLinearPrimeExpGeometryGood (j : ℕ) : Set Omega :=
  trackBLinearPrimeExpVarianceGood j ∩ trackBLinearPrimeExpFlatGood j

/-- One-point lower-tail failure for the exponential scheduled variance. -/
noncomputable def trackBLinearPrimeExpVarianceBadSet (j N : ℕ) : Set Omega :=
  {omega : Omega |
    trackBLinearPrimeExpScheduledVariance omega j N < trackBLinearPrimeExpScheduleSpec.V j}

/-- Layer-indexed version of the exponential scheduled variance lower-tail
failure.  This is the form the analytic estimate should usually target. -/
noncomputable def trackBLinearPrimeExpVarianceLayerBadSet (j r : ℕ) : Set Omega :=
  {omega : Omega |
    (∑ p ∈
        trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
        (trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p) ^ 2) <
      trackBLinearPrimeExpScheduleSpec.V j}

/-- One-coefficient failure for the exponential flatness target. -/
noncomputable def trackBLinearPrimeExpFlatBadSet (j N p : ℕ) : Set Omega :=
  {omega : Omega |
    trackBLinearPrimeExpScheduleSpec.flat j <
      |trackBLinearPrimeExpScheduledFreshCoeff omega j N p|}

/-- Layer-indexed one-coefficient failure for the exponential flatness target. -/
noncomputable def trackBLinearPrimeExpFlatLayerBadSet (j r p : ℕ) : Set Omega :=
  trackBLinearPrimeExpFlatBadSet j (trackBLinearPrimeExpScheduleSpec.point j r) p

/-- Finite union of variance lower-tail failures over the exponential mesh. -/
noncomputable def trackBLinearPrimeExpVarianceBadUnion (j : ℕ) : Set Omega :=
  ⋃ N ∈ trackBLinearPrimeExpMeshTestSet j,
    trackBLinearPrimeExpVarianceBadSet j N

/-- Finite union of coefficient flatness failures over the exponential mesh
and its scheduled fresh-prime layers.  This is irreducible to keep public
probability statements from expanding the full nested coefficient event. -/
@[irreducible] noncomputable def trackBLinearPrimeExpFlatBadUnion (j : ℕ) : Set Omega :=
  ⋃ N ∈ trackBLinearPrimeExpMeshTestSet j,
    ⋃ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
      trackBLinearPrimeExpFlatBadSet j N p

/-- The finite stage-wise geometry-good failure budget obtained from pointwise
variance and flatness bad events.  Proving summability of this quantity is the
remaining high-probability geometry task for this workbench. -/
noncomputable def trackBLinearPrimeExpGeometryGoodFail (j : ℕ) : ℝ≥0∞ :=
  (∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
      mu (trackBLinearPrimeExpVarianceBadSet j N)) +
    ∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
      ∑ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
        mu (trackBLinearPrimeExpFlatBadSet j N p)

/-- The exponential variance-floor good event is measurable. -/
theorem measurableSet_trackBLinearPrimeExpVarianceGood (j : ℕ) :
    MeasurableSet (trackBLinearPrimeExpVarianceGood j) := by
  unfold trackBLinearPrimeExpVarianceGood
  refine MeasurableSet.iInter (fun N : ℕ => ?_)
  unfold trackBLinearPrimeExpVarianceGoodPoint
  by_cases hN : N ∈ trackBLinearPrimeExpMeshTestSet j
  · simp only [hN, true_implies]
    unfold trackBLinearPrimeExpScheduledVariance
    exact measurableSet_le measurable_const
      (measurable_trackBLinearPrimeScheduledVariance
        trackBLinearPrimeExpScheduleSpec.Q
        trackBLinearPrimeExpScheduleSpec.point
        trackBLinearPrimeExpScheduleSpec.freshLo
        trackBLinearPrimeExpScheduleSpec.freshHi j N)
  · have hset :
        {omega : Omega |
          N ∈ trackBLinearPrimeExpMeshTestSet j →
            trackBLinearPrimeExpScheduleSpec.V j ≤
              trackBLinearPrimeExpScheduledVariance omega j N} =
          Set.univ := by
        ext omega
        simp [hN]
    rw [hset]
    exact MeasurableSet.univ

set_option maxRecDepth 20000 in
set_option linter.constructorNameAsVariable false in
/-- The exponential coefficient-flatness good event is measurable. -/
theorem measurableSet_trackBLinearPrimeExpFlatGood (j : ℕ) :
    MeasurableSet (trackBLinearPrimeExpFlatGood j) := by
  unfold trackBLinearPrimeExpFlatGood
  refine MeasurableSet.iInter (fun N : ℕ => ?_)
  refine MeasurableSet.iInter (fun p : ℕ => ?_)
  unfold trackBLinearPrimeExpFlatGoodPoint
  by_cases hN : N ∈ trackBLinearPrimeExpMeshTestSet j
  · by_cases hp : p ∈ trackBLinearPrimeExpScheduledFreshSet j N
    · simp only [hN, hp, true_implies]
      have hcoeff :
          Measurable fun omega : Omega =>
            trackBLinearPrimeExpScheduledFreshCoeff omega j N p := by
        unfold trackBLinearPrimeExpScheduledFreshCoeff
        unfold trackBLinearPrimeScheduledFreshCoeff
        exact
          measurable_trackBSquarefreeFreshLinearCoeff
            (trackBLinearPrimeScheduledFreshSet
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi) j N p
      simpa [trackBLinearPrimeExpScheduledCoeffFlat] using
        measurableSet_le hcoeff.abs measurable_const
    · have hset :
          {omega : Omega |
            N ∈ trackBLinearPrimeExpMeshTestSet j →
              p ∈ trackBLinearPrimeExpScheduledFreshSet j N →
                trackBLinearPrimeExpScheduledCoeffFlat omega j N p} =
            Set.univ := by
          ext omega
          simp [hN, hp]
      rw [hset]
      exact MeasurableSet.univ
  · have hset :
        {omega : Omega |
          N ∈ trackBLinearPrimeExpMeshTestSet j →
            p ∈ trackBLinearPrimeExpScheduledFreshSet j N →
              trackBLinearPrimeExpScheduledCoeffFlat omega j N p} =
          Set.univ := by
        ext omega
        simp [hN]
    rw [hset]
    exact MeasurableSet.univ

/-- The exponential geometry good event is measurable. -/
theorem measurableSet_trackBLinearPrimeExpGeometryGood (j : ℕ) :
    MeasurableSet (trackBLinearPrimeExpGeometryGood j) := by
  unfold trackBLinearPrimeExpGeometryGood
  exact (measurableSet_trackBLinearPrimeExpVarianceGood j).inter
    (measurableSet_trackBLinearPrimeExpFlatGood j)

/-- The exponential one-point variance-bad event is measurable. -/
theorem measurableSet_trackBLinearPrimeExpVarianceBadSet (j N : ℕ) :
    MeasurableSet (trackBLinearPrimeExpVarianceBadSet j N) := by
  unfold trackBLinearPrimeExpVarianceBadSet trackBLinearPrimeExpScheduledVariance
  exact measurableSet_lt
    (measurable_trackBLinearPrimeScheduledVariance
      trackBLinearPrimeExpScheduleSpec.Q
      trackBLinearPrimeExpScheduleSpec.point
      trackBLinearPrimeExpScheduleSpec.freshLo
      trackBLinearPrimeExpScheduleSpec.freshHi j N)
    measurable_const

/-- At a mesh index, the scheduled variance-bad event is exactly the
layer-indexed variance-bad event. -/
theorem trackBLinearPrimeExpVarianceBadSet_eq_layer
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j) :
    trackBLinearPrimeExpVarianceBadSet j (trackBLinearPrimeExpScheduleSpec.point j r) =
      trackBLinearPrimeExpVarianceLayerBadSet j r := by
  ext omega
  unfold trackBLinearPrimeExpVarianceBadSet trackBLinearPrimeExpVarianceLayerBadSet
  simp only [Set.mem_setOf_eq]
  unfold trackBLinearPrimeExpScheduledVariance
  rw [trackBLinearPrimeExp_scheduledVariance_eq_layer omega j r hr]

/-- The layer-indexed exponential variance-bad event is measurable. -/
theorem measurableSet_trackBLinearPrimeExpVarianceLayerBadSet
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j) :
    MeasurableSet (trackBLinearPrimeExpVarianceLayerBadSet j r) := by
  rw [← trackBLinearPrimeExpVarianceBadSet_eq_layer j r hr]
  exact measurableSet_trackBLinearPrimeExpVarianceBadSet j
    (trackBLinearPrimeExpScheduleSpec.point j r)

/-- Measures of the scheduled and layer-indexed variance-bad events agree at a
mesh index. -/
theorem measure_trackBLinearPrimeExpVarianceBadSet_eq_layer
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j) :
    mu (trackBLinearPrimeExpVarianceBadSet j
        (trackBLinearPrimeExpScheduleSpec.point j r)) =
      mu (trackBLinearPrimeExpVarianceLayerBadSet j r) := by
  rw [trackBLinearPrimeExpVarianceBadSet_eq_layer j r hr]

/-- Rewrite the finite scheduled variance-bad sum as a layer-indexed mesh sum. -/
theorem sum_trackBLinearPrimeExpVarianceBadSet_eq_layer (j : ℕ) :
    (∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
        mu (trackBLinearPrimeExpVarianceBadSet j N)) =
      ∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
        mu (trackBLinearPrimeExpVarianceLayerBadSet j r) := by
  classical
  unfold trackBLinearPrimeExpMeshTestSet trackBLinearPrimeMeshTestSet
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro r hr
    rw [measure_trackBLinearPrimeExpVarianceBadSet_eq_layer j r hr]
  · intro r hr s hs hpoint
    have hinj :
        Set.InjOn (trackBLinearPrimeExpScheduleSpec.point j)
          (trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j : Set ℕ) := by
      refine trackBLinearPrimeMesh_injOn_of_strict
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j ?_
      intro a b ha hb hab
      exact trackBLinearPrimeExpPoint_strict j ha hb hab
    exact hinj (by simpa using hr) (by simpa using hs) hpoint

/-- The exponential one-coefficient flatness-bad event is measurable. -/
theorem measurableSet_trackBLinearPrimeExpFlatBadSet (j N p : ℕ) :
    MeasurableSet (trackBLinearPrimeExpFlatBadSet j N p) := by
  unfold trackBLinearPrimeExpFlatBadSet
  have hcoeff :
      Measurable fun omega : Omega => trackBLinearPrimeExpScheduledFreshCoeff omega j N p := by
    unfold trackBLinearPrimeExpScheduledFreshCoeff
    unfold trackBLinearPrimeScheduledFreshCoeff
    exact
      measurable_trackBSquarefreeFreshLinearCoeff
        (trackBLinearPrimeScheduledFreshSet
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi) j N p
  exact measurableSet_lt measurable_const hcoeff.abs

private theorem compl_iInter_imp_subset_biUnion_of_not
    (A : Finset ℕ) (B : ℕ → Finset ℕ)
    (P : Omega → ℕ → ℕ → Prop) (bad : ℕ → ℕ → Set Omega)
    (hbad :
      ∀ omega N p, N ∈ A → p ∈ B N → ¬ P omega N p → omega ∈ bad N p) :
    (⋂ N, ⋂ p, {omega : Omega | N ∈ A → p ∈ B N → P omega N p})ᶜ ⊆
      ⋃ N ∈ A, ⋃ p ∈ B N, bad N p := by
  intro omega homega
  by_contra hnot
  apply homega
  refine Set.mem_iInter.mpr ?_
  intro N
  refine Set.mem_iInter.mpr ?_
  intro p hN hp
  by_contra hP
  exact hnot (Set.mem_iUnion₂.mpr ⟨N, hN, Set.mem_iUnion₂.mpr ⟨p, hp,
    hbad omega N p hN hp hP⟩⟩)

/-- Union-bound control of the named exponential flatness-bad union. -/
theorem measure_trackBLinearPrimeExpFlatBadUnion_le_sum_bad (j : ℕ) :
    mu (trackBLinearPrimeExpFlatBadUnion j) ≤
      ∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
        ∑ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
          mu (trackBLinearPrimeExpFlatBadSet j N p) := by
  unfold trackBLinearPrimeExpFlatBadUnion
  calc
    mu (⋃ N ∈ trackBLinearPrimeExpMeshTestSet j,
          ⋃ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
            trackBLinearPrimeExpFlatBadSet j N p)
        ≤ ∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
            mu (⋃ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
              trackBLinearPrimeExpFlatBadSet j N p) :=
          measure_biUnion_finset_le (μ := mu)
            (trackBLinearPrimeExpMeshTestSet j)
            fun N => ⋃ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
              trackBLinearPrimeExpFlatBadSet j N p
    _ ≤ ∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
          ∑ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
            mu (trackBLinearPrimeExpFlatBadSet j N p) := by
        exact Finset.sum_le_sum (fun N _hN =>
          measure_biUnion_finset_le (μ := mu)
            (trackBLinearPrimeExpScheduledFreshSet j N)
            fun p => trackBLinearPrimeExpFlatBadSet j N p)

/-- Rewrite the finite scheduled flatness-bad sum as a layer-indexed mesh sum. -/
theorem sum_trackBLinearPrimeExpFlatBadSet_eq_layer (j : ℕ) :
    (∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
        ∑ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
          mu (trackBLinearPrimeExpFlatBadSet j N p)) =
      ∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
        ∑ p ∈ trackBLinearPrimeExpFreshLayer j r,
          mu (trackBLinearPrimeExpFlatLayerBadSet j r p) := by
  classical
  unfold trackBLinearPrimeExpMeshTestSet trackBLinearPrimeMeshTestSet
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro r hr
    rw [trackBLinearPrimeExpScheduledFreshSet,
      trackBLinearPrimeExp_scheduledFreshSet_eq_layer j r hr]
    simp [trackBLinearPrimeExpFreshLayer, trackBLinearPrimeExpFlatLayerBadSet]
  · intro r hr s hs hpoint
    have hinj :
        Set.InjOn (trackBLinearPrimeExpScheduleSpec.point j)
          (trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j : Set ℕ) := by
      refine trackBLinearPrimeMesh_injOn_of_strict
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j ?_
      intro a b ha hb hab
      exact trackBLinearPrimeExpPoint_strict j ha hb hab
    exact hinj (by simpa using hr) (by simpa using hs) hpoint

set_option maxRecDepth 20000 in
set_option linter.constructorNameAsVariable false in
/-- Union-bound control of the exponential flat-good complement from
pointwise coefficient flatness failures. -/
theorem measure_trackBLinearPrimeExpFlatGood_compl_le_sum_bad (j : ℕ) :
    mu (trackBLinearPrimeExpFlatGoodCompl j) ≤
      ∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
        ∑ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
          mu (trackBLinearPrimeExpFlatBadSet j N p) := by
  unfold trackBLinearPrimeExpFlatGoodCompl
  have hgeneric :
      (⋂ N, ⋂ p,
          {omega : Omega |
            N ∈ trackBLinearPrimeExpMeshTestSet j →
              p ∈ trackBLinearPrimeExpScheduledFreshSet j N →
                |trackBLinearPrimeExpScheduledFreshCoeff omega j N p| ≤
                  trackBLinearPrimeExpScheduleSpec.flat j})ᶜ ⊆
        ⋃ N ∈ trackBLinearPrimeExpMeshTestSet j,
          ⋃ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
            trackBLinearPrimeExpFlatBadSet j N p :=
    compl_iInter_imp_subset_biUnion_of_not
      (trackBLinearPrimeExpMeshTestSet j)
      (fun N => trackBLinearPrimeExpScheduledFreshSet j N)
      (fun omega N p =>
        |trackBLinearPrimeExpScheduledFreshCoeff omega j N p| ≤
          trackBLinearPrimeExpScheduleSpec.flat j)
      (fun N p => trackBLinearPrimeExpFlatBadSet j N p)
      (by
        intro omega N p _hN _hp hnot
        unfold trackBLinearPrimeExpFlatBadSet
        exact lt_of_not_ge hnot)
  have hsubset :
      (trackBLinearPrimeExpFlatGood j)ᶜ ⊆
        ⋃ N ∈ trackBLinearPrimeExpMeshTestSet j,
          ⋃ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
            trackBLinearPrimeExpFlatBadSet j N p := by
    intro omega homega
    apply hgeneric
    intro hmem
    apply homega
    rw [trackBLinearPrimeExpFlatGood]
    refine Set.mem_iInter.mpr ?_
    intro N
    refine Set.mem_iInter.mpr ?_
    intro p
    unfold trackBLinearPrimeExpFlatGoodPoint
    exact (Set.mem_iInter.mp (Set.mem_iInter.mp hmem N) p)
  calc
    mu (trackBLinearPrimeExpFlatGood j)ᶜ
        ≤ mu (⋃ N ∈ trackBLinearPrimeExpMeshTestSet j,
            ⋃ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
              trackBLinearPrimeExpFlatBadSet j N p) :=
          measure_mono hsubset
    _ ≤ ∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
          ∑ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
            mu (trackBLinearPrimeExpFlatBadSet j N p) := by
        calc
          mu (⋃ N ∈ trackBLinearPrimeExpMeshTestSet j,
              ⋃ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
                trackBLinearPrimeExpFlatBadSet j N p)
              ≤ ∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
                  mu (⋃ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
                    trackBLinearPrimeExpFlatBadSet j N p) :=
                measure_biUnion_finset_le (μ := mu)
                  (trackBLinearPrimeExpMeshTestSet j)
                  fun N => ⋃ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
                    trackBLinearPrimeExpFlatBadSet j N p
          _ ≤ ∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
                ∑ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
                  mu (trackBLinearPrimeExpFlatBadSet j N p) := by
              exact Finset.sum_le_sum (fun N _hN =>
                measure_biUnion_finset_le (μ := mu)
                  (trackBLinearPrimeExpScheduledFreshSet j N)
                  fun p => trackBLinearPrimeExpFlatBadSet j N p)

/-- Membership in the exponential geometry-good event gives the variance floor
in the compact exponential-schedule alias language. -/
theorem trackBLinearPrimeExpGeometryGood_variance_floor
    {omega : Omega} {j N : ℕ}
    (hgood : omega ∈ trackBLinearPrimeExpGeometryGood j)
    (hN : N ∈ trackBLinearPrimeExpMeshTestSet j) :
    trackBLinearPrimeExpScheduleSpec.V j ≤
      trackBLinearPrimeExpScheduledVariance omega j N :=
  (Set.mem_iInter.mp hgood.1 N) hN

/-- Membership in the exponential geometry-good event gives each named
coefficient-flatness point event. -/
theorem trackBLinearPrimeExpGeometryGood_flatGoodPoint
    {omega : Omega} {j N p : ℕ}
    (hgood : omega ∈ trackBLinearPrimeExpGeometryGood j) :
    omega ∈ trackBLinearPrimeExpFlatGoodPoint j N p :=
  Set.mem_iInter.mp (Set.mem_iInter.mp hgood.2 N) p

/-- Layer-indexed characterization of the exponential variance-good event. -/
theorem mem_trackBLinearPrimeExpVarianceGood_iff_layer
    (omega : Omega) (j : ℕ) :
    omega ∈ trackBLinearPrimeExpVarianceGood j ↔
      ∀ r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
        trackBLinearPrimeExpScheduleSpec.V j ≤
          ∑ p ∈
            trackBFreshPrimeLayer
              (trackBLinearPrimeExpScheduleSpec.freshLo j r)
              (trackBLinearPrimeExpScheduleSpec.freshHi j r),
            (trackBLinearPrimeScheduledFreshCoeff
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) p) ^ 2 := by
  constructor
  · intro hgood r hr
    have hN :
        trackBLinearPrimeExpScheduleSpec.point j r ∈
          trackBLinearPrimeExpMeshTestSet j := by
      unfold trackBLinearPrimeExpMeshTestSet
      rw [mem_trackBLinearPrimeMeshTestSet]
      exact ⟨r, hr, rfl⟩
    have hv :=
      (Set.mem_iInter.mp hgood (trackBLinearPrimeExpScheduleSpec.point j r)) hN
    simpa [trackBLinearPrimeExpScheduledVariance,
      trackBLinearPrimeExp_scheduledVariance_eq_layer omega j r hr] using hv
  · intro hgood
    rw [trackBLinearPrimeExpVarianceGood]
    refine Set.mem_iInter.mpr ?_
    intro N hN
    have hN' :
        N ∈ trackBLinearPrimeMeshTestSet
          trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j := by
      simpa [trackBLinearPrimeExpMeshTestSet] using hN
    rcases mem_trackBLinearPrimeMeshTestSet.mp hN' with ⟨r, hr, hpoint⟩
    subst N
    simpa [trackBLinearPrimeExpScheduledVariance,
      trackBLinearPrimeExp_scheduledVariance_eq_layer omega j r hr] using hgood r hr

/-- If exponential variance-good fails at stage `j`, then one scheduled test
point has variance below the target. -/
theorem trackBLinearPrimeExpVarianceGood_compl_subset_exists_bad (j : ℕ) :
    (trackBLinearPrimeExpVarianceGood j)ᶜ ⊆
      trackBLinearPrimeExpVarianceBadUnion j := by
  intro omega homega
  rw [trackBLinearPrimeExpVarianceGood] at homega
  by_contra hnot
  apply homega
  refine Set.mem_iInter.mpr ?_
  intro N
  unfold trackBLinearPrimeExpVarianceGoodPoint
  intro hN
  by_contra hfloor
  have hbad : omega ∈ trackBLinearPrimeExpVarianceBadSet j N := by
    unfold trackBLinearPrimeExpVarianceBadSet
    exact lt_of_not_ge hfloor
  unfold trackBLinearPrimeExpVarianceBadUnion at hnot
  exact hnot (Set.mem_iUnion₂.mpr ⟨N, hN, hbad⟩)

/-- Union-bound control of the named exponential variance-bad union. -/
theorem measure_trackBLinearPrimeExpVarianceBadUnion_le_sum_bad (j : ℕ) :
    mu (trackBLinearPrimeExpVarianceBadUnion j) ≤
      ∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
        mu (trackBLinearPrimeExpVarianceBadSet j N) := by
  unfold trackBLinearPrimeExpVarianceBadUnion
  exact
    measure_biUnion_finset_le (μ := mu)
      (trackBLinearPrimeExpMeshTestSet j)
      fun N => trackBLinearPrimeExpVarianceBadSet j N

/-- Union-bound control of the exponential variance-good complement from
pointwise variance lower-tail failures. -/
theorem measure_trackBLinearPrimeExpVarianceGood_compl_le_sum_bad (j : ℕ) :
    mu (trackBLinearPrimeExpVarianceGood j)ᶜ ≤
      ∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
        mu (trackBLinearPrimeExpVarianceBadSet j N) := by
  exact le_trans
    (measure_mono (trackBLinearPrimeExpVarianceGood_compl_subset_exists_bad j))
    (measure_trackBLinearPrimeExpVarianceBadUnion_le_sum_bad j)

/-- Union-bound control of the exponential variance-good complement in the
analytic layer-indexed form. -/
theorem measure_trackBLinearPrimeExpVarianceGood_compl_le_sum_layer_bad (j : ℕ) :
    mu (trackBLinearPrimeExpVarianceGood j)ᶜ ≤
      ∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
        mu (trackBLinearPrimeExpVarianceLayerBadSet j r) := by
  simpa [sum_trackBLinearPrimeExpVarianceBadSet_eq_layer j] using
    measure_trackBLinearPrimeExpVarianceGood_compl_le_sum_bad j

/-- The stage-wise geometry-good complement is controlled by the finite
variance-bad union plus the remaining flat-good complement. -/
theorem measure_trackBLinearPrimeExpGeometryGood_compl_le_variance_sum_add_flatCompl
    (j : ℕ) :
    mu (trackBLinearPrimeExpGeometryGood j)ᶜ ≤
      (∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
        mu (trackBLinearPrimeExpVarianceBadSet j N)) +
        mu (trackBLinearPrimeExpFlatGoodCompl j) := by
  have hcompl :
      (trackBLinearPrimeExpGeometryGood j)ᶜ =
        (trackBLinearPrimeExpVarianceGood j)ᶜ ∪
          trackBLinearPrimeExpFlatGoodCompl j := by
    unfold trackBLinearPrimeExpFlatGoodCompl
    rw [trackBLinearPrimeExpGeometryGood, Set.compl_inter]
  calc
    mu (trackBLinearPrimeExpGeometryGood j)ᶜ
        = mu ((trackBLinearPrimeExpVarianceGood j)ᶜ ∪
            trackBLinearPrimeExpFlatGoodCompl j) := by
          rw [hcompl]
    _ ≤ mu (trackBLinearPrimeExpVarianceGood j)ᶜ +
          mu (trackBLinearPrimeExpFlatGoodCompl j) :=
        measure_union_le _ _
    _ ≤ (∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
            mu (trackBLinearPrimeExpVarianceBadSet j N)) +
          mu (trackBLinearPrimeExpFlatGoodCompl j) := by
        exact add_le_add
          (measure_trackBLinearPrimeExpVarianceGood_compl_le_sum_bad j)
          (le_refl _)

/-- Layer-indexed version of the geometry-good complement bound.  The remaining
flat-good complement is kept as an explicit analytic obligation. -/
theorem measure_trackBLinearPrimeExpGeometryGood_compl_le_variance_layer_sum_add_flatCompl
    (j : ℕ) :
    mu (trackBLinearPrimeExpGeometryGood j)ᶜ ≤
      (∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
        mu (trackBLinearPrimeExpVarianceLayerBadSet j r)) +
        mu (trackBLinearPrimeExpFlatGoodCompl j) := by
  simpa [sum_trackBLinearPrimeExpVarianceBadSet_eq_layer j] using
    measure_trackBLinearPrimeExpGeometryGood_compl_le_variance_sum_add_flatCompl j

/-- Layer-indexed stage failure budget for the exponential geometry-good
event.  The variance part is now indexed by mesh indices instead of image test
points; the flatness complement remains a named analytic obligation. -/
noncomputable def trackBLinearPrimeExpGeometryGoodLayerFail (j : ℕ) : ℝ≥0∞ :=
  (∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
      mu (trackBLinearPrimeExpVarianceLayerBadSet j r)) +
    mu (trackBLinearPrimeExpFlatGoodCompl j)

/-- The named layer-indexed geometry-good failure budget controls the
complement of the geometry-good event. -/
theorem measure_trackBLinearPrimeExpGeometryGood_compl_le_layerFail (j : ℕ) :
    mu (trackBLinearPrimeExpGeometryGood j)ᶜ ≤
      trackBLinearPrimeExpGeometryGoodLayerFail j := by
  simpa [trackBLinearPrimeExpGeometryGoodLayerFail] using
    measure_trackBLinearPrimeExpGeometryGood_compl_le_variance_layer_sum_add_flatCompl j

/-- Analytic probability inputs for making `trackBLinearPrimeExpGeometryGood`
a genuine high-probability good event. -/
structure TrackBLinearPrimeExpGeometryGoodProbabilityFacts where
  varianceLayerFail : ℕ → ℕ → ℝ≥0∞
  flatFail : ℕ → ℝ≥0∞
  variance_layer_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      mu (trackBLinearPrimeExpVarianceLayerBadSet j r) ≤ varianceLayerFail j r
  flat_compl_le : ∀ j, mu (trackBLinearPrimeExpFlatGoodCompl j) ≤ flatFail j
  fail_summable :
    (∑' j,
      ((∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
          varianceLayerFail j r) + flatFail j)) ≠ ⊤

/-- Failure budget generated from analytic pointwise variance and flatness
probability estimates. -/
noncomputable def trackBLinearPrimeExpGeometryGoodFailOfProbabilityFacts
    (h : TrackBLinearPrimeExpGeometryGoodProbabilityFacts) (j : ℕ) : ℝ≥0∞ :=
  (∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
      h.varianceLayerFail j r) + h.flatFail j

/-- Analytic pointwise probability inputs control the geometry-good complement. -/
theorem measure_trackBLinearPrimeExpGeometryGood_compl_le_failOfProbabilityFacts
    (h : TrackBLinearPrimeExpGeometryGoodProbabilityFacts) (j : ℕ) :
    mu (trackBLinearPrimeExpGeometryGood j)ᶜ ≤
      trackBLinearPrimeExpGeometryGoodFailOfProbabilityFacts h j := by
  calc
    mu (trackBLinearPrimeExpGeometryGood j)ᶜ
        ≤ trackBLinearPrimeExpGeometryGoodLayerFail j :=
          measure_trackBLinearPrimeExpGeometryGood_compl_le_layerFail j
    _ ≤ trackBLinearPrimeExpGeometryGoodFailOfProbabilityFacts h j := by
        unfold trackBLinearPrimeExpGeometryGoodLayerFail
        unfold trackBLinearPrimeExpGeometryGoodFailOfProbabilityFacts
        exact add_le_add
          (Finset.sum_le_sum (fun r hr => h.variance_layer_bad_le j r hr))
          (h.flat_compl_le j)

/-- Stage facts for the exponential schedule using the geometry-good event and
analytic failure budget. -/
def trackBLinearPrimeExpScheduleStageFactsWithGeometryGood
    (h : TrackBLinearPrimeExpGeometryGoodProbabilityFacts) :
    TrackBLinearPrimeScheduleStageFacts
      (trackBLinearPrimeExpScheduleSpecWithGood
        trackBLinearPrimeExpGeometryGood
        (trackBLinearPrimeExpGeometryGoodFailOfProbabilityFacts h)) :=
  trackBLinearPrimeExpScheduleStageFactsWithGood
    trackBLinearPrimeExpGeometryGood
    (trackBLinearPrimeExpGeometryGoodFailOfProbabilityFacts h)
    (by
      simpa [trackBLinearPrimeExpScheduleSpecWithGood,
        trackBLinearPrimeExpGeometryGoodFailOfProbabilityFacts] using h.fail_summable)

/-- Good-event facts for the exponential schedule using the geometry-good event
and analytic failure budget. -/
noncomputable def trackBLinearPrimeExpScheduleGoodEventFactsWithGeometryGood
    (h : TrackBLinearPrimeExpGeometryGoodProbabilityFacts) :
    TrackBLinearPrimeScheduleGoodEventFacts
      (trackBLinearPrimeExpScheduleSpecWithGood
        trackBLinearPrimeExpGeometryGood
        (trackBLinearPrimeExpGeometryGoodFailOfProbabilityFacts h)) :=
  trackBLinearPrimeExpScheduleGoodEventFactsWithGood
    trackBLinearPrimeExpGeometryGood
    (trackBLinearPrimeExpGeometryGoodFailOfProbabilityFacts h)
    measurableSet_trackBLinearPrimeExpGeometryGood
    (measure_trackBLinearPrimeExpGeometryGood_compl_le_failOfProbabilityFacts h)

/-- The shifted eighth-power reciprocal is summable. -/
theorem trackBLinearPrimeConcrete_inv_base_eight_summable :
    Summable fun j : ℕ => (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹ := by
  have hbase : Summable fun n : ℕ => (((n : ℝ) ^ (8 : ℝ)))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 8)
  have hshift :
      Summable fun j : ℕ => ((((j + 2 : ℕ) : ℝ) ^ (8 : ℝ)))⁻¹ := by
    simpa [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff (f := fun n : ℕ => (((n : ℝ) ^ (8 : ℝ)))⁻¹) 2).mpr
        hbase
  simpa [trackBLinearPrimeConcreteBase, Real.rpow_natCast] using hshift

/-- Concrete stage budget for the layer variance lower-tail part of the
exponential geometry-good event. -/
noncomputable def trackBLinearPrimeExpGeometryVarianceLayerSumBudget (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹)

/-- Pointwise layer variance lower-tail budget.  Summing this over the
`Q_j = base_j^4` mesh indices pays the stage variance budget
`base_j^-8`. -/
noncomputable def trackBLinearPrimeExpGeometryVarianceLayerPointBudget
    (j _r : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 12))⁻¹)

/-- Real-valued pointwise layer variance lower-tail budget. -/
noncomputable def trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal
    (j _r : ℕ) : ℝ :=
  (((trackBLinearPrimeConcreteBase j : ℝ) ^ 12))⁻¹

/-- The `ENNReal` pointwise variance budget is the `ofReal` of the real-valued
budget. -/
theorem trackBLinearPrimeExpGeometryVarianceLayerPointBudget_eq_ofReal (j r : ℕ) :
    trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r =
      ENNReal.ofReal (trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r) := by
  rfl

/-- Four `base^-14` bad-event budgets fit inside the pointwise `base^-12`
variance budget. -/
theorem trackBLinearPrimeExp_four_inv_base_pow_fourteen_le_variancePointBudgetReal
    (j r : ℕ) :
    4 * ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹) ≤
      trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r := by
  have hb2 : (2 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
    exact_mod_cast trackBLinearPrimeConcreteBase_two_le j
  have hpow2 : (4 : ℝ) ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 2 := by
    have hmono : (2 : ℝ) ^ 2 ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hb2 2
    norm_num at hmono ⊢
    exact hmono
  have hinv2 : 4 * ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 2))⁻¹) ≤ 1 := by
    have hpos : (0 : ℝ) < (trackBLinearPrimeConcreteBase j : ℝ) ^ 2 := by
      positivity
    have hle : (((trackBLinearPrimeConcreteBase j : ℝ) ^ 2))⁻¹ ≤ (1 : ℝ) / 4 := by
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hpow2
    nlinarith
  have hpow_eq :
      (trackBLinearPrimeConcreteBase j : ℝ) ^ 14 =
        (trackBLinearPrimeConcreteBase j : ℝ) ^ 12 *
          (trackBLinearPrimeConcreteBase j : ℝ) ^ 2 := by
    rw [show 14 = 12 + 2 by norm_num, pow_add]
  calc
    4 * ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
        = (((trackBLinearPrimeConcreteBase j : ℝ) ^ 12))⁻¹ *
            (4 * ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 2))⁻¹)) := by
          rw [hpow_eq, mul_inv_rev]
          ring
    _ ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 12))⁻¹ * 1 := by
          gcongr
    _ = trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r := by
          simp [trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal]

/-- `ENNReal` version of the four-event `base^-14` budget bridge. -/
theorem trackBLinearPrimeExp_four_inv_base_pow_fourteen_le_variancePointBudget
    (j r : ℕ) :
    ENNReal.ofReal (4 * ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)) ≤
      trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r := by
  rw [trackBLinearPrimeExpGeometryVarianceLayerPointBudget_eq_ofReal j r]
  exact ENNReal.ofReal_le_ofReal
    (trackBLinearPrimeExp_four_inv_base_pow_fourteen_le_variancePointBudgetReal j r)

/-- Concrete stage budget for the flat-good complement. -/
noncomputable def trackBLinearPrimeExpGeometryFlatBudget (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹)

/-- The exponential schedule flatness threshold is positive. -/
theorem trackBLinearPrimeExp_flat_pos (j : ℕ) :
    0 < trackBLinearPrimeExpScheduleSpec.flat j := by
  have hbase : (0 : ℝ) < trackBLinearPrimeConcreteBase j := by
    exact_mod_cast trackBLinearPrimeConcreteBase_pos j
  simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteFlat] using
    inv_pos.mpr (pow_pos hbase trackBLinearPrimeConcreteK)

/-- Concrete summable failure budget for the exponential geometry-good event. -/
noncomputable def trackBLinearPrimeExpGeometryGoodConcreteFail (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹)

/-- The concrete exponential geometry-good failure budget is summable. -/
theorem trackBLinearPrimeExpGeometryGoodConcreteFail_tsum_ne_top :
    (∑' j, trackBLinearPrimeExpGeometryGoodConcreteFail j) ≠ ⊤ := by
  have hs :
      Summable fun j : ℕ =>
        2 * (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹ :=
    trackBLinearPrimeConcrete_inv_base_eight_summable.mul_left 2
  simpa [trackBLinearPrimeExpGeometryGoodConcreteFail] using hs.tsum_ofReal_ne_top

/-- The pointwise `base_j^-12` layer variance budget sums to at most the
stage variance budget `base_j^-8`. -/
theorem sum_trackBLinearPrimeExpGeometryVarianceLayerPointBudget_le
    (j : ℕ) :
    (∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
        trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r) ≤
      trackBLinearPrimeExpGeometryVarianceLayerSumBudget j := by
  have hb0 : (trackBLinearPrimeConcreteBase j : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (trackBLinearPrimeConcreteBase_pos j))
  have hb8 : ((trackBLinearPrimeConcreteBase j : ℝ) ^ 8) ≠ 0 := pow_ne_zero 8 hb0
  have hb12 : ((trackBLinearPrimeConcreteBase j : ℝ) ^ 12) ≠ 0 := pow_ne_zero 12 hb0
  have hreal_base :
      (trackBLinearPrimeConcreteBase j ^ 4 : ℝ) *
          (((trackBLinearPrimeConcreteBase j : ℝ) ^ 12))⁻¹ ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹
      := by
    field_simp [hb8, hb12]
    norm_num
  have hreal :
      (trackBLinearPrimeExpScheduleSpec.Q j : ℝ) *
          (((trackBLinearPrimeConcreteBase j : ℝ) ^ 12))⁻¹ ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹ := by
    simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteQ] using hreal_base
  calc
    (∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
        trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r)
        = (trackBLinearPrimeExpScheduleSpec.Q j) •
            ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 12))⁻¹) := by
          simp [trackBLinearPrimeExpGeometryVarianceLayerPointBudget,
            trackBLinearPrimeMeshIndexSet_card]
    _ = ENNReal.ofReal
          ((trackBLinearPrimeExpScheduleSpec.Q j : ℝ) *
            (((trackBLinearPrimeConcreteBase j : ℝ) ^ 12))⁻¹) := by
          rw [← ENNReal.ofReal_nsmul]
          simp [nsmul_eq_mul]
    _ ≤ trackBLinearPrimeExpGeometryVarianceLayerSumBudget j := by
          simpa [trackBLinearPrimeExpGeometryVarianceLayerSumBudget] using
            ENNReal.ofReal_le_ofReal hreal

/-- Concrete analytic probability inputs for the exponential geometry-good
event.  The variance input is already summed over the mesh, so the analytic
side can prove either this bound directly or derive it from one-point
layer-bad bounds. -/
structure TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts where
  variance_layer_sum_le :
    ∀ j,
      (∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
        mu (trackBLinearPrimeExpVarianceLayerBadSet j r)) ≤
        trackBLinearPrimeExpGeometryVarianceLayerSumBudget j
  flat_compl_le :
    ∀ j, mu (trackBLinearPrimeExpFlatGoodCompl j) ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Pointwise version of the concrete analytic probability inputs. -/
structure TrackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts where
  variance_layer_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      mu (trackBLinearPrimeExpVarianceLayerBadSet j r) ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r
  flat_compl_le :
    ∀ j, mu (trackBLinearPrimeExpFlatGoodCompl j) ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Layer-indexed pointwise coefficient-flatness probability inputs.  This is
the finite-union form of the flat-good complement estimate: prove one
coefficient tail bound and a stage-wise finite-sum budget. -/
structure TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts where
  flatLayerFail : ℕ → ℕ → ℕ → ℝ≥0∞
  flat_layer_bad_le :
    ∀ j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBLinearPrimeExpFreshLayer j r →
        mu (trackBLinearPrimeExpFlatLayerBadSet j r p) ≤ flatLayerFail j r p
  flat_layer_sum_le :
    ∀ j,
      (∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
        ∑ p ∈ trackBLinearPrimeExpFreshLayer j r, flatLayerFail j r p) ≤
        trackBLinearPrimeExpGeometryFlatBudget j

/-- Layer-indexed coefficient flatness tail estimates imply the stage
flat-good complement budget. -/
theorem measure_trackBLinearPrimeExpFlatGood_compl_le_of_layerProbabilityFacts
    (h : TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts) (j : ℕ) :
    mu (trackBLinearPrimeExpFlatGoodCompl j) ≤
      trackBLinearPrimeExpGeometryFlatBudget j := by
  calc
    mu (trackBLinearPrimeExpFlatGoodCompl j)
        ≤ ∑ N ∈ trackBLinearPrimeExpMeshTestSet j,
            ∑ p ∈ trackBLinearPrimeExpScheduledFreshSet j N,
              mu (trackBLinearPrimeExpFlatBadSet j N p) :=
          measure_trackBLinearPrimeExpFlatGood_compl_le_sum_bad j
    _ = ∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
          ∑ p ∈ trackBLinearPrimeExpFreshLayer j r,
            mu (trackBLinearPrimeExpFlatLayerBadSet j r p) :=
          sum_trackBLinearPrimeExpFlatBadSet_eq_layer j
    _ ≤ ∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
          ∑ p ∈ trackBLinearPrimeExpFreshLayer j r, h.flatLayerFail j r p := by
        exact Finset.sum_le_sum (fun r hr =>
          Finset.sum_le_sum (fun p hp => h.flat_layer_bad_le j r p hr hp))
    _ ≤ trackBLinearPrimeExpGeometryFlatBudget j :=
        h.flat_layer_sum_le j

/-- The square of one exponential scheduled fresh coefficient is integrable. -/
theorem integrable_trackBLinearPrimeExpScheduledFreshCoeff_sq (j N p : ℕ) :
    Integrable (fun omega : Omega =>
      (trackBLinearPrimeExpScheduledFreshCoeff omega j N p) ^ 2) mu := by
  unfold trackBLinearPrimeExpScheduledFreshCoeff trackBLinearPrimeScheduledFreshCoeff
  unfold trackBSquarefreeFreshLinearCoeff
  exact integrable_trackBSquarefreeFreshCoeff_sq _ _ _

/-- Exact second moment of one exponential layer coefficient at a mesh point. -/
theorem integral_trackBLinearPrimeExpFlatLayerCoeff_sq_eq
    (j r p : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j) :
    (∫ omega,
      (trackBLinearPrimeExpScheduledFreshCoeff
        omega j (trackBLinearPrimeExpScheduleSpec.point j r) p) ^ 2 ∂mu) =
      ∑ m ∈ trackBLinearPrimeExpLayerCoeffSupport j r p,
        ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2 := by
  unfold trackBLinearPrimeExpScheduledFreshCoeff trackBLinearPrimeScheduledFreshCoeff
  unfold trackBSquarefreeFreshLinearCoeff
  rw [trackBLinearPrimeExp_scheduledFreshSet_eq_layer j r hr]
  simpa [trackBLinearPrimeExpFreshLayer, trackBLinearPrimeExpLayerCoeffSupport] using
    integral_trackBSquarefreeFreshCoeff_sq_eq
      (trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r))
      (trackBLinearPrimeExpScheduleSpec.point j r) p

/-- One-coefficient exponential flatness failure is controlled by the
coefficient second moment. -/
theorem measure_trackBLinearPrimeExpFlatLayerBadSet_le_second
    (flatSecond : ℕ → ℕ → ℕ → ℝ) (j r p : ℕ)
    (hsecond :
      (∫ omega,
        (trackBLinearPrimeExpScheduledFreshCoeff
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p) ^ 2 ∂mu) ≤
        flatSecond j r p) :
    mu (trackBLinearPrimeExpFlatLayerBadSet j r p) ≤
      ENNReal.ofReal
        (flatSecond j r p / (trackBLinearPrimeExpScheduleSpec.flat j) ^ 2) := by
  unfold trackBLinearPrimeExpFlatLayerBadSet trackBLinearPrimeExpFlatBadSet
  exact
    measure_abs_error_gt_le_second
      (E := fun omega =>
        trackBLinearPrimeExpScheduledFreshCoeff
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p)
      (A := trackBLinearPrimeExpScheduleSpec.flat j)
      (V := flatSecond j r p)
      (trackBLinearPrimeExp_flat_pos j)
      (integrable_trackBLinearPrimeExpScheduledFreshCoeff_sq j
        (trackBLinearPrimeExpScheduleSpec.point j r) p)
      hsecond

/-- Finite coefficient-flatness second-moment budget over one stage. -/
noncomputable def trackBLinearPrimeExpFlatLayerSecondMomentBudget
    (flatSecond : ℕ → ℕ → ℕ → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
    ∑ p ∈ trackBLinearPrimeExpFreshLayer j r,
      ENNReal.ofReal
        (flatSecond j r p / (trackBLinearPrimeExpScheduleSpec.flat j) ^ 2)

/-- Finite coefficient-flatness budget expressed through upper bounds for the
coefficient-support reciprocal masses. -/
noncomputable def trackBLinearPrimeExpFlatLayerReciprocalMassUpperBudget
    (supportUpper : ℕ → ℕ → ℕ → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
    ∑ p ∈ trackBLinearPrimeExpFreshLayer j r,
      ENNReal.ofReal
        (((p : ℝ)⁻¹ * supportUpper j r p) /
          (trackBLinearPrimeExpScheduleSpec.flat j) ^ 2)

/-- Real-valued version of the finite flatness budget coming from
coefficient-support reciprocal-mass upper bounds. -/
noncomputable def trackBLinearPrimeExpFlatLayerReciprocalMassUpperRealBudget
    (supportUpper : ℕ → ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
    ∑ p ∈ trackBLinearPrimeExpFreshLayer j r,
      (((p : ℝ)⁻¹ * supportUpper j r p) /
        (trackBLinearPrimeExpScheduleSpec.flat j) ^ 2)

/-- Flatness budget obtained from the trivial harmonic interval upper bound on
each coefficient support. -/
noncomputable def trackBLinearPrimeExpFlatLayerHarmonicUpperBudget (j : ℕ) : ℝ≥0∞ :=
  trackBLinearPrimeExpFlatLayerReciprocalMassUpperBudget
    trackBLinearPrimeExpSupportHarmonicUpper j

/-- Real-valued finite harmonic flatness budget.  This is the scalar form that
the analytic estimate should usually prove. -/
noncomputable def trackBLinearPrimeExpFlatLayerHarmonicUpperRealBudget (j : ℕ) : ℝ :=
  ∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
    ∑ p ∈ trackBLinearPrimeExpFreshLayer j r,
      (((p : ℝ)⁻¹ * trackBLinearPrimeExpSupportHarmonicUpper j r p) /
        (trackBLinearPrimeExpScheduleSpec.flat j) ^ 2)

/-- Real-valued flat-good complement budget. -/
noncomputable def trackBLinearPrimeExpGeometryFlatBudgetReal (j : ℕ) : ℝ :=
  (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹

/-- Real-valued finite budget for arbitrary layer-indexed coefficient-flatness
tail bounds.  This is the scalar form suited to subgaussian or
Littlewood-Offord flatness estimates. -/
noncomputable def trackBLinearPrimeExpFlatLayerRealProbabilityBudget
    (flatLayerFail : ℕ → ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
    ∑ p ∈ trackBLinearPrimeExpFreshLayer j r, flatLayerFail j r p

/-- The `ENNReal` finite budget obtained by applying `ofReal` pointwise is the
`ofReal` of the real-valued finite budget when all active summands are
nonnegative. -/
theorem trackBLinearPrimeExpFlatLayerRealProbabilityBudget_eq_ofReal
    (flatLayerFail : ℕ → ℕ → ℕ → ℝ)
    (hfail_nonneg :
      ∀ j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
        p ∈ trackBLinearPrimeExpFreshLayer j r → 0 ≤ flatLayerFail j r p)
    (j : ℕ) :
    (∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
      ∑ p ∈ trackBLinearPrimeExpFreshLayer j r,
        ENNReal.ofReal (flatLayerFail j r p)) =
      ENNReal.ofReal (trackBLinearPrimeExpFlatLayerRealProbabilityBudget flatLayerFail j) := by
  classical
  unfold trackBLinearPrimeExpFlatLayerRealProbabilityBudget
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun r hr => Finset.sum_nonneg fun p hp => hfail_nonneg j r p hr hp)]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [ENNReal.ofReal_sum_of_nonneg (fun p hp => hfail_nonneg j r p hr hp)]

/-- One summand in the harmonic flatness budget is nonnegative. -/
theorem trackBLinearPrimeExp_harmonic_flat_summand_nonneg (j r p : ℕ) :
    0 ≤
      (((p : ℝ)⁻¹ * trackBLinearPrimeExpSupportHarmonicUpper j r p) /
        (trackBLinearPrimeExpScheduleSpec.flat j) ^ 2) := by
  have hmass : 0 ≤ trackBLinearPrimeExpSupportHarmonicUpper j r p :=
    trackBLinearPrimeExpSupportHarmonicUpper_nonneg j r p
  have hnum :
      0 ≤ (p : ℝ)⁻¹ * trackBLinearPrimeExpSupportHarmonicUpper j r p :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) hmass
  exact div_nonneg hnum (sq_nonneg _)

/-- One summand in a reciprocal-mass upper flatness budget is nonnegative when
the supplied support upper bound is nonnegative. -/
theorem trackBLinearPrimeExp_reciprocal_flat_summand_nonneg
    (supportUpper : ℕ → ℕ → ℕ → ℝ) (j r p : ℕ)
    (hsupport : 0 ≤ supportUpper j r p) :
    0 ≤
      (((p : ℝ)⁻¹ * supportUpper j r p) /
        (trackBLinearPrimeExpScheduleSpec.flat j) ^ 2) := by
  have hnum : 0 ≤ (p : ℝ)⁻¹ * supportUpper j r p :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) hsupport
  exact div_nonneg hnum (sq_nonneg _)

/-- The `ENNReal` reciprocal-mass upper flatness budget is the `ofReal` of its
real-valued version when all supplied upper bounds are nonnegative. -/
theorem trackBLinearPrimeExpFlatLayerReciprocalMassUpperBudget_eq_ofReal
    (supportUpper : ℕ → ℕ → ℕ → ℝ)
    (hsupport : ∀ j r p, 0 ≤ supportUpper j r p) (j : ℕ) :
    trackBLinearPrimeExpFlatLayerReciprocalMassUpperBudget supportUpper j =
      ENNReal.ofReal
        (trackBLinearPrimeExpFlatLayerReciprocalMassUpperRealBudget supportUpper j) := by
  classical
  unfold trackBLinearPrimeExpFlatLayerReciprocalMassUpperBudget
  unfold trackBLinearPrimeExpFlatLayerReciprocalMassUpperRealBudget
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun r hr => Finset.sum_nonneg fun p hp =>
      trackBLinearPrimeExp_reciprocal_flat_summand_nonneg supportUpper j r p
        (hsupport j r p))]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun p hp =>
      trackBLinearPrimeExp_reciprocal_flat_summand_nonneg supportUpper j r p
        (hsupport j r p))]

/-- The `ENNReal` harmonic flatness budget is exactly the `ofReal` of the
real-valued finite harmonic budget. -/
theorem trackBLinearPrimeExpFlatLayerHarmonicUpperBudget_eq_ofReal
    (j : ℕ) :
    trackBLinearPrimeExpFlatLayerHarmonicUpperBudget j =
      ENNReal.ofReal (trackBLinearPrimeExpFlatLayerHarmonicUpperRealBudget j) := by
  classical
  unfold trackBLinearPrimeExpFlatLayerHarmonicUpperBudget
  unfold trackBLinearPrimeExpFlatLayerReciprocalMassUpperBudget
  unfold trackBLinearPrimeExpFlatLayerHarmonicUpperRealBudget
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun r hr => Finset.sum_nonneg fun p hp =>
      trackBLinearPrimeExp_harmonic_flat_summand_nonneg j r p)]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun p hp => trackBLinearPrimeExp_harmonic_flat_summand_nonneg j r p)]

/-- Second-moment inputs for the layer-indexed coefficient flatness tails. -/
structure TrackBLinearPrimeExpFlatGoodLayerSecondMomentFacts where
  flatSecond : ℕ → ℕ → ℕ → ℝ
  flatSecond_le :
    ∀ j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBLinearPrimeExpFreshLayer j r →
        (∫ omega,
          (trackBLinearPrimeExpScheduledFreshCoeff
            omega j (trackBLinearPrimeExpScheduleSpec.point j r) p) ^ 2 ∂mu) ≤
          flatSecond j r p
  flatSecond_budget :
    ∀ j, trackBLinearPrimeExpFlatLayerSecondMomentBudget flatSecond j ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Coefficient flatness inputs in reciprocal-mass upper-bound form.  Since
`E[c_p^2] = p^{-1} * supportMass(p)`, this is the natural deterministic target
for Markov flatness estimates. -/
structure TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperFacts where
  supportUpper : ℕ → ℕ → ℕ → ℝ
  support_mass_upper :
    ∀ j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBLinearPrimeExpFreshLayer j r →
        trackBLinearPrimeExpSupportReciprocalMass j r p ≤ supportUpper j r p
  supportUpper_budget :
    ∀ j, trackBLinearPrimeExpFlatLayerReciprocalMassUpperBudget supportUpper j ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Real-budget version of reciprocal-mass upper-bound flatness facts.  This is
the preferred form for deterministic analytic estimates before converting to
the `ENNReal` Markov budget. -/
structure TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperRealBudgetFacts where
  supportUpper : ℕ → ℕ → ℕ → ℝ
  supportUpper_nonneg : ∀ j r p, 0 ≤ supportUpper j r p
  support_mass_upper :
    ∀ j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBLinearPrimeExpFreshLayer j r →
        trackBLinearPrimeExpSupportReciprocalMass j r p ≤ supportUpper j r p
  supportUpper_real_budget :
    ∀ j, trackBLinearPrimeExpFlatLayerReciprocalMassUpperRealBudget supportUpper j ≤
      trackBLinearPrimeExpGeometryFlatBudgetReal j

/-- Coefficient flatness inputs using the trivial harmonic upper interval for
each coefficient support.  The only remaining field is the finite stage
budget. -/
structure TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperFacts where
  harmonicUpper_budget :
    ∀ j, trackBLinearPrimeExpFlatLayerHarmonicUpperBudget j ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Real-budget version of the trivial harmonic upper flatness facts. -/
structure TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperRealBudgetFacts where
  harmonicUpper_real_budget :
    ∀ j, trackBLinearPrimeExpFlatLayerHarmonicUpperRealBudget j ≤
      trackBLinearPrimeExpGeometryFlatBudgetReal j

/-- Generic real-valued layer-indexed coefficient-flatness probability facts.
Use this for analytic tail estimates that are not Markov/second-moment based:
prove a real bound for each one-coefficient bad event and a real finite-sum
budget, and Lean converts the result to the existing `ENNReal` layer package. -/
structure TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts where
  flatLayerFail : ℕ → ℕ → ℕ → ℝ
  flatLayerFail_nonneg :
    ∀ j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBLinearPrimeExpFreshLayer j r → 0 ≤ flatLayerFail j r p
  flat_layer_bad_le :
    ∀ j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBLinearPrimeExpFreshLayer j r →
        mu (trackBLinearPrimeExpFlatLayerBadSet j r p) ≤
          ENNReal.ofReal (flatLayerFail j r p)
  flat_layer_sum_real_le :
    ∀ j, trackBLinearPrimeExpFlatLayerRealProbabilityBudget flatLayerFail j ≤
      trackBLinearPrimeExpGeometryFlatBudgetReal j

/-- Event-witness version of the real-valued layer-indexed coefficient-flatness
tail package.  Use this when the analytic estimate naturally controls enlarged
bad events rather than the exact one-coefficient flatness failures. -/
structure TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts where
  flatLayerFail : ℕ → ℕ → ℕ → ℝ
  badFlat : ℕ → ℕ → ℕ → Set Omega
  flatLayerFail_nonneg :
    ∀ j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBLinearPrimeExpFreshLayer j r → 0 ≤ flatLayerFail j r p
  flat_bad_subset :
    ∀ j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBLinearPrimeExpFreshLayer j r →
        trackBLinearPrimeExpFlatLayerBadSet j r p ⊆ badFlat j r p
  flat_bad_event_real_le :
    ∀ j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBLinearPrimeExpFreshLayer j r →
        mu.real (badFlat j r p) ≤ flatLayerFail j r p
  flat_layer_sum_real_le :
    ∀ j, trackBLinearPrimeExpFlatLayerRealProbabilityBudget flatLayerFail j ≤
      trackBLinearPrimeExpGeometryFlatBudgetReal j

/-- Convert event-witness flatness tails to the exact real-probability
layer-flatness package. -/
def trackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts_of_event
    (h : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts) :
    TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts where
  flatLayerFail := h.flatLayerFail
  flatLayerFail_nonneg := h.flatLayerFail_nonneg
  flat_layer_bad_le := by
    intro j r p hr hp
    have hbad_ne_top : mu (h.badFlat j r p) ≠ ∞ := by
      exact ne_top_of_le_ne_top ENNReal.one_ne_top
        ((measure_mono (Set.subset_univ (h.badFlat j r p))).trans (by simp))
    have hbad :
        mu (h.badFlat j r p) ≤ ENNReal.ofReal (h.flatLayerFail j r p) := by
      rw [← ofReal_measureReal (μ := mu) (s := h.badFlat j r p) hbad_ne_top]
      exact ENNReal.ofReal_le_ofReal (h.flat_bad_event_real_le j r p hr hp)
    exact (measure_mono (h.flat_bad_subset j r p hr hp)).trans hbad
  flat_layer_sum_real_le := h.flat_layer_sum_real_le

/-- Real-valued layer flatness probabilities supply the existing `ENNReal`
layer-flatness package. -/
def trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_realProbability
    (h : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts where
  flatLayerFail := fun j r p => ENNReal.ofReal (h.flatLayerFail j r p)
  flat_layer_bad_le := h.flat_layer_bad_le
  flat_layer_sum_le := by
    intro j
    rw [trackBLinearPrimeExpFlatLayerRealProbabilityBudget_eq_ofReal
      h.flatLayerFail h.flatLayerFail_nonneg j]
    simpa [trackBLinearPrimeExpGeometryFlatBudget,
      trackBLinearPrimeExpGeometryFlatBudgetReal] using
      ENNReal.ofReal_le_ofReal (h.flat_layer_sum_real_le j)

/-- Event-witness real-valued layer flatness probabilities supply the existing
`ENNReal` layer-flatness package. -/
def trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_realProbabilityEvent
    (h : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts) :
    TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts :=
  trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_realProbability
    (trackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts_of_event h)

/-- A real-valued harmonic budget inequality supplies the `ENNReal` harmonic
upper facts. -/
def trackBLinearPrimeExpFlatGoodLayerHarmonicUpperFacts_of_realBudget
    (h : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperRealBudgetFacts) :
    TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperFacts where
  harmonicUpper_budget := by
    intro j
    rw [trackBLinearPrimeExpFlatLayerHarmonicUpperBudget_eq_ofReal j]
    simpa [trackBLinearPrimeExpGeometryFlatBudget,
      trackBLinearPrimeExpGeometryFlatBudgetReal] using
      ENNReal.ofReal_le_ofReal (h.harmonicUpper_real_budget j)

/-- A real-valued reciprocal-mass upper budget supplies the `ENNReal`
reciprocal-mass upper facts. -/
def trackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperFacts_of_realBudget
    (h : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperRealBudgetFacts) :
    TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperFacts where
  supportUpper := h.supportUpper
  support_mass_upper := h.support_mass_upper
  supportUpper_budget := by
    intro j
    rw [trackBLinearPrimeExpFlatLayerReciprocalMassUpperBudget_eq_ofReal
      h.supportUpper h.supportUpper_nonneg j]
    simpa [trackBLinearPrimeExpGeometryFlatBudget,
      trackBLinearPrimeExpGeometryFlatBudgetReal] using
      ENNReal.ofReal_le_ofReal (h.supportUpper_real_budget j)

/-- The trivial harmonic upper budget supplies reciprocal-mass upper facts. -/
def trackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperFacts_of_harmonicUpper
    (h : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperFacts) :
    TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperFacts where
  supportUpper := trackBLinearPrimeExpSupportHarmonicUpper
  support_mass_upper := by
    intro j r p _hr _hp
    exact trackBLinearPrimeExpSupportReciprocalMass_le_harmonicUpper j r p
  supportUpper_budget := by
    intro j
    simpa [trackBLinearPrimeExpFlatLayerHarmonicUpperBudget] using
      h.harmonicUpper_budget j

/-- Deterministic support-square-sum inputs for coefficient flatness.  This is
the paper-facing form of the Markov route: bound the explicit square weights
on each coefficient support, then check the finite stage budget. -/
structure TrackBLinearPrimeExpFlatGoodLayerSupportSecondMomentFacts where
  flatSecond : ℕ → ℕ → ℕ → ℝ
  supportSecond_le :
    ∀ j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBLinearPrimeExpFreshLayer j r →
        (∑ m ∈ trackBLinearPrimeExpLayerCoeffSupport j r p,
          ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2) ≤ flatSecond j r p
  flatSecond_budget :
    ∀ j, trackBLinearPrimeExpFlatLayerSecondMomentBudget flatSecond j ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Reciprocal-mass upper bounds imply the deterministic support-square-sum
flatness package. -/
def trackBLinearPrimeExpFlatGoodLayerSupportSecondMomentFacts_of_reciprocalMassUpper
    (h : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperFacts) :
    TrackBLinearPrimeExpFlatGoodLayerSupportSecondMomentFacts where
  flatSecond := fun j r p => (p : ℝ)⁻¹ * h.supportUpper j r p
  supportSecond_le := by
    intro j r p hr hp
    change trackBLinearPrimeExpLayerCoeffSecondMass j r p ≤
      (p : ℝ)⁻¹ * h.supportUpper j r p
    rw [trackBLinearPrimeExpLayerCoeffSecondMass_eq_prime_inv_mul_supportReciprocalMass hp]
    exact mul_le_mul_of_nonneg_left (h.support_mass_upper j r p hr hp)
      (inv_nonneg.mpr (by exact_mod_cast Nat.zero_le p))
  flatSecond_budget := by
    intro j
    simpa [trackBLinearPrimeExpFlatLayerSecondMomentBudget,
      trackBLinearPrimeExpFlatLayerReciprocalMassUpperBudget] using
      h.supportUpper_budget j

/-- Deterministic coefficient support-square-sum estimates imply the
coefficient second-moment flatness package. -/
def trackBLinearPrimeExpFlatGoodLayerSecondMomentFacts_of_supportSecond
    (h : TrackBLinearPrimeExpFlatGoodLayerSupportSecondMomentFacts) :
    TrackBLinearPrimeExpFlatGoodLayerSecondMomentFacts where
  flatSecond := h.flatSecond
  flatSecond_le := by
    intro j r p hr hp
    rw [integral_trackBLinearPrimeExpFlatLayerCoeff_sq_eq j r p hr]
    exact h.supportSecond_le j r p hr hp
  flatSecond_budget := h.flatSecond_budget

/-- Coefficient second-moment bounds imply the layer-indexed flatness
probability package by Markov's inequality. -/
def trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_secondMoment
    (h : TrackBLinearPrimeExpFlatGoodLayerSecondMomentFacts) :
    TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts where
  flatLayerFail := fun j r p =>
    ENNReal.ofReal
      (h.flatSecond j r p / (trackBLinearPrimeExpScheduleSpec.flat j) ^ 2)
  flat_layer_bad_le := by
    intro j r p hr hp
    exact measure_trackBLinearPrimeExpFlatLayerBadSet_le_second
      h.flatSecond j r p (h.flatSecond_le j r p hr hp)
  flat_layer_sum_le := by
    intro j
    simpa [trackBLinearPrimeExpFlatLayerSecondMomentBudget] using h.flatSecond_budget j

/-- Deterministic support-square-sum estimates imply the layer-indexed
flatness probability package. -/
def trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_supportSecond
    (h : TrackBLinearPrimeExpFlatGoodLayerSupportSecondMomentFacts) :
    TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts :=
  trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_secondMoment
    (trackBLinearPrimeExpFlatGoodLayerSecondMomentFacts_of_supportSecond h)

/-- Reciprocal-mass upper bounds imply the layer-indexed flatness probability
package. -/
def trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_reciprocalMassUpper
    (h : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperFacts) :
    TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts :=
  trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_supportSecond
    (trackBLinearPrimeExpFlatGoodLayerSupportSecondMomentFacts_of_reciprocalMassUpper h)

/-- Real-valued reciprocal-mass upper budgets imply the layer-indexed flatness
probability package. -/
def trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_reciprocalMassUpperRealBudget
    (h : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperRealBudgetFacts) :
    TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts :=
  trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_reciprocalMassUpper
    (trackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperFacts_of_realBudget h)

/-- The trivial harmonic upper budget implies the layer-indexed flatness
probability package. -/
def trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_harmonicUpper
    (h : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperFacts) :
    TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts :=
  trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_reciprocalMassUpper
    (trackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperFacts_of_harmonicUpper h)

/-- Real-valued harmonic upper budgets imply the layer-indexed flatness
probability package. -/
def trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_harmonicUpperRealBudget
    (h : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperRealBudgetFacts) :
    TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts :=
  trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_harmonicUpper
    (trackBLinearPrimeExpFlatGoodLayerHarmonicUpperFacts_of_realBudget h)

/-- Pointwise layer-bad estimates imply the concrete stage-summed probability
inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_pointwise
    (h : TrackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts where
  variance_layer_sum_le := by
    intro j
    exact le_trans
      (Finset.sum_le_sum (fun r hr => h.variance_layer_bad_le j r hr))
      (sum_trackBLinearPrimeExpGeometryVarianceLayerPointBudget_le j)
  flat_compl_le := h.flat_compl_le

/-- Analytic split of the concrete exponential geometry probability task.
The variance field is the layer small-ball estimate, and the flatness field is
the stage-wise complement estimate for coefficient flatness. -/
structure TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts where
  variance_small_ball :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      mu (trackBLinearPrimeExpVarianceLayerBadSet j r) ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r
  flatness_compl :
    ∀ j, mu (trackBLinearPrimeExpFlatGoodCompl j) ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Fully pointwise finite-union version of the small-ball/flatness interface.
The variance input is already layer-indexed; the flatness input is reduced to
one coefficient tail estimate plus a finite stage budget. -/
structure TrackBLinearPrimeExpGeometrySmallBallLayerFlatnessFacts where
  variance_small_ball :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      mu (trackBLinearPrimeExpVarianceLayerBadSet j r) ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r
  flatness_layer : TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts

/-- Pointwise coefficient flatness tails give the compact small-ball/flatness
package by a finite union bound. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_layerFlatness
    (h : TrackBLinearPrimeExpGeometrySmallBallLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts where
  variance_small_ball := h.variance_small_ball
  flatness_compl :=
    measure_trackBLinearPrimeExpFlatGood_compl_le_of_layerProbabilityFacts h.flatness_layer

/-- Lower-tail concentration input for the layer variance, separated from both
the deterministic mean lower bound and the flatness estimate.  This is the
right target for genuine small-ball or log-energy arguments that should not be
forced through Chebyshev. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationFacts where
  variance_concentration :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (trackBLinearPrimeExpVarianceLayerBadSet j r) ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r

/-- Product/rough-facing variant of the variance concentration input.  It lets
the analytic proof first union four `base^-14` bad events; Lean then converts
that bound to the pointwise `base^-12` budget. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationFourteenthFacts where
  variance_concentration_fourteenth :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (trackBLinearPrimeExpVarianceLayerBadSet j r) ≤
        ENNReal.ofReal (4 * ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹))

/-- Product/rough-facing four-bad-event form.  The analytic proof may name the
small-prime, rough-energy, error, and mass-compatibility bad events separately;
Lean then performs the union bound and converts their common `base^-14` budget
to the fourteenth concentration wrapper. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts where
  badSmall : ℕ → ℕ → Set Omega
  badRough : ℕ → ℕ → Set Omega
  badError : ℕ → ℕ → Set Omega
  badMass : ℕ → ℕ → Set Omega
  variance_bad_subset :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      trackBLinearPrimeExpVarianceLayerBadSet j r ⊆
        badSmall j r ∪ badRough j r ∪ badError j r ∪ badMass j r
  small_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badSmall j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  rough_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badRough j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  error_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badError j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  mass_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badMass j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)

/-- Analytic signal/error decomposition form for the variance lower-tail
contract.  It replaces the direct subset obligation in
`TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts` by two
finite-dimensional energy estimates: outside the small/rough/mass bad events
the signal energy is at least `4V`, and outside the error bad event the error
energy is at most one quarter of the signal energy.  Lean then uses the
deterministic L2 stability lemma to derive the variance-bad subset. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationEnergyDecompositionFacts where
  badSmall : ℕ → ℕ → Set Omega
  badRough : ℕ → ℕ → Set Omega
  badError : ℕ → ℕ → Set Omega
  badMass : ℕ → ℕ → Set Omega
  signalCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  errorCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  coeff_eq_signal_add_error :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p =
        signalCoeff omega j r p + errorCoeff omega j r p
  signal_energy_lower :
    ∀ omega j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      omega ∉ badSmall j r →
      omega ∉ badRough j r →
      omega ∉ badMass j r →
      4 * trackBLinearPrimeExpScheduleSpec.V j ≤
        ∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          signalCoeff omega j r p ^ 2
  error_energy_le :
    ∀ omega j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      omega ∉ badSmall j r →
      omega ∉ badRough j r →
      omega ∉ badError j r →
      omega ∉ badMass j r →
      4 * (∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          errorCoeff omega j r p ^ 2) ≤
        ∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          signalCoeff omega j r p ^ 2
  small_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badSmall j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  rough_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badRough j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  error_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badError j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  mass_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badMass j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)

/-- Common-floor form of the signal/error decomposition contract.  This is
suited to product/rough estimates where the analyst first proves a deterministic
floor, for example `smallFloor(j) * roughFloor(j,r)`, then shows it is below the
signal energy, above `4V`, and above four times the error energy on the relevant
good event. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationEnergyFloorFacts where
  badSmall : ℕ → ℕ → Set Omega
  badRough : ℕ → ℕ → Set Omega
  badError : ℕ → ℕ → Set Omega
  badMass : ℕ → ℕ → Set Omega
  signalCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  errorCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  energyFloor : ℕ → ℕ → ℝ
  coeff_eq_signal_add_error :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p =
        signalCoeff omega j r p + errorCoeff omega j r p
  signal_floor_le_energy :
    ∀ omega j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      omega ∉ badSmall j r →
      omega ∉ badRough j r →
      omega ∉ badMass j r →
      energyFloor j r ≤
        ∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          signalCoeff omega j r p ^ 2
  floor_ge_four_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      4 * trackBLinearPrimeExpScheduleSpec.V j ≤ energyFloor j r
  error_energy_le_floor :
    ∀ omega j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      omega ∉ badSmall j r →
      omega ∉ badRough j r →
      omega ∉ badError j r →
      omega ∉ badMass j r →
      4 * (∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          errorCoeff omega j r p ^ 2) ≤ energyFloor j r
  small_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badSmall j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  rough_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badRough j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  error_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badError j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  mass_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badMass j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)

/-- Product/rough floor form of the variance lower-tail contract.  This exposes
the analytic product `smallFloor(j) * roughFloor(j,r)` as the common energy
floor used by `TrackBLinearPrimeExpGeometryVarianceConcentrationEnergyFloorFacts`.
It matches the intended proof shape where one lower-tail estimate controls the
small-prime product, another controls the rough sampled energy, and a scalar
compatibility inequality turns their product into the `4V` signal floor. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughFloorFacts where
  badSmall : ℕ → ℕ → Set Omega
  badRough : ℕ → ℕ → Set Omega
  badError : ℕ → ℕ → Set Omega
  badMass : ℕ → ℕ → Set Omega
  signalCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  errorCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFloor : ℕ → ℝ
  roughFloor : ℕ → ℕ → ℝ
  coeff_eq_signal_add_error :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p =
        signalCoeff omega j r p + errorCoeff omega j r p
  product_floor_le_signal_energy :
    ∀ omega j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      omega ∉ badSmall j r →
      omega ∉ badRough j r →
      omega ∉ badMass j r →
      smallFloor j * roughFloor j r ≤
        ∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          signalCoeff omega j r p ^ 2
  product_floor_ge_four_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      4 * trackBLinearPrimeExpScheduleSpec.V j ≤ smallFloor j * roughFloor j r
  error_energy_le_product_floor :
    ∀ omega j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      omega ∉ badSmall j r →
      omega ∉ badRough j r →
      omega ∉ badError j r →
      omega ∉ badMass j r →
      4 * (∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          errorCoeff omega j r p ^ 2) ≤ smallFloor j * roughFloor j r
  small_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badSmall j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  rough_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badRough j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  error_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badError j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  mass_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badMass j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)

/-- Product/rough signal-factor form.  This exposes the common analytic step
behind the product floor: on the good event the signal coefficients factor as a
small-prime factor times rough coefficients, with separate lower bounds for the
small factor and rough sampled energy. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSignalFacts where
  badSmall : ℕ → ℕ → Set Omega
  badRough : ℕ → ℕ → Set Omega
  badError : ℕ → ℕ → Set Omega
  badMass : ℕ → ℕ → Set Omega
  signalCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  errorCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFactor : Omega → ℕ → ℝ
  roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFloor : ℕ → ℝ
  roughFloor : ℕ → ℕ → ℝ
  coeff_eq_signal_add_error :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p =
        signalCoeff omega j r p + errorCoeff omega j r p
  signal_eq_small_mul_rough :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      signalCoeff omega j r p = smallFactor omega j * roughCoeff omega j r p
  smallFloor_nonneg : ∀ j, 0 ≤ smallFloor j
  small_floor_le_sq :
    ∀ omega j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      omega ∉ badSmall j r →
      omega ∉ badMass j r →
      smallFloor j ≤ smallFactor omega j ^ 2
  rough_floor_le_energy :
    ∀ omega j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      omega ∉ badRough j r →
      omega ∉ badMass j r →
      roughFloor j r ≤
        ∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          roughCoeff omega j r p ^ 2
  product_floor_ge_four_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      4 * trackBLinearPrimeExpScheduleSpec.V j ≤ smallFloor j * roughFloor j r
  error_energy_le_product_floor :
    ∀ omega j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      omega ∉ badSmall j r →
      omega ∉ badRough j r →
      omega ∉ badError j r →
      omega ∉ badMass j r →
      4 * (∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          errorCoeff omega j r p ^ 2) ≤ smallFloor j * roughFloor j r
  small_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badSmall j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  rough_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badRough j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  error_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badError j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  mass_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badMass j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)

/-- Threshold-bad-event product/rough signal form.  The small, rough, and error
bad events are the canonical lower-tail or error-threshold sets, so Lean derives
the outside-good inequalities by `not_lt`.  The mass/boundary bad event remains
explicit because its convenient analytic definition may depend on support-bulk
or boundary choices. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdFacts where
  badMass : ℕ → ℕ → Set Omega
  signalCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  errorCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFactor : Omega → ℕ → ℝ
  roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFloor : ℕ → ℝ
  roughFloor : ℕ → ℕ → ℝ
  coeff_eq_signal_add_error :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p =
        signalCoeff omega j r p + errorCoeff omega j r p
  signal_eq_small_mul_rough :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      signalCoeff omega j r p = smallFactor omega j * roughCoeff omega j r p
  smallFloor_nonneg : ∀ j, 0 ≤ smallFloor j
  product_floor_ge_four_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      4 * trackBLinearPrimeExpScheduleSpec.V j ≤ smallFloor j * roughFloor j r
  small_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu {omega | smallFactor omega j ^ 2 < smallFloor j} ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  rough_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu {omega |
          (∑ p ∈ trackBFreshPrimeLayer
            (trackBLinearPrimeExpScheduleSpec.freshLo j r)
            (trackBLinearPrimeExpScheduleSpec.freshHi j r),
            roughCoeff omega j r p ^ 2) < roughFloor j r} ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  error_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu {omega |
          smallFloor j * roughFloor j r <
            4 * (∑ p ∈ trackBFreshPrimeLayer
              (trackBLinearPrimeExpScheduleSpec.freshLo j r)
              (trackBLinearPrimeExpScheduleSpec.freshHi j r),
              errorCoeff omega j r p ^ 2)} ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
  mass_bad_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (badMass j r) ≤
        ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)

/-- Convert a real probability estimate under the ambient fair-coin probability
measure into the corresponding `ENNReal.ofReal` estimate. -/
theorem trackBLinearPrimeExp_measure_le_of_real_le {s : Set Omega} {a : ℝ}
    (h : mu.real s ≤ a) :
    mu s ≤ ENNReal.ofReal a := by
  have hs_ne_top : mu s ≠ ∞ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      ((measure_mono (Set.subset_univ s)).trans (by simp))
  rw [← ENNReal.ofReal_toReal hs_ne_top]
  exact ENNReal.ofReal_le_ofReal (by simpa using h)

/-- Real-probability version of the threshold product/rough signal package.
Use this when the analytic estimates are stated as ordinary real probability
bounds for the canonical threshold events. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdRealFacts where
  badMass : ℕ → ℕ → Set Omega
  signalCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  errorCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFactor : Omega → ℕ → ℝ
  roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFloor : ℕ → ℝ
  roughFloor : ℕ → ℕ → ℝ
  coeff_eq_signal_add_error :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p =
        signalCoeff omega j r p + errorCoeff omega j r p
  signal_eq_small_mul_rough :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      signalCoeff omega j r p = smallFactor omega j * roughCoeff omega j r p
  smallFloor_nonneg : ∀ j, 0 ≤ smallFloor j
  product_floor_ge_four_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      4 * trackBLinearPrimeExpScheduleSpec.V j ≤ smallFloor j * roughFloor j r
  small_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real {omega | smallFactor omega j ^ 2 < smallFloor j} ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹
  rough_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real {omega |
          (∑ p ∈ trackBFreshPrimeLayer
            (trackBLinearPrimeExpScheduleSpec.freshLo j r)
            (trackBLinearPrimeExpScheduleSpec.freshHi j r),
            roughCoeff omega j r p ^ 2) < roughFloor j r} ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹
  error_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real {omega |
          smallFloor j * roughFloor j r <
            4 * (∑ p ∈ trackBFreshPrimeLayer
              (trackBLinearPrimeExpScheduleSpec.freshLo j r)
              (trackBLinearPrimeExpScheduleSpec.freshHi j r),
              errorCoeff omega j r p ^ 2)} ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹
  mass_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real (badMass j r) ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹

/-- Real-probability product/rough package with a separate error-energy budget.
Use this when the analytic estimate is naturally stated as
`P(errorBudget < errorEnergy) <= base^-14` and the comparison
`4 * errorBudget <= smallFloor * roughFloor` is a deterministic scalar check. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughErrorBudgetRealFacts where
  badMass : ℕ → ℕ → Set Omega
  signalCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  errorCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFactor : Omega → ℕ → ℝ
  roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFloor : ℕ → ℝ
  roughFloor : ℕ → ℕ → ℝ
  errorBudget : ℕ → ℕ → ℝ
  coeff_eq_signal_add_error :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p =
        signalCoeff omega j r p + errorCoeff omega j r p
  signal_eq_small_mul_rough :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      signalCoeff omega j r p = smallFactor omega j * roughCoeff omega j r p
  smallFloor_nonneg : ∀ j, 0 ≤ smallFloor j
  product_floor_ge_four_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      4 * trackBLinearPrimeExpScheduleSpec.V j ≤ smallFloor j * roughFloor j r
  error_budget_le_product_floor :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      4 * errorBudget j r ≤ smallFloor j * roughFloor j r
  small_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real {omega | smallFactor omega j ^ 2 < smallFloor j} ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹
  rough_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real {omega |
          (∑ p ∈ trackBFreshPrimeLayer
            (trackBLinearPrimeExpScheduleSpec.freshLo j r)
            (trackBLinearPrimeExpScheduleSpec.freshHi j r),
            roughCoeff omega j r p ^ 2) < roughFloor j r} ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹
  error_budget_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real {omega |
          errorBudget j r <
            ∑ p ∈ trackBFreshPrimeLayer
              (trackBLinearPrimeExpScheduleSpec.freshLo j r)
              (trackBLinearPrimeExpScheduleSpec.freshHi j r),
              errorCoeff omega j r p ^ 2} ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹
  mass_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real (badMass j r) ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹

/-- Real-probability product/rough package with the canonical error budget
`errorBudget(j,r) = V_j`.  This is the shortest interface when the boundary or
Rankin estimate naturally proves `P(V_j < errorEnergy) <= base^-14`; the
product-floor scalar check `4V_j <= smallFloor * roughFloor` supplies the
quarter-error comparison. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts where
  badMass : ℕ → ℕ → Set Omega
  signalCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  errorCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFactor : Omega → ℕ → ℝ
  roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFloor : ℕ → ℝ
  roughFloor : ℕ → ℕ → ℝ
  coeff_eq_signal_add_error :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p =
        signalCoeff omega j r p + errorCoeff omega j r p
  signal_eq_small_mul_rough :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      signalCoeff omega j r p = smallFactor omega j * roughCoeff omega j r p
  smallFloor_nonneg : ∀ j, 0 ≤ smallFloor j
  product_floor_ge_four_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      4 * trackBLinearPrimeExpScheduleSpec.V j ≤ smallFloor j * roughFloor j r
  small_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real {omega | smallFactor omega j ^ 2 < smallFloor j} ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹
  rough_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real {omega |
          (∑ p ∈ trackBFreshPrimeLayer
            (trackBLinearPrimeExpScheduleSpec.freshLo j r)
            (trackBLinearPrimeExpScheduleSpec.freshHi j r),
            roughCoeff omega j r p ^ 2) < roughFloor j r} ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹
  error_V_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real {omega |
          trackBLinearPrimeExpScheduleSpec.V j <
            ∑ p ∈ trackBFreshPrimeLayer
              (trackBLinearPrimeExpScheduleSpec.freshLo j r)
              (trackBLinearPrimeExpScheduleSpec.freshHi j r),
              errorCoeff omega j r p ^ 2} ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹
  mass_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real (badMass j r) ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹

/-- Deterministic and algebraic data for the product/rough lower-tail package
with the canonical `V_j` error budget.  The probabilistic estimates are split
into separate records below so the analytic proof can close them independently. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts where
  badMass : ℕ → ℕ → Set Omega
  signalCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  errorCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFactor : Omega → ℕ → ℝ
  roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFloor : ℕ → ℝ
  roughFloor : ℕ → ℕ → ℝ
  coeff_eq_signal_add_error :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p =
        signalCoeff omega j r p + errorCoeff omega j r p
  signal_eq_small_mul_rough :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      signalCoeff omega j r p = smallFactor omega j * roughCoeff omega j r p
  smallFloor_nonneg : ∀ j, 0 ≤ smallFloor j
  product_floor_ge_four_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      4 * trackBLinearPrimeExpScheduleSpec.V j ≤ smallFloor j * roughFloor j r

/-- Product/rough deterministic core with the first-pass floor normalization
fixed to `trackBLinearPrimeExpProductRoughSmallFloor` and
`trackBLinearPrimeExpProductRoughRoughFloor`.  This is the smaller analytic
record to target once the coefficient decomposition has been chosen; Lean fills
the floor nonnegativity and `4V` scalar checks. -/
structure TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts where
  badMass : ℕ → ℕ → Set Omega
  signalCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  errorCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFactor : Omega → ℕ → ℝ
  roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  coeff_eq_signal_add_error :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p =
        signalCoeff omega j r p + errorCoeff omega j r p
  signal_eq_small_mul_rough :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      signalCoeff omega j r p = smallFactor omega j * roughCoeff omega j r p

/-- Fixed-floor product/rough core for the common case where the decomposition
has no random mass/boundary bad event. -/
structure TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts where
  signalCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  errorCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  smallFactor : Omega → ℕ → ℝ
  roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ
  coeff_eq_signal_add_error :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          omega j (trackBLinearPrimeExpScheduleSpec.point j r) p =
        signalCoeff omega j r p + errorCoeff omega j r p
  signal_eq_small_mul_rough :
    ∀ omega j r p, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r) →
      signalCoeff omega j r p = smallFactor omega j * roughCoeff omega j r p

/-- Build the no-mass fixed-floor core from a chosen small factor and rough
coefficient family.  Lean defines the signal as `smallFactor * roughCoeff` and
the error as the residual from the scheduled fresh-prime coefficient, so the
two algebra fields are closed definitionally. -/
def trackBLinearPrimeExpNoMassCoreFacts_of_smallRough
    (smallFactor : Omega → ℕ → ℝ)
    (roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ) :
    TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts where
  signalCoeff := fun omega j r p => smallFactor omega j * roughCoeff omega j r p
  errorCoeff := fun omega j r p =>
    trackBLinearPrimeScheduledFreshCoeff
        trackBLinearPrimeExpScheduleSpec.Q
        trackBLinearPrimeExpScheduleSpec.point
        trackBLinearPrimeExpScheduleSpec.freshLo
        trackBLinearPrimeExpScheduleSpec.freshHi
        omega j (trackBLinearPrimeExpScheduleSpec.point j r) p -
      smallFactor omega j * roughCoeff omega j r p
  smallFactor := smallFactor
  roughCoeff := roughCoeff
  coeff_eq_signal_add_error := by
    intro omega j r p _hr _hp
    simp
  signal_eq_small_mul_rough := by
    intro omega j r p _hr _hp
    rfl

/-- Convert the no-mass fixed-floor core to the fixed-floor core by setting
`badMass = ∅`. -/
def trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass
    (h : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts) :
    TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts where
  badMass := fun _ _ => ∅
  signalCoeff := h.signalCoeff
  errorCoeff := h.errorCoeff
  smallFactor := h.smallFactor
  roughCoeff := h.roughCoeff
  coeff_eq_signal_add_error := h.coeff_eq_signal_add_error
  signal_eq_small_mul_rough := h.signal_eq_small_mul_rough

/-- Convert the fixed-floor product/rough core to the existing general
product/rough core record. -/
def trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor
    (h : TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts where
  badMass := h.badMass
  signalCoeff := h.signalCoeff
  errorCoeff := h.errorCoeff
  smallFactor := h.smallFactor
  roughCoeff := h.roughCoeff
  smallFloor := trackBLinearPrimeExpProductRoughSmallFloor
  roughFloor := trackBLinearPrimeExpProductRoughRoughFloor
  coeff_eq_signal_add_error := h.coeff_eq_signal_add_error
  signal_eq_small_mul_rough := h.signal_eq_small_mul_rough
  smallFloor_nonneg := trackBLinearPrimeExpProductRoughSmallFloor_nonneg
  product_floor_ge_four_V := by
    intro j r hr _hmean
    exact trackBLinearPrimeExp_productRoughFloor_ge_four_V j r hr

/-- Convert the no-mass fixed-floor core directly to the product/rough core
consumed by Packet C probability records. -/
def trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass
    (h : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts :=
  trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor
    (trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass h)

/-- The `base^-14` Packet C probability budget is nonnegative. -/
theorem trackBLinearPrimeExp_productRoughTailBudget_nonneg (j : ℕ) :
    0 ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹ := by
  have hbase_nonneg : (0 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
    exact_mod_cast Nat.zero_le (trackBLinearPrimeConcreteBase j)
  exact inv_nonneg.mpr (pow_nonneg hbase_nonneg 14)

/-- Small-prime product lower-tail estimate for a fixed product/rough core. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts
    (core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts) where
  small_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real {omega | core.smallFactor omega j ^ 2 < core.smallFloor j} ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹

/-- Rough sampled-energy lower-tail estimate for a fixed product/rough core. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts
    (core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts) where
  rough_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real {omega |
          (∑ p ∈ trackBFreshPrimeLayer
            (trackBLinearPrimeExpScheduleSpec.freshLo j r)
            (trackBLinearPrimeExpScheduleSpec.freshHi j r),
            core.roughCoeff omega j r p ^ 2) < core.roughFloor j r} ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹

/-- Boundary or Rankin error-energy lower-tail estimate for a fixed
product/rough core, in the specialized `V_j` form. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts
    (core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts) where
  error_V_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real {omega |
          trackBLinearPrimeExpScheduleSpec.V j <
            ∑ p ∈ trackBFreshPrimeLayer
              (trackBLinearPrimeExpScheduleSpec.freshLo j r)
              (trackBLinearPrimeExpScheduleSpec.freshHi j r),
              core.errorCoeff omega j r p ^ 2} ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹

/-- Boundary/mass bad-event estimate for a fixed product/rough core. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts
    (core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts) where
  mass_bad_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real (core.badMass j r) ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹

/-- A pointwise small-factor floor makes the small-product tail event empty. -/
def trackBLinearPrimeExpSmallTailRealFacts_of_pointwise
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (hsmall : ∀ omega j, core.smallFloor j ≤ core.smallFactor omega j ^ 2) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts core where
  small_bad_real_le := by
    intro j r _hr _hmean
    have hset : {omega | core.smallFactor omega j ^ 2 < core.smallFloor j} = ∅ := by
      ext omega
      simp [not_lt_of_ge (hsmall omega j)]
    simp [hset, trackBLinearPrimeExp_productRoughTailBudget_nonneg j]

/-- A pointwise rough-energy floor makes the rough lower-tail event empty. -/
def trackBLinearPrimeExpRoughTailRealFacts_of_pointwise
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (hrough :
      ∀ omega j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
        core.roughFloor j r ≤
          ∑ p ∈ trackBFreshPrimeLayer
            (trackBLinearPrimeExpScheduleSpec.freshLo j r)
            (trackBLinearPrimeExpScheduleSpec.freshHi j r),
            core.roughCoeff omega j r p ^ 2) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts core where
  rough_bad_real_le := by
    intro j r hr _hmean
    have hset :
        {omega |
          (∑ p ∈ trackBFreshPrimeLayer
            (trackBLinearPrimeExpScheduleSpec.freshLo j r)
            (trackBLinearPrimeExpScheduleSpec.freshHi j r),
            core.roughCoeff omega j r p ^ 2) < core.roughFloor j r} = ∅ := by
      ext omega
      simp [not_lt_of_ge (hrough omega j r hr)]
    simp [hset, trackBLinearPrimeExp_productRoughTailBudget_nonneg j]

/-- A pointwise error-energy upper bound makes the `V_j` error event empty. -/
def trackBLinearPrimeExpVErrorTailRealFacts_of_pointwise
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (herror :
      ∀ omega j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
        (∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          core.errorCoeff omega j r p ^ 2) ≤ trackBLinearPrimeExpScheduleSpec.V j) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts core where
  error_V_bad_real_le := by
    intro j r hr _hmean
    have hset :
        {omega |
          trackBLinearPrimeExpScheduleSpec.V j <
            ∑ p ∈ trackBFreshPrimeLayer
              (trackBLinearPrimeExpScheduleSpec.freshLo j r)
              (trackBLinearPrimeExpScheduleSpec.freshHi j r),
              core.errorCoeff omega j r p ^ 2} = ∅ := by
      ext omega
      simp [not_lt_of_ge (herror omega j r hr)]
    simp [hset, trackBLinearPrimeExp_productRoughTailBudget_nonneg j]

/-- If the product/rough core has no random mass bad event, the canonical
mass-tail record is automatic. -/
def trackBLinearPrimeExpProductRoughMassTailRealFacts_of_empty
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (hbad : ∀ j r, core.badMass j r = ∅) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts core where
  mass_bad_real_le := by
    intro j r _hr _hmean
    have hbase_nonneg : (0 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
      exact_mod_cast Nat.zero_le (trackBLinearPrimeConcreteBase j)
    have hnonneg : 0 ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹ := by
      exact inv_nonneg.mpr (pow_nonneg hbase_nonneg 14)
    simp [hbad j r, hnonneg]

/-- Fixed-floor convenience form of the empty-mass canonical-tail adapter. -/
def trackBLinearPrimeExpFixedFloorMassTailRealFacts_of_empty
    (fixedCore : TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts)
    (hbad : ∀ j r, fixedCore.badMass j r = ∅) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts
      (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore) :=
  trackBLinearPrimeExpProductRoughMassTailRealFacts_of_empty
    (core := trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore)
    (by
      intro j r
      simpa [trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor] using
        hbad j r)

/-- Event-witness version of the small-prime product lower-tail estimate.  The
analytic proof may bound any convenient bad event containing the canonical
threshold failure. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
    (core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts) where
  badSmall : ℕ → ℕ → Set Omega
  small_bad_subset :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      {omega | core.smallFactor omega j ^ 2 < core.smallFloor j} ⊆ badSmall j r
  small_bad_event_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real (badSmall j r) ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹

/-- Event-witness version of the rough sampled-energy lower-tail estimate. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
    (core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts) where
  badRough : ℕ → ℕ → Set Omega
  rough_bad_subset :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      {omega |
          (∑ p ∈ trackBFreshPrimeLayer
            (trackBLinearPrimeExpScheduleSpec.freshLo j r)
            (trackBLinearPrimeExpScheduleSpec.freshHi j r),
            core.roughCoeff omega j r p ^ 2) < core.roughFloor j r} ⊆ badRough j r
  rough_bad_event_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real (badRough j r) ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹

/-- Event-witness version of the specialized `V_j` error-energy estimate. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
    (core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts) where
  badError : ℕ → ℕ → Set Omega
  error_V_bad_subset :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      {omega |
          trackBLinearPrimeExpScheduleSpec.V j <
            ∑ p ∈ trackBFreshPrimeLayer
              (trackBLinearPrimeExpScheduleSpec.freshLo j r)
              (trackBLinearPrimeExpScheduleSpec.freshHi j r),
              core.errorCoeff omega j r p ^ 2} ⊆ badError j r
  error_V_bad_event_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real (badError j r) ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹

/-- Event-witness version of the mass/boundary bad-event estimate. -/
structure TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts
    (core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts) where
  badMass : ℕ → ℕ → Set Omega
  mass_bad_subset :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      core.badMass j r ⊆ badMass j r
  mass_bad_event_real_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu.real (badMass j r) ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹

/-- Event-witness small-tail record from the canonical small-product probability
bound.  This is the direct Packet C adapter for analytic estimates whose bad
event is exactly `smallFactor^2 < smallFloor`; the event is independent of the
mesh index `r`. -/
def trackBLinearPrimeExpSmallTailEventRealFacts_of_canonical
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (hsmall :
      ∀ j,
        mu.real {omega | core.smallFactor omega j ^ 2 < core.smallFloor j} ≤
          (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      core where
  badSmall := fun j _r => {omega | core.smallFactor omega j ^ 2 < core.smallFloor j}
  small_bad_subset := by
    intro _j _r _hr _hmean omega homega
    exact homega
  small_bad_event_real_le := by
    intro j _r _hr _hmean
    exact hsmall j

/-- Event-witness small-tail record from a weighted Rademacher log-product
lower-tail reduction.  Analytic work should supply the finite prime set,
weights, threshold, containment of the canonical small-product bad event, and
the scalar Hoeffding exponent check. -/
def trackBLinearPrimeExpSmallTailEventRealFacts_of_weightedLogTail
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (primeSet : ℕ → Finset ℕ) (weight : ℕ → ℕ → ℝ) (threshold : ℕ → ℝ)
    (threshold_nonneg : ∀ j, 0 ≤ threshold j)
    (small_bad_subset :
      ∀ j,
        {omega | core.smallFactor omega j ^ 2 < core.smallFloor j} ⊆
          {omega |
            threshold j ≤ ∑ q ∈ primeSet j, (-(weight j q) * eps omega q)})
    (hoeffding_exponent :
      ∀ j,
        ((81 : ℝ) / 5) * Real.log (trackBLinearPrimeConcreteBase j : ℝ) ≤
          threshold j ^ 2 / (2 * (∑ q ∈ primeSet j, weight j q ^ 2))) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      core :=
  trackBLinearPrimeExpSmallTailEventRealFacts_of_canonical
    (core := core)
    (by
      intro j
      have hb : (1 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
        exact_mod_cast (trackBLinearPrimeConcreteBase_one_lt j).le
      exact
        measure_event_le_inv_pow_fourteen_of_subset_weighted_eps_neg_sum_ge
          (bad := {omega | core.smallFactor omega j ^ 2 < core.smallFloor j})
          (primeSet j) (weight j) (threshold_nonneg j) hb
          (small_bad_subset j) (hoeffding_exponent j))

/-- Specialized small-product adapter for the current Packet C constants.  The
analytic proof supplies the log-product containment at threshold
`(9/5) * 100 * log(base)` and the deterministic variance proxy
`sum weights^2 <= 10 * 100 * log(base)`; Lean derives the Hoeffding exponent
and packages the small-tail event record. -/
def trackBLinearPrimeExpSmallTailEventRealFacts_of_weightedLogTailVarianceProxy
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (primeSet : ℕ → Finset ℕ) (weight : ℕ → ℕ → ℝ)
    (small_bad_subset :
      ∀ j,
        {omega | core.smallFactor omega j ^ 2 < core.smallFloor j} ⊆
          {omega |
            ((9 : ℝ) / 5) * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ) ≤
              ∑ q ∈ primeSet j, (-(weight j q) * eps omega q)})
    (variance_pos :
      ∀ j, 0 < ∑ q ∈ primeSet j, weight j q ^ 2)
    (variance_le :
      ∀ j,
        (∑ q ∈ primeSet j, weight j q ^ 2) ≤
          10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      core :=
  trackBLinearPrimeExpSmallTailEventRealFacts_of_weightedLogTail
    (core := core) primeSet weight
    (fun j => ((9 : ℝ) / 5) * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
    (by
      intro j
      have hb : (1 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
        exact_mod_cast (trackBLinearPrimeConcreteBase_one_lt j).le
      have hlog : 0 ≤ Real.log (trackBLinearPrimeConcreteBase j : ℝ) :=
        Real.log_nonneg hb
      nlinarith)
    small_bad_subset
    (by
      intro j
      have hb : (1 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
        exact_mod_cast (trackBLinearPrimeConcreteBase_one_lt j).le
      exact smallProductHoeffdingExponent_log_ge_of_variance_proxy hb
        (variance_pos j) (variance_le j))

/-- Small-product adapter from a pointwise log-product decomposition and the
current Packet C variance proxy.  This removes the manual event-containment
step from future analytic instantiations. -/
def trackBLinearPrimeExpSmallTailEventRealFacts_of_logDecompositionVarianceProxy
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (primeSet : ℕ → Finset ℕ) (weight : ℕ → ℕ → ℝ) (mean : ℕ → ℝ)
    (small_sq_pos : ∀ omega j, 0 < core.smallFactor omega j ^ 2)
    (log_decomposition :
      ∀ omega j,
        Real.log (core.smallFactor omega j ^ 2) =
          mean j + ∑ q ∈ primeSet j, eps omega q * weight j q)
    (log_floor_bound :
      ∀ j,
        Real.log (core.smallFloor j) ≤
          mean j - ((9 : ℝ) / 5) * 100 *
            Real.log (trackBLinearPrimeConcreteBase j : ℝ))
    (variance_pos :
      ∀ j, 0 < ∑ q ∈ primeSet j, weight j q ^ 2)
    (variance_le :
      ∀ j,
        (∑ q ∈ primeSet j, weight j q ^ 2) ≤
          10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      core :=
  trackBLinearPrimeExpSmallTailEventRealFacts_of_weightedLogTailVarianceProxy
    (core := core) primeSet weight
    (by
      intro j
      exact
        smallProduct_bad_subset_weighted_eps_neg_sum_of_log_decomposition
          (X := fun omega => core.smallFactor omega j ^ 2)
          (floor := core.smallFloor j)
          (mean := mean j)
          (threshold :=
            ((9 : ℝ) / 5) * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
          (s := primeSet j)
          (weight := weight j)
          (fun omega => small_sq_pos omega j)
          (fun omega => log_decomposition omega j)
          (log_floor_bound j))
    variance_pos variance_le

/-- Small-product adapter from the exact paper-side inputs: log decomposition,
mean lower bound, floor log bound, and variance proxy. -/
def trackBLinearPrimeExpSmallTailEventRealFacts_of_logDecompositionMeanVarianceProxy
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (primeSet : ℕ → Finset ℕ) (weight : ℕ → ℕ → ℝ) (mean : ℕ → ℝ)
    (small_sq_pos : ∀ omega j, 0 < core.smallFactor omega j ^ 2)
    (log_decomposition :
      ∀ omega j,
        Real.log (core.smallFactor omega j ^ 2) =
          mean j + ∑ q ∈ primeSet j, eps omega q * weight j q)
    (mean_lower :
      ∀ j,
        -(((11 : ℝ) / 5) * 100 *
            Real.log (trackBLinearPrimeConcreteBase j : ℝ)) ≤ mean j)
    (small_floor_log_le :
      ∀ j,
        Real.log (core.smallFloor j) ≤
          -(4 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)))
    (variance_pos :
      ∀ j, 0 < ∑ q ∈ primeSet j, weight j q ^ 2)
    (variance_le :
      ∀ j,
        (∑ q ∈ primeSet j, weight j q ^ 2) ≤
          10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      core :=
  trackBLinearPrimeExpSmallTailEventRealFacts_of_logDecompositionVarianceProxy
    (core := core) primeSet weight mean small_sq_pos log_decomposition
    (by
      intro j
      exact smallProduct_log_floor_bound_of_mean_lower (mean_lower j)
        (small_floor_log_le j))
    variance_pos variance_le

/-- Fixed-floor version of the log-decomposition/mean/variance small-product
adapter.  The fixed floor `base^(-4K)` supplies the floor-log bound
automatically. -/
def trackBLinearPrimeExpFixedFloorSmallTailEventRealFacts_of_logDecompositionMeanVarianceProxy
    (fixedCore : TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts)
    (primeSet : ℕ → Finset ℕ) (weight : ℕ → ℕ → ℝ) (mean : ℕ → ℝ)
    (small_sq_pos : ∀ omega j, 0 < fixedCore.smallFactor omega j ^ 2)
    (log_decomposition :
      ∀ omega j,
        Real.log (fixedCore.smallFactor omega j ^ 2) =
          mean j + ∑ q ∈ primeSet j, eps omega q * weight j q)
    (mean_lower :
      ∀ j,
        -(((11 : ℝ) / 5) * 100 *
            Real.log (trackBLinearPrimeConcreteBase j : ℝ)) ≤ mean j)
    (variance_pos :
      ∀ j, 0 < ∑ q ∈ primeSet j, weight j q ^ 2)
    (variance_le :
      ∀ j,
        (∑ q ∈ primeSet j, weight j q ^ 2) ≤
          10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore) :=
  trackBLinearPrimeExpSmallTailEventRealFacts_of_logDecompositionMeanVarianceProxy
    (core := trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore)
    primeSet weight mean
    (by
      intro omega j
      simpa [trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor] using
        small_sq_pos omega j)
    (by
      intro omega j
      simpa [trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor] using
        log_decomposition omega j)
    mean_lower
    (by
      intro j
      simpa [trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor] using
        trackBLinearPrimeExpProductRoughSmallFloor_log_le j)
    variance_pos variance_le

/-- No-mass fixed-floor version of the log-decomposition/mean/variance
small-product adapter for the shortest Packet B route. -/
def trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_logDecompositionMeanVarianceProxy
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (primeSet : ℕ → Finset ℕ) (weight : ℕ → ℕ → ℝ) (mean : ℕ → ℝ)
    (small_sq_pos : ∀ omega j, 0 < core.smallFactor omega j ^ 2)
    (log_decomposition :
      ∀ omega j,
        Real.log (core.smallFactor omega j ^ 2) =
          mean j + ∑ q ∈ primeSet j, eps omega q * weight j q)
    (mean_lower :
      ∀ j,
        -(((11 : ℝ) / 5) * 100 *
            Real.log (trackBLinearPrimeConcreteBase j : ℝ)) ≤ mean j)
    (variance_pos :
      ∀ j, 0 < ∑ q ∈ primeSet j, weight j q ^ 2)
    (variance_le :
      ∀ j,
        (∑ q ∈ primeSet j, weight j q ^ 2) ≤
          10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpFixedFloorSmallTailEventRealFacts_of_logDecompositionMeanVarianceProxy
    (trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass core)
    primeSet weight mean
    (by
      intro omega j
      simpa [trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass] using small_sq_pos omega j)
    (by
      intro omega j
      simpa [trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass] using
        log_decomposition omega j)
    mean_lower variance_pos variance_le

/-- No-mass small-tail adapter for a finite Euler-product small factor.  This
closes product positivity and the finite log-product decomposition from the
pointwise identity
`smallFactor = prod_q (1 + eps_q * x_q)`.  The remaining analytic inputs are
the mean lower bound and variance proxy for the displayed finite prime set. -/
def trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_finiteEulerProduct
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (primeSet : ℕ → Finset ℕ) (x : ℕ → ℕ → ℝ)
    (smallFactor_eq :
      ∀ omega j,
        core.smallFactor omega j =
          ∏ q ∈ primeSet j, (1 + eps omega q * x j q))
    (x_pos : ∀ j q, q ∈ primeSet j → 0 < x j q)
    (x_lt_one : ∀ j q, q ∈ primeSet j → x j q < 1)
    (mean_lower :
      ∀ j,
        -(((11 : ℝ) / 5) * 100 *
            Real.log (trackBLinearPrimeConcreteBase j : ℝ)) ≤
          ∑ q ∈ primeSet j, Real.log (1 - x j q ^ 2))
    (variance_pos :
      ∀ j, 0 < ∑ q ∈ primeSet j,
        Real.log ((1 + x j q) / (1 - x j q)) ^ 2)
    (variance_le :
      ∀ j,
        (∑ q ∈ primeSet j, Real.log ((1 + x j q) / (1 - x j q)) ^ 2) ≤
          10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_logDecompositionMeanVarianceProxy
    core primeSet
    (fun j q => Real.log ((1 + x j q) / (1 - x j q)))
    (fun j => ∑ q ∈ primeSet j, Real.log (1 - x j q ^ 2))
    (by
      intro omega j
      rw [smallFactor_eq omega j]
      exact smallProduct_prod_sq_pos_eps omega (primeSet j) (x j)
        (fun q hq => x_pos j q hq) (fun q hq => x_lt_one j q hq))
    (by
      intro omega j
      rw [smallFactor_eq omega j]
      exact smallProduct_log_prod_decomposition_eps omega (primeSet j) (x j)
        (fun q hq => x_pos j q hq) (fun q hq => x_lt_one j q hq))
    mean_lower variance_pos variance_le

/-- No-mass finite Euler-product small-tail adapter where variance positivity
is supplied by nonemptiness of the finite small-prime set. -/
def trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_finiteEulerProductNonempty
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (primeSet : ℕ → Finset ℕ) (x : ℕ → ℕ → ℝ)
    (smallFactor_eq :
      ∀ omega j,
        core.smallFactor omega j =
          ∏ q ∈ primeSet j, (1 + eps omega q * x j q))
    (x_pos : ∀ j q, q ∈ primeSet j → 0 < x j q)
    (x_lt_one : ∀ j q, q ∈ primeSet j → x j q < 1)
    (primeSet_nonempty : ∀ j, (primeSet j).Nonempty)
    (mean_lower :
      ∀ j,
        -(((11 : ℝ) / 5) * 100 *
            Real.log (trackBLinearPrimeConcreteBase j : ℝ)) ≤
          ∑ q ∈ primeSet j, Real.log (1 - x j q ^ 2))
    (variance_le :
      ∀ j,
        (∑ q ∈ primeSet j, Real.log ((1 + x j q) / (1 - x j q)) ^ 2) ≤
          10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_finiteEulerProduct
    core primeSet x smallFactor_eq x_pos x_lt_one mean_lower
    (by
      intro j
      exact smallProduct_log_weight_sq_sum_pos_of_nonempty (primeSet j) (x j)
        (primeSet_nonempty j) (fun q hq => x_pos j q hq) (fun q hq => x_lt_one j q hq))
    variance_le

/-- Finite small-prime set up to a natural cutoff.  This is the canonical
finite set for the small Euler product once the analytic cutoff `Y_j` has been
chosen. -/
def trackBLinearPrimeExpSmallPrimeSetUpTo (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Y).filter Nat.Prime

/-- First-pass small-prime cutoff for the product/rough route.  The exponential
endpoint schedule uses base-two integer surrogates, so this is the natural
finite version of the analytic cutoff `exp(base^(2K))`. -/
def trackBLinearPrimeExpSmallCutoff (j : ℕ) : ℕ :=
  2 ^ (trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK))

/-- Thinner exploratory small-prime cutoff `2^(base^K)`.  This keeps the
canonical `2K` cutoff available while exposing a lower-memory product for
analytic experiments with weaker prime-reciprocal constants. -/
def trackBLinearPrimeExpThinSmallCutoff (j : ℕ) : ℕ :=
  2 ^ (trackBLinearPrimeConcreteBase j ^ trackBLinearPrimeConcreteK)

/-- The concrete small-prime cutoff is at least `2`, so the cutoff prime set is
nonempty. -/
theorem trackBLinearPrimeExpSmallCutoff_ge_two (j : ℕ) :
    2 ≤ trackBLinearPrimeExpSmallCutoff j := by
  unfold trackBLinearPrimeExpSmallCutoff
  exact Nat.le_pow (a := 2)
    (pow_pos (trackBLinearPrimeConcreteBase_pos j) (2 * trackBLinearPrimeConcreteK))

/-- The thinner exploratory small-prime cutoff is at least `2`. -/
theorem trackBLinearPrimeExpThinSmallCutoff_ge_two (j : ℕ) :
    2 ≤ trackBLinearPrimeExpThinSmallCutoff j := by
  unfold trackBLinearPrimeExpThinSmallCutoff
  exact Nat.le_pow (a := 2)
    (pow_pos (trackBLinearPrimeConcreteBase_pos j) trackBLinearPrimeConcreteK)

/-- Every element of the finite small-prime cutoff set is prime. -/
theorem trackBLinearPrimeExpSmallPrimeSetUpTo_prime {Y q : ℕ}
    (hq : q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo Y) :
    Nat.Prime q := by
  exact (Finset.mem_filter.mp hq).2

/-- The prime `2` belongs to the cutoff set when the cutoff is at least `2`. -/
theorem two_mem_trackBLinearPrimeExpSmallPrimeSetUpTo {Y : ℕ} (hY : 2 ≤ Y) :
    2 ∈ trackBLinearPrimeExpSmallPrimeSetUpTo Y := by
  unfold trackBLinearPrimeExpSmallPrimeSetUpTo
  exact Finset.mem_filter.mpr ⟨by simp [hY], Nat.prime_two⟩

/-- The finite small-prime cutoff set is nonempty when the cutoff is at least
`2`. -/
theorem trackBLinearPrimeExpSmallPrimeSetUpTo_nonempty {Y : ℕ} (hY : 2 ≤ Y) :
    (trackBLinearPrimeExpSmallPrimeSetUpTo Y).Nonempty :=
  ⟨2, two_mem_trackBLinearPrimeExpSmallPrimeSetUpTo hY⟩

/-- Pointwise telescoping comparison for the reciprocal-square tail. -/
theorem trackBLinearPrimeExp_inv_natCast_sq_le_pred_inv_sub_inv {q : ℕ} (hq : 2 ≤ q) :
    ((q : ℝ)⁻¹) ^ 2 ≤ (((q : ℝ) - 1)⁻¹) - ((q : ℝ)⁻¹) := by
  have hqpos_nat : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqpos_nat
  have hqge : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpredpos : (0 : ℝ) < (q : ℝ) - 1 := by nlinarith
  rw [inv_pow]
  field_simp [hqpos.ne', hpredpos.ne']
  nlinarith

/-- Telescoping sum of the reciprocal first differences on an integer interval. -/
theorem trackBLinearPrimeExp_sum_Icc_inv_sub_inv_eq (Y : ℕ) (hY : 2 ≤ Y) :
    (∑ q ∈ Finset.Icc 2 Y, (((q : ℝ) - 1)⁻¹ - (q : ℝ)⁻¹)) =
      1 - (Y : ℝ)⁻¹ := by
  induction Y with
  | zero => omega
  | succ Y ih =>
      by_cases hY2 : 2 ≤ Y
      · rw [Finset.sum_Icc_succ_top (show 2 ≤ Y + 1 by omega)]
        have hih := ih hY2
        rw [hih]
        have hYpos_nat : 0 < Y := lt_of_lt_of_le (by norm_num) hY2
        have hYpos : (0 : ℝ) < Y := by exact_mod_cast hYpos_nat
        have hYsuccpos : (0 : ℝ) < Y + 1 := by positivity
        field_simp [hYpos.ne', hYsuccpos.ne']
        norm_num [Nat.cast_add, Nat.cast_one]
        ring
      · have hYeq : Y = 1 := by omega
        subst Y
        norm_num

/-- The full integer reciprocal-square sum between `2` and any cutoff is at most `1`. -/
theorem trackBLinearPrimeExp_sum_Icc_recip_sq_le_one (Y : ℕ) :
    (∑ q ∈ Finset.Icc 2 Y, ((q : ℝ)⁻¹) ^ 2) ≤ 1 := by
  by_cases hY : 2 ≤ Y
  · have hpoint :
        ∀ q ∈ Finset.Icc 2 Y,
          ((q : ℝ)⁻¹) ^ 2 ≤ (((q : ℝ) - 1)⁻¹) - ((q : ℝ)⁻¹) := by
      intro q hq
      exact trackBLinearPrimeExp_inv_natCast_sq_le_pred_inv_sub_inv
        (Finset.mem_Icc.mp hq).1
    have hsum := Finset.sum_le_sum hpoint
    have htel := trackBLinearPrimeExp_sum_Icc_inv_sub_inv_eq Y hY
    have hYpos_nat : 0 < Y := lt_of_lt_of_le (by norm_num) hY
    have hYpos : (0 : ℝ) < Y := by exact_mod_cast hYpos_nat
    have htail : 1 - (Y : ℝ)⁻¹ ≤ 1 := by
      have hinv_nonneg : 0 ≤ (Y : ℝ)⁻¹ := inv_nonneg.mpr hYpos.le
      nlinarith
    calc
      (∑ q ∈ Finset.Icc 2 Y, ((q : ℝ)⁻¹) ^ 2)
          ≤ ∑ q ∈ Finset.Icc 2 Y, (((q : ℝ) - 1)⁻¹ - ((q : ℝ)⁻¹)) := hsum
      _ = 1 - (Y : ℝ)⁻¹ := htel
      _ ≤ 1 := htail
  · have hemp : Finset.Icc 2 Y = ∅ := by
      ext q
      simp only [Finset.mem_Icc]
      constructor
      · intro hq
        exact False.elim (hY (le_trans hq.1 hq.2))
      · intro h
        simp at h
    simp [hemp]

/-- The prime-filtered reciprocal-square sum up to any cutoff is at most `1`. -/
theorem trackBLinearPrimeExpSmallPrimeSetUpTo_recip_sq_sum_le_one (Y : ℕ) :
    (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo Y, ((q : ℝ)⁻¹) ^ 2) ≤ 1 := by
  unfold trackBLinearPrimeExpSmallPrimeSetUpTo
  calc
    (∑ q ∈ (Finset.Icc 2 Y).filter Nat.Prime, ((q : ℝ)⁻¹) ^ 2)
        ≤ ∑ q ∈ Finset.Icc 2 Y, ((q : ℝ)⁻¹) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro q hq
            exact (Finset.mem_filter.mp hq).1
          · intro _q _hq _hnot
            positivity
    _ ≤ 1 := trackBLinearPrimeExp_sum_Icc_recip_sq_le_one Y

/-- The concrete base is large enough that `5 log(base)` dominates the unit bound. -/
theorem trackBLinearPrimeConcreteBase_one_le_five_log (j : ℕ) :
    (1 : ℝ) ≤ 5 * Real.log (trackBLinearPrimeConcreteBase j : ℝ) := by
  have hb2 : (2 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
    exact_mod_cast trackBLinearPrimeConcreteBase_two_le j
  have hlog_mono : Real.log (2 : ℝ) ≤
      Real.log (trackBLinearPrimeConcreteBase j : ℝ) := by
    exact Real.log_le_log (by norm_num) hb2
  have hlog2 : (1 : ℝ) ≤ 5 * Real.log (2 : ℝ) := by
    nlinarith [Real.log_two_gt_d9]
  nlinarith

/-- Concrete-cutoff reciprocal-square input for the small Euler-product tail. -/
theorem trackBLinearPrimeExpSmallCutoff_recip_sq_sum_le_five_log (j : ℕ) :
    (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
      (trackBLinearPrimeExpSmallCutoff j), ((q : ℝ)⁻¹) ^ 2) ≤
      5 * Real.log (trackBLinearPrimeConcreteBase j : ℝ) := by
  exact (trackBLinearPrimeExpSmallPrimeSetUpTo_recip_sq_sum_le_one
    (trackBLinearPrimeExpSmallCutoff j)).trans
    (trackBLinearPrimeConcreteBase_one_le_five_log j)

/-- Thin-cutoff reciprocal-square input for exploratory small-product routes. -/
theorem trackBLinearPrimeExpThinSmallCutoff_recip_sq_sum_le_five_log (j : ℕ) :
    (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
      (trackBLinearPrimeExpThinSmallCutoff j), ((q : ℝ)⁻¹) ^ 2) ≤
      5 * Real.log (trackBLinearPrimeConcreteBase j : ℝ) := by
  exact (trackBLinearPrimeExpSmallPrimeSetUpTo_recip_sq_sum_le_one
    (trackBLinearPrimeExpThinSmallCutoff j)).trans
    (trackBLinearPrimeConcreteBase_one_le_five_log j)

/-- Standard Mertens-style input for prime reciprocals, isolated in the common
`log log Y + 1` form.  This is the only analytic number-theory estimate still
needed by the canonical small Euler-product tail. -/
structure TrackBLinearPrimeExpSmallPrimeReciprocalLogLogUpperFacts where
  recip_sum_le_loglog_add_one :
    ∀ Y, 2 ≤ Y →
      (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo Y, ((q : ℝ)⁻¹)) ≤
        Real.log (Real.log (Y : ℝ)) + 1

/-- Flexible reciprocal-budget interface for the concrete small-prime cutoff.
This is an analytic workbench: callers may supply any first- and second-moment
reciprocal budgets, provided they satisfy the two scalar inequalities needed by
the mean and variance reducers. -/
structure TrackBLinearPrimeExpSmallCutoffReciprocalBudgetFacts where
  recipBudget : ℕ → ℝ
  recipSqBudget : ℕ → ℝ
  recip_sum_le :
    ∀ j,
      (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
        (trackBLinearPrimeExpSmallCutoff j), ((q : ℝ)⁻¹)) ≤ recipBudget j
  recip_sq_sum_le :
    ∀ j,
      (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
        (trackBLinearPrimeExpSmallCutoff j), ((q : ℝ)⁻¹) ^ 2) ≤ recipSqBudget j
  mean_budget_le :
    ∀ j,
      recipBudget j + 2 * recipSqBudget j ≤
        ((11 : ℝ) / 5) * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)
  variance_budget_le :
    ∀ j,
      4 * recipBudget j + 24 * recipSqBudget j ≤
        10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)

/-- Cutoff-parameterized reciprocal-budget interface.  This is useful for
testing alternate small-prime memory cutoffs without changing the active
concrete `2K` cutoff definitions. -/
structure TrackBLinearPrimeExpSmallPrimeCutoffReciprocalBudgetFacts
    (upper : ℕ → ℕ) where
  upper_ge_two : ∀ j, 2 ≤ upper j
  recipBudget : ℕ → ℝ
  recipSqBudget : ℕ → ℝ
  recip_sum_le :
    ∀ j,
      (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (upper j), ((q : ℝ)⁻¹)) ≤
        recipBudget j
  recip_sq_sum_le :
    ∀ j,
      (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (upper j), ((q : ℝ)⁻¹) ^ 2) ≤
        recipSqBudget j
  mean_budget_le :
    ∀ j,
      recipBudget j + 2 * recipSqBudget j ≤
        ((11 : ℝ) / 5) * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)
  variance_budget_le :
    ∀ j,
      4 * recipBudget j + 24 * recipSqBudget j ≤
        10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)

/-- Fixed-coefficient constructor for the cutoff-parameterized reciprocal
budget interface. -/
def trackBLinearPrimeExpSmallPrimeCutoffReciprocalBudgetFacts_of_fixedCoefficients
    (upper : ℕ → ℕ) (upper_ge_two : ∀ j, 2 ≤ upper j) {A B : ℝ}
    (recip_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (upper j), ((q : ℝ)⁻¹)) ≤
          A * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
    (recip_sq_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (upper j), ((q : ℝ)⁻¹) ^ 2) ≤
          B * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
    (mean_coeff_le : A + 2 * B ≤ ((11 : ℝ) / 5) * 100)
    (variance_coeff_le : 4 * A + 24 * B ≤ 10 * 100) :
    TrackBLinearPrimeExpSmallPrimeCutoffReciprocalBudgetFacts upper where
  upper_ge_two := upper_ge_two
  recipBudget := fun j => A * Real.log (trackBLinearPrimeConcreteBase j : ℝ)
  recipSqBudget := fun j => B * Real.log (trackBLinearPrimeConcreteBase j : ℝ)
  recip_sum_le := recip_sum_le
  recip_sq_sum_le := recip_sq_sum_le
  mean_budget_le := by
    intro j
    let L := Real.log (trackBLinearPrimeConcreteBase j : ℝ)
    have hL_nonneg : 0 ≤ L := by
      have hb : (1 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
        exact_mod_cast (trackBLinearPrimeConcreteBase_one_lt j).le
      exact Real.log_nonneg hb
    have hmul := mul_le_mul_of_nonneg_right mean_coeff_le hL_nonneg
    nlinarith
  variance_budget_le := by
    intro j
    let L := Real.log (trackBLinearPrimeConcreteBase j : ℝ)
    have hL_nonneg : 0 ≤ L := by
      have hb : (1 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
        exact_mod_cast (trackBLinearPrimeConcreteBase_one_lt j).le
      exact Real.log_nonneg hb
    have hmul := mul_le_mul_of_nonneg_right variance_coeff_le hL_nonneg
    nlinarith

/-- Constructor for the flexible reciprocal-budget interface from fixed
coefficients multiplying `log(base)`.  This makes the scalar checks visible:
the coefficients must satisfy `A + 2B <= 220` and `4A + 24B <= 1000`. -/
def trackBLinearPrimeExpSmallCutoffReciprocalBudgetFacts_of_fixedCoefficients
    {A B : ℝ}
    (recip_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpSmallCutoff j), ((q : ℝ)⁻¹)) ≤
          A * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
    (recip_sq_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpSmallCutoff j), ((q : ℝ)⁻¹) ^ 2) ≤
          B * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
    (mean_coeff_le : A + 2 * B ≤ ((11 : ℝ) / 5) * 100)
    (variance_coeff_le : 4 * A + 24 * B ≤ 10 * 100) :
    TrackBLinearPrimeExpSmallCutoffReciprocalBudgetFacts where
  recipBudget := fun j => A * Real.log (trackBLinearPrimeConcreteBase j : ℝ)
  recipSqBudget := fun j => B * Real.log (trackBLinearPrimeConcreteBase j : ℝ)
  recip_sum_le := recip_sum_le
  recip_sq_sum_le := recip_sq_sum_le
  mean_budget_le := by
    intro j
    let L := Real.log (trackBLinearPrimeConcreteBase j : ℝ)
    have hL_nonneg : 0 ≤ L := by
      have hb : (1 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
        exact_mod_cast (trackBLinearPrimeConcreteBase_one_lt j).le
      exact Real.log_nonneg hb
    have hmul := mul_le_mul_of_nonneg_right mean_coeff_le hL_nonneg
    nlinarith
  variance_budget_le := by
    intro j
    let L := Real.log (trackBLinearPrimeConcreteBase j : ℝ)
    have hL_nonneg : 0 ≤ L := by
      have hb : (1 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
        exact_mod_cast (trackBLinearPrimeConcreteBase_one_lt j).le
      exact Real.log_nonneg hb
    have hmul := mul_le_mul_of_nonneg_right variance_coeff_le hL_nonneg
    nlinarith

/-- At the concrete cutoff, the `log log Y` term in the standard Mertens
input is at most `200 * log(base)`. -/
theorem trackBLinearPrimeExpSmallCutoff_log_log_le_twoK_log (j : ℕ) :
    Real.log (Real.log (trackBLinearPrimeExpSmallCutoff j : ℝ)) ≤
      (200 : ℝ) * Real.log (trackBLinearPrimeConcreteBase j : ℝ) := by
  let n : ℕ := trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK)
  have hcut : (trackBLinearPrimeExpSmallCutoff j : ℝ) = (2 : ℝ) ^ n := by
    change ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n
    exact_mod_cast (show (2 ^ n : ℕ) = 2 ^ n by rfl)
  rw [hcut, Real.log_pow]
  have hn_pos_nat : 0 < n := by
    dsimp [n]
    exact pow_pos (trackBLinearPrimeConcreteBase_pos j) (2 * trackBLinearPrimeConcreteK)
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have harg_pos : 0 < (n : ℝ) * Real.log (2 : ℝ) := mul_pos hn_pos hlog2_pos
  have hlog2_le_one : Real.log (2 : ℝ) ≤ 1 := by
    exact (Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < 2)).2 Real.exp_one_gt_two.le
  have harg_le : (n : ℝ) * Real.log (2 : ℝ) ≤ n := by
    calc
      (n : ℝ) * Real.log (2 : ℝ) ≤ (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlog2_le_one hn_pos.le
      _ = n := by ring
  have hle_log_n :
      Real.log ((n : ℝ) * Real.log (2 : ℝ)) ≤ Real.log (n : ℝ) :=
    Real.log_le_log harg_pos harg_le
  have hlogn :
      Real.log (n : ℝ) =
        ((2 * trackBLinearPrimeConcreteK : ℕ) : ℝ) *
          Real.log (trackBLinearPrimeConcreteBase j : ℝ) := by
    have hn_cast : (n : ℝ) =
        (trackBLinearPrimeConcreteBase j : ℝ) ^ (2 * trackBLinearPrimeConcreteK) := by
      change ((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) :
          ℝ) =
        (trackBLinearPrimeConcreteBase j : ℝ) ^ (2 * trackBLinearPrimeConcreteK)
      exact_mod_cast (show trackBLinearPrimeConcreteBase j ^
          (2 * trackBLinearPrimeConcreteK) =
        trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) by rfl)
    rw [hn_cast, Real.log_pow]
  calc
    Real.log ((n : ℝ) * Real.log (2 : ℝ)) ≤ Real.log (n : ℝ) := hle_log_n
    _ = ((2 * trackBLinearPrimeConcreteK : ℕ) : ℝ) *
          Real.log (trackBLinearPrimeConcreteBase j : ℝ) := hlogn
    _ = (200 : ℝ) * Real.log (trackBLinearPrimeConcreteBase j : ℝ) := by
      change (200 : ℝ) * Real.log (trackBLinearPrimeConcreteBase j : ℝ) =
        (200 : ℝ) * Real.log (trackBLinearPrimeConcreteBase j : ℝ)
      rfl

/-- A standard `log log Y + 1` Mertens upper bound implies the concrete
reciprocal input required by the small-product tail. -/
theorem trackBLinearPrimeExpSmallCutoff_recip_sum_le_of_loglogUpper
    (h : TrackBLinearPrimeExpSmallPrimeReciprocalLogLogUpperFacts) (j : ℕ) :
    (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
      (trackBLinearPrimeExpSmallCutoff j), ((q : ℝ)⁻¹)) ≤
      205 * Real.log (trackBLinearPrimeConcreteBase j : ℝ) := by
  have hsum := h.recip_sum_le_loglog_add_one
    (trackBLinearPrimeExpSmallCutoff j) (trackBLinearPrimeExpSmallCutoff_ge_two j)
  have hloglog := trackBLinearPrimeExpSmallCutoff_log_log_le_twoK_log j
  have hone := trackBLinearPrimeConcreteBase_one_le_five_log j
  nlinarith

/-- The usual `205 log(base)` reciprocal input, together with the elementary
square-reciprocal bound, supplies the flexible reciprocal-budget interface. -/
def trackBLinearPrimeExpSmallCutoffReciprocalBudgetFacts_of_reciprocalSum
    (recip_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpSmallCutoff j), ((q : ℝ)⁻¹)) ≤
          205 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpSmallCutoffReciprocalBudgetFacts :=
  trackBLinearPrimeExpSmallCutoffReciprocalBudgetFacts_of_fixedCoefficients
    (A := 205) (B := 5)
    recip_sum_le
    (fun j => trackBLinearPrimeExpSmallCutoff_recip_sq_sum_le_five_log j)
    (by norm_num)
    (by norm_num)

/-- The standard `log log Y + 1` Mertens-style input supplies the flexible
reciprocal-budget interface at the concrete small-prime cutoff. -/
def trackBLinearPrimeExpSmallCutoffReciprocalBudgetFacts_of_loglogUpper
    (h : TrackBLinearPrimeExpSmallPrimeReciprocalLogLogUpperFacts) :
    TrackBLinearPrimeExpSmallCutoffReciprocalBudgetFacts :=
  trackBLinearPrimeExpSmallCutoffReciprocalBudgetFacts_of_reciprocalSum
    (trackBLinearPrimeExpSmallCutoff_recip_sum_le_of_loglogUpper h)

/-- At the thinner exploratory cutoff, the `log log Y` term is at most
`K * log(base) = 100 * log(base)`. -/
theorem trackBLinearPrimeExpThinSmallCutoff_log_log_le_K_log (j : ℕ) :
    Real.log (Real.log (trackBLinearPrimeExpThinSmallCutoff j : ℝ)) ≤
      (100 : ℝ) * Real.log (trackBLinearPrimeConcreteBase j : ℝ) := by
  let n : ℕ := trackBLinearPrimeConcreteBase j ^ trackBLinearPrimeConcreteK
  have hcut : (trackBLinearPrimeExpThinSmallCutoff j : ℝ) = (2 : ℝ) ^ n := by
    change ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n
    exact_mod_cast (show (2 ^ n : ℕ) = 2 ^ n by rfl)
  rw [hcut, Real.log_pow]
  have hn_pos_nat : 0 < n := by
    dsimp [n]
    exact pow_pos (trackBLinearPrimeConcreteBase_pos j) trackBLinearPrimeConcreteK
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have harg_pos : 0 < (n : ℝ) * Real.log (2 : ℝ) := mul_pos hn_pos hlog2_pos
  have hlog2_le_one : Real.log (2 : ℝ) ≤ 1 := by
    exact (Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < 2)).2 Real.exp_one_gt_two.le
  have harg_le : (n : ℝ) * Real.log (2 : ℝ) ≤ n := by
    calc
      (n : ℝ) * Real.log (2 : ℝ) ≤ (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlog2_le_one hn_pos.le
      _ = n := by ring
  have hle_log_n :
      Real.log ((n : ℝ) * Real.log (2 : ℝ)) ≤ Real.log (n : ℝ) :=
    Real.log_le_log harg_pos harg_le
  have hlogn :
      Real.log (n : ℝ) =
        (trackBLinearPrimeConcreteK : ℝ) *
          Real.log (trackBLinearPrimeConcreteBase j : ℝ) := by
    have hn_cast : (n : ℝ) =
        (trackBLinearPrimeConcreteBase j : ℝ) ^ trackBLinearPrimeConcreteK := by
      change ((trackBLinearPrimeConcreteBase j ^ trackBLinearPrimeConcreteK : ℕ) : ℝ) =
        (trackBLinearPrimeConcreteBase j : ℝ) ^ trackBLinearPrimeConcreteK
      exact_mod_cast (show trackBLinearPrimeConcreteBase j ^ trackBLinearPrimeConcreteK =
        trackBLinearPrimeConcreteBase j ^ trackBLinearPrimeConcreteK by rfl)
    rw [hn_cast, Real.log_pow]
  calc
    Real.log ((n : ℝ) * Real.log (2 : ℝ)) ≤ Real.log (n : ℝ) := hle_log_n
    _ = (trackBLinearPrimeConcreteK : ℝ) *
          Real.log (trackBLinearPrimeConcreteBase j : ℝ) := hlogn
    _ = (100 : ℝ) * Real.log (trackBLinearPrimeConcreteBase j : ℝ) := by
      norm_num [trackBLinearPrimeConcreteK]

/-- A standard `log log Y + 1` Mertens upper bound implies the thinner-cutoff
reciprocal input `105 * log(base)`. -/
theorem trackBLinearPrimeExpThinSmallCutoff_recip_sum_le_of_loglogUpper
    (h : TrackBLinearPrimeExpSmallPrimeReciprocalLogLogUpperFacts) (j : ℕ) :
    (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
      (trackBLinearPrimeExpThinSmallCutoff j), ((q : ℝ)⁻¹)) ≤
      105 * Real.log (trackBLinearPrimeConcreteBase j : ℝ) := by
  have hsum := h.recip_sum_le_loglog_add_one
    (trackBLinearPrimeExpThinSmallCutoff j) (trackBLinearPrimeExpThinSmallCutoff_ge_two j)
  have hloglog := trackBLinearPrimeExpThinSmallCutoff_log_log_le_K_log j
  have hone := trackBLinearPrimeConcreteBase_one_le_five_log j
  nlinarith

/-- The thinner cutoff plus the usual elementary square-reciprocal bound
supplies the cutoff-parameterized reciprocal-budget interface. -/
def trackBLinearPrimeExpThinSmallCutoffReciprocalBudgetFacts_of_reciprocalSum
    (recip_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpThinSmallCutoff j), ((q : ℝ)⁻¹)) ≤
          105 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpSmallPrimeCutoffReciprocalBudgetFacts
      trackBLinearPrimeExpThinSmallCutoff :=
  trackBLinearPrimeExpSmallPrimeCutoffReciprocalBudgetFacts_of_fixedCoefficients
    trackBLinearPrimeExpThinSmallCutoff trackBLinearPrimeExpThinSmallCutoff_ge_two
    (A := 105) (B := 5)
    recip_sum_le
    (fun j => trackBLinearPrimeExpThinSmallCutoff_recip_sq_sum_le_five_log j)
    (by norm_num)
    (by norm_num)

/-- Thin-cutoff reciprocal-budget constructor with an arbitrary first-reciprocal
coefficient.  This is the verifier-facing hook for weaker analytic estimates
than the standard `log log Y + 1` input, provided the displayed scalar checks
close. -/
def trackBLinearPrimeExpThinSmallCutoffReciprocalBudgetFacts_of_reciprocalCoeff
    {A : ℝ}
    (recip_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpThinSmallCutoff j), ((q : ℝ)⁻¹)) ≤
          A * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
    (mean_coeff_le : A + 2 * 5 ≤ ((11 : ℝ) / 5) * 100)
    (variance_coeff_le : 4 * A + 24 * 5 ≤ 10 * 100) :
    TrackBLinearPrimeExpSmallPrimeCutoffReciprocalBudgetFacts
      trackBLinearPrimeExpThinSmallCutoff :=
  trackBLinearPrimeExpSmallPrimeCutoffReciprocalBudgetFacts_of_fixedCoefficients
    trackBLinearPrimeExpThinSmallCutoff trackBLinearPrimeExpThinSmallCutoff_ge_two
    (A := A) (B := 5)
    recip_sum_le
    (fun j => trackBLinearPrimeExpThinSmallCutoff_recip_sq_sum_le_five_log j)
    mean_coeff_le
    variance_coeff_le

/-- The standard `log log Y + 1` Mertens-style input supplies the thinner-cutoff
reciprocal-budget workbench. -/
def trackBLinearPrimeExpThinSmallCutoffReciprocalBudgetFacts_of_loglogUpper
    (h : TrackBLinearPrimeExpSmallPrimeReciprocalLogLogUpperFacts) :
    TrackBLinearPrimeExpSmallPrimeCutoffReciprocalBudgetFacts
      trackBLinearPrimeExpThinSmallCutoff :=
  trackBLinearPrimeExpThinSmallCutoffReciprocalBudgetFacts_of_reciprocalSum
    (trackBLinearPrimeExpThinSmallCutoff_recip_sum_le_of_loglogUpper h)

/-- Canonical inverse-square-root small Euler product for the Packet B
product/rough decomposition. -/
noncomputable def trackBLinearPrimeExpSmallEulerFactor (omega : Omega) (j : ℕ) : ℝ :=
  ∏ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (trackBLinearPrimeExpSmallCutoff j),
    (1 + eps omega q * (Real.sqrt (q : ℝ))⁻¹)

/-- Thinner inverse-square-root small Euler product using the exploratory
`2^(base^K)` cutoff. -/
noncomputable def trackBLinearPrimeExpThinSmallEulerFactor (omega : Omega) (j : ℕ) : ℝ :=
  ∏ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (trackBLinearPrimeExpThinSmallCutoff j),
    (1 + eps omega q * (Real.sqrt (q : ℝ))⁻¹)

/-- No-mass fixed-floor product/rough core using the canonical small Euler
factor and an arbitrary rough coefficient family. -/
def trackBLinearPrimeExpNoMassCoreFacts_of_smallEulerRough
    (roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ) :
    TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts :=
  trackBLinearPrimeExpNoMassCoreFacts_of_smallRough
    trackBLinearPrimeExpSmallEulerFactor roughCoeff

/-- No-mass fixed-floor product/rough core using the thinner exploratory small
Euler factor and an arbitrary rough coefficient family. -/
def trackBLinearPrimeExpNoMassCoreFacts_of_thinSmallEulerRough
    (roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ) :
    TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts :=
  trackBLinearPrimeExpNoMassCoreFacts_of_smallRough
    trackBLinearPrimeExpThinSmallEulerFactor roughCoeff

/-- No-mass finite Euler-product small-tail adapter specialized to the intended
small-prime factor `x_q = 1 / sqrt(q)`.  Primality supplies the local
`0 < x_q < 1` bounds. -/
def trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProduct
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (primeSet : ℕ → Finset ℕ)
    (smallFactor_eq :
      ∀ omega j,
        core.smallFactor omega j =
          ∏ q ∈ primeSet j, (1 + eps omega q * (Real.sqrt (q : ℝ))⁻¹))
    (primeSet_prime : ∀ j q, q ∈ primeSet j → Nat.Prime q)
    (primeSet_nonempty : ∀ j, (primeSet j).Nonempty)
    (mean_lower :
      ∀ j,
        -(((11 : ℝ) / 5) * 100 *
            Real.log (trackBLinearPrimeConcreteBase j : ℝ)) ≤
          ∑ q ∈ primeSet j, Real.log (1 - ((Real.sqrt (q : ℝ))⁻¹) ^ 2))
    (variance_le :
      ∀ j,
        (∑ q ∈ primeSet j,
          Real.log ((1 + (Real.sqrt (q : ℝ))⁻¹) /
            (1 - (Real.sqrt (q : ℝ))⁻¹)) ^ 2) ≤
          10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_finiteEulerProductNonempty
    core primeSet (fun _j q => (Real.sqrt (q : ℝ))⁻¹) smallFactor_eq
    (by
      intro j q hq
      exact smallProduct_inv_sqrt_natCast_pos (primeSet_prime j q hq).pos)
    (by
      intro j q hq
      exact smallProduct_inv_sqrt_natCast_lt_one (primeSet_prime j q hq).two_le)
    primeSet_nonempty mean_lower variance_le

/-- No-mass inverse-square-root Euler-product adapter for the canonical finite
small-prime cutoff set `{q : prime, 2 <= q <= Y_j}`.  The cutoff lower bound
`2 <= Y_j` supplies both primality and nonemptiness bookkeeping. -/
def trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProductUpTo
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (upper : ℕ → ℕ)
    (upper_ge_two : ∀ j, 2 ≤ upper j)
    (smallFactor_eq :
      ∀ omega j,
        core.smallFactor omega j =
          ∏ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (upper j),
            (1 + eps omega q * (Real.sqrt (q : ℝ))⁻¹))
    (mean_lower :
      ∀ j,
        -(((11 : ℝ) / 5) * 100 *
            Real.log (trackBLinearPrimeConcreteBase j : ℝ)) ≤
          ∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (upper j),
            Real.log (1 - ((Real.sqrt (q : ℝ))⁻¹) ^ 2))
    (variance_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (upper j),
          Real.log ((1 + (Real.sqrt (q : ℝ))⁻¹) /
            (1 - (Real.sqrt (q : ℝ))⁻¹)) ^ 2) ≤
          10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProduct
    core (fun j => trackBLinearPrimeExpSmallPrimeSetUpTo (upper j)) smallFactor_eq
    (by
      intro j q hq
      exact trackBLinearPrimeExpSmallPrimeSetUpTo_prime hq)
    (by
      intro j
      exact trackBLinearPrimeExpSmallPrimeSetUpTo_nonempty (upper_ge_two j))
    mean_lower variance_le

/-- Arbitrary-cutoff inverse-square-root Euler-product adapter from the
cutoff-parameterized reciprocal-budget workbench. -/
def trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProductUpToBudget
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (upper : ℕ → ℕ)
    (smallFactor_eq :
      ∀ omega j,
        core.smallFactor omega j =
          ∏ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (upper j),
            (1 + eps omega q * (Real.sqrt (q : ℝ))⁻¹))
    (budget : TrackBLinearPrimeExpSmallPrimeCutoffReciprocalBudgetFacts upper) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProductUpTo
    core upper budget.upper_ge_two smallFactor_eq
    (by
      intro j
      let s := trackBLinearPrimeExpSmallPrimeSetUpTo (upper j)
      have hmean_prime :
          -(((11 : ℝ) / 5) * 100 *
              Real.log (trackBLinearPrimeConcreteBase j : ℝ)) ≤
            ∑ q ∈ s, Real.log (1 - ((q : ℝ)⁻¹)) :=
        smallProduct_primeLogMeanLower_of_reciprocal_bounds
          (s := s)
          (hge_two := fun q hq => (trackBLinearPrimeExpSmallPrimeSetUpTo_prime hq).two_le)
          (A := budget.recipBudget j)
          (B := budget.recipSqBudget j)
          (C := ((11 : ℝ) / 5) * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
          (by simpa [s] using budget.recip_sum_le j)
          (by simpa [s] using budget.recip_sq_sum_le j)
          (budget.mean_budget_le j)
      have hmean_eq :
          (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (upper j),
              Real.log (1 - ((Real.sqrt (q : ℝ))⁻¹) ^ 2)) =
            ∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (upper j),
              Real.log (1 - ((q : ℝ)⁻¹)) :=
        smallProduct_inv_sqrt_mean_sum_eq_inv_nat
          (trackBLinearPrimeExpSmallPrimeSetUpTo (upper j))
          (fun q hq => (trackBLinearPrimeExpSmallPrimeSetUpTo_prime hq).pos)
      simpa [s, hmean_eq] using hmean_prime)
    (by
      intro j
      let s := trackBLinearPrimeExpSmallPrimeSetUpTo (upper j)
      exact smallProduct_logWeightSqSum_le_of_reciprocal_bounds
        (s := s)
        (hge_two := fun q hq => (trackBLinearPrimeExpSmallPrimeSetUpTo_prime hq).two_le)
        (A := budget.recipBudget j)
        (B := budget.recipSqBudget j)
        (C := 10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
        (by simpa [s] using budget.recip_sum_le j)
        (by simpa [s] using budget.recip_sq_sum_le j)
        (budget.variance_budget_le j))

/-- No-mass inverse-square-root Euler-product adapter for the concrete first-pass
small-prime cutoff `2^(base^(2K))`.  This removes the arbitrary cutoff and
cutoff lower-bound inputs from the Packet C small-product tail handoff. -/
def trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProductSmallCutoff
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (smallFactor_eq :
      ∀ omega j,
        core.smallFactor omega j =
          ∏ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
              (trackBLinearPrimeExpSmallCutoff j),
            (1 + eps omega q * (Real.sqrt (q : ℝ))⁻¹))
    (mean_lower :
      ∀ j,
        -(((11 : ℝ) / 5) * 100 *
            Real.log (trackBLinearPrimeConcreteBase j : ℝ)) ≤
          ∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
              (trackBLinearPrimeExpSmallCutoff j),
            Real.log (1 - ((Real.sqrt (q : ℝ))⁻¹) ^ 2))
    (variance_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpSmallCutoff j),
          Real.log ((1 + (Real.sqrt (q : ℝ))⁻¹) /
            (1 - (Real.sqrt (q : ℝ))⁻¹)) ^ 2) ≤
          10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProductUpTo
    core trackBLinearPrimeExpSmallCutoff trackBLinearPrimeExpSmallCutoff_ge_two
    smallFactor_eq mean_lower variance_le

/-- Concrete-cutoff small-tail adapter whose mean hypothesis is stated in the
standard prime-reciprocal Mertens form `sum log (1 - 1 / q)`. -/
def trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProductSmallCutoffPrimeLog
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (smallFactor_eq :
      ∀ omega j,
        core.smallFactor omega j =
          ∏ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
              (trackBLinearPrimeExpSmallCutoff j),
            (1 + eps omega q * (Real.sqrt (q : ℝ))⁻¹))
    (mean_lower :
      ∀ j,
        -(((11 : ℝ) / 5) * 100 *
            Real.log (trackBLinearPrimeConcreteBase j : ℝ)) ≤
          ∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
              (trackBLinearPrimeExpSmallCutoff j),
            Real.log (1 - ((q : ℝ)⁻¹)))
    (variance_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpSmallCutoff j),
          Real.log ((1 + (Real.sqrt (q : ℝ))⁻¹) /
            (1 - (Real.sqrt (q : ℝ))⁻¹)) ^ 2) ≤
          10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProductSmallCutoff
    core smallFactor_eq
    (by
      intro j
      have hmean_eq :
          (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (trackBLinearPrimeExpSmallCutoff j),
              Real.log (1 - ((Real.sqrt (q : ℝ))⁻¹) ^ 2)) =
            ∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo (trackBLinearPrimeExpSmallCutoff j),
              Real.log (1 - ((q : ℝ)⁻¹)) :=
        smallProduct_inv_sqrt_mean_sum_eq_inv_nat
          (trackBLinearPrimeExpSmallPrimeSetUpTo (trackBLinearPrimeExpSmallCutoff j))
          (fun q hq => (trackBLinearPrimeExpSmallPrimeSetUpTo_prime hq).pos)
      simpa [hmean_eq] using mean_lower j)
    variance_le

/-- Concrete-cutoff small-tail adapter whose mean hypothesis is reduced to the
coarse reciprocal bounds `sum 1/q <= 205 log base` and
`sum 1/q^2 <= 5 log base`.  The remaining variance input is still stated as
the log-weight square sum. -/
def
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProductSmallCutoffReciprocalMean
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (smallFactor_eq :
      ∀ omega j,
        core.smallFactor omega j =
          ∏ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
              (trackBLinearPrimeExpSmallCutoff j),
            (1 + eps omega q * (Real.sqrt (q : ℝ))⁻¹))
    (recip_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpSmallCutoff j), ((q : ℝ)⁻¹)) ≤
          205 * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
    (recip_sq_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpSmallCutoff j), ((q : ℝ)⁻¹) ^ 2) ≤
          5 * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
    (variance_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpSmallCutoff j),
          Real.log ((1 + (Real.sqrt (q : ℝ))⁻¹) /
            (1 - (Real.sqrt (q : ℝ))⁻¹)) ^ 2) ≤
          10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProductSmallCutoffPrimeLog
    core smallFactor_eq
    (by
      intro j
      let s := trackBLinearPrimeExpSmallPrimeSetUpTo (trackBLinearPrimeExpSmallCutoff j)
      let L := Real.log (trackBLinearPrimeConcreteBase j : ℝ)
      have hL_nonneg : 0 ≤ L := by
        have hb : (1 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
          exact_mod_cast (trackBLinearPrimeConcreteBase_one_lt j).le
        exact Real.log_nonneg hb
      exact smallProduct_primeLogMeanLower_of_reciprocal_bounds
        (s := s)
        (hge_two := fun q hq => (trackBLinearPrimeExpSmallPrimeSetUpTo_prime hq).two_le)
        (A := 205 * L) (B := 5 * L)
        (C := ((11 : ℝ) / 5) * 100 * L)
        (by simpa [s, L] using recip_sum_le j)
        (by simpa [s, L] using recip_sq_sum_le j)
        (by nlinarith))
    variance_le

/-- Concrete-cutoff small-tail adapter reduced completely to the two coarse
reciprocal estimates
`sum 1/q <= 205 log base` and `sum 1/q^2 <= 5 log base`, plus the pointwise
Euler-product definition of `smallFactor`. -/
def
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_smallCutoffReciprocalBounds
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (smallFactor_eq :
      ∀ omega j,
        core.smallFactor omega j =
          ∏ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
              (trackBLinearPrimeExpSmallCutoff j),
            (1 + eps omega q * (Real.sqrt (q : ℝ))⁻¹))
    (recip_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpSmallCutoff j), ((q : ℝ)⁻¹)) ≤
          205 * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
    (recip_sq_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpSmallCutoff j), ((q : ℝ)⁻¹) ^ 2) ≤
          5 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProductSmallCutoffReciprocalMean
    core smallFactor_eq recip_sum_le recip_sq_sum_le
    (by
      intro j
      let s := trackBLinearPrimeExpSmallPrimeSetUpTo (trackBLinearPrimeExpSmallCutoff j)
      let L := Real.log (trackBLinearPrimeConcreteBase j : ℝ)
      have hL_nonneg : 0 ≤ L := by
        have hb : (1 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
          exact_mod_cast (trackBLinearPrimeConcreteBase_one_lt j).le
        exact Real.log_nonneg hb
      exact smallProduct_logWeightSqSum_le_of_reciprocal_bounds
        (s := s)
        (hge_two := fun q hq => (trackBLinearPrimeExpSmallPrimeSetUpTo_prime hq).two_le)
        (A := 205 * L) (B := 5 * L) (C := 10 * 100 * L)
        (by simpa [s, L] using recip_sum_le j)
        (by simpa [s, L] using recip_sq_sum_le j)
        (by nlinarith))

/-- Concrete-cutoff small-tail adapter from the flexible reciprocal-budget
workbench.  The budget fields expose exactly the analytic and scalar content
needed by the mean and variance reducers. -/
def
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_smallCutoffReciprocalBudget
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (smallFactor_eq :
      ∀ omega j,
        core.smallFactor omega j =
          ∏ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
              (trackBLinearPrimeExpSmallCutoff j),
            (1 + eps omega q * (Real.sqrt (q : ℝ))⁻¹))
    (budget : TrackBLinearPrimeExpSmallCutoffReciprocalBudgetFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProductSmallCutoffPrimeLog
    core smallFactor_eq
    (by
      intro j
      let s := trackBLinearPrimeExpSmallPrimeSetUpTo (trackBLinearPrimeExpSmallCutoff j)
      exact smallProduct_primeLogMeanLower_of_reciprocal_bounds
        (s := s)
        (hge_two := fun q hq => (trackBLinearPrimeExpSmallPrimeSetUpTo_prime hq).two_le)
        (A := budget.recipBudget j)
        (B := budget.recipSqBudget j)
        (C := ((11 : ℝ) / 5) * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
        (by simpa [s] using budget.recip_sum_le j)
        (by simpa [s] using budget.recip_sq_sum_le j)
        (budget.mean_budget_le j))
    (by
      intro j
      let s := trackBLinearPrimeExpSmallPrimeSetUpTo (trackBLinearPrimeExpSmallCutoff j)
      exact smallProduct_logWeightSqSum_le_of_reciprocal_bounds
        (s := s)
        (hge_two := fun q hq => (trackBLinearPrimeExpSmallPrimeSetUpTo_prime hq).two_le)
        (A := budget.recipBudget j)
        (B := budget.recipSqBudget j)
        (C := 10 * 100 * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
        (by simpa [s] using budget.recip_sum_le j)
        (by simpa [s] using budget.recip_sq_sum_le j)
        (budget.variance_budget_le j))

/-- Thin-cutoff small-tail adapter from the cutoff-parameterized reciprocal
budget workbench. -/
def
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_thinSmallCutoffReciprocalBudget
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (smallFactor_eq :
      ∀ omega j,
        core.smallFactor omega j =
          ∏ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
              (trackBLinearPrimeExpThinSmallCutoff j),
            (1 + eps omega q * (Real.sqrt (q : ℝ))⁻¹))
    (budget :
      TrackBLinearPrimeExpSmallPrimeCutoffReciprocalBudgetFacts
        trackBLinearPrimeExpThinSmallCutoff) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_invSqrtEulerProductUpToBudget
    core trackBLinearPrimeExpThinSmallCutoff smallFactor_eq budget

/-- Thin-cutoff small-tail adapter whose only analytic reciprocal input is
`sum 1/q <= 105 * log(base)`; the square-reciprocal side is elementary. -/
def
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_thinSmallCutoffReciprocalSum
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (smallFactor_eq :
      ∀ omega j,
        core.smallFactor omega j =
          ∏ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
              (trackBLinearPrimeExpThinSmallCutoff j),
            (1 + eps omega q * (Real.sqrt (q : ℝ))⁻¹))
    (recip_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpThinSmallCutoff j), ((q : ℝ)⁻¹)) ≤
          105 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_thinSmallCutoffReciprocalBudget
    core smallFactor_eq
    (trackBLinearPrimeExpThinSmallCutoffReciprocalBudgetFacts_of_reciprocalSum
      recip_sum_le)

/-- Concrete-cutoff small-tail adapter whose only analytic reciprocal input is
the first-moment Mertens-type bound.  The square-reciprocal input is supplied by
the elementary finite telescoping estimate above. -/
def
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_smallCutoffReciprocalSum
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (smallFactor_eq :
      ∀ omega j,
        core.smallFactor omega j =
          ∏ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
              (trackBLinearPrimeExpSmallCutoff j),
            (1 + eps omega q * (Real.sqrt (q : ℝ))⁻¹))
    (recip_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpSmallCutoff j), ((q : ℝ)⁻¹)) ≤
          205 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_smallCutoffReciprocalBounds
    core smallFactor_eq recip_sum_le
    (fun j => trackBLinearPrimeExpSmallCutoff_recip_sq_sum_le_five_log j)

/-- Flexible-budget small-tail record for the canonical small-Euler no-mass
core.  Use this when experimenting with alternate analytic estimates or cutoff
normalizations while keeping the canonical product definition. -/
def
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_smallEulerRoughReciprocalBudget
    (roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (budget : TrackBLinearPrimeExpSmallCutoffReciprocalBudgetFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass
        (trackBLinearPrimeExpNoMassCoreFacts_of_smallEulerRough roughCoeff)) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_smallCutoffReciprocalBudget
    (trackBLinearPrimeExpNoMassCoreFacts_of_smallEulerRough roughCoeff)
    (by
      intro omega j
      simp only [trackBLinearPrimeExpNoMassCoreFacts_of_smallEulerRough,
        trackBLinearPrimeExpNoMassCoreFacts_of_smallRough,
        trackBLinearPrimeExpSmallEulerFactor])
    budget

/-- Flexible-budget small-tail record for the thinner small-Euler no-mass core. -/
def
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_thinSmallEulerRoughReciprocalBudget
    (roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (budget :
      TrackBLinearPrimeExpSmallPrimeCutoffReciprocalBudgetFacts
        trackBLinearPrimeExpThinSmallCutoff) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass
        (trackBLinearPrimeExpNoMassCoreFacts_of_thinSmallEulerRough roughCoeff)) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_thinSmallCutoffReciprocalBudget
    (trackBLinearPrimeExpNoMassCoreFacts_of_thinSmallEulerRough roughCoeff)
    (by
      intro omega j
      simp only [trackBLinearPrimeExpNoMassCoreFacts_of_thinSmallEulerRough,
        trackBLinearPrimeExpNoMassCoreFacts_of_smallRough,
        trackBLinearPrimeExpThinSmallEulerFactor])
    budget

/-- Thin small-Euler small-tail record from the `105 * log(base)` reciprocal
bound. -/
def
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_thinSmallEulerRoughReciprocalSum
    (roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (recip_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpThinSmallCutoff j), ((q : ℝ)⁻¹)) ≤
          105 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass
        (trackBLinearPrimeExpNoMassCoreFacts_of_thinSmallEulerRough roughCoeff)) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_thinSmallEulerRoughReciprocalBudget
    roughCoeff
    (trackBLinearPrimeExpThinSmallCutoffReciprocalBudgetFacts_of_reciprocalSum
      recip_sum_le)

/-- Thin small-Euler small-tail record from an arbitrary first-reciprocal
coefficient that passes the scalar budget checks. -/
def
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_thinSmallEulerRoughReciprocalCoeff
    (roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ) {A : ℝ}
    (recip_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpThinSmallCutoff j), ((q : ℝ)⁻¹)) ≤
          A * Real.log (trackBLinearPrimeConcreteBase j : ℝ))
    (mean_coeff_le : A + 2 * 5 ≤ ((11 : ℝ) / 5) * 100)
    (variance_coeff_le : 4 * A + 24 * 5 ≤ 10 * 100) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass
        (trackBLinearPrimeExpNoMassCoreFacts_of_thinSmallEulerRough roughCoeff)) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_thinSmallEulerRoughReciprocalBudget
    roughCoeff
    (trackBLinearPrimeExpThinSmallCutoffReciprocalBudgetFacts_of_reciprocalCoeff
      recip_sum_le mean_coeff_le variance_coeff_le)

/-- Thin small-Euler small-tail record from the standard `log log Y + 1`
Mertens-style prime reciprocal upper bound. -/
def
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_thinSmallEulerRoughLogLogMertens
    (roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (h : TrackBLinearPrimeExpSmallPrimeReciprocalLogLogUpperFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass
        (trackBLinearPrimeExpNoMassCoreFacts_of_thinSmallEulerRough roughCoeff)) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_thinSmallEulerRoughReciprocalSum
    roughCoeff
    (trackBLinearPrimeExpThinSmallCutoff_recip_sum_le_of_loglogUpper h)

/-- Small-tail record for the canonical small-Euler no-mass core.  The only
remaining analytic input is the Mertens-type reciprocal sum. -/
def
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_smallEulerRoughReciprocalSum
    (roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (recip_sum_le :
      ∀ j,
        (∑ q ∈ trackBLinearPrimeExpSmallPrimeSetUpTo
          (trackBLinearPrimeExpSmallCutoff j), ((q : ℝ)⁻¹)) ≤
          205 * Real.log (trackBLinearPrimeConcreteBase j : ℝ)) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass
        (trackBLinearPrimeExpNoMassCoreFacts_of_smallEulerRough roughCoeff)) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_smallCutoffReciprocalSum
    (trackBLinearPrimeExpNoMassCoreFacts_of_smallEulerRough roughCoeff)
    (by
      intro omega j
      simp only [trackBLinearPrimeExpNoMassCoreFacts_of_smallEulerRough,
        trackBLinearPrimeExpNoMassCoreFacts_of_smallRough,
        trackBLinearPrimeExpSmallEulerFactor])
    recip_sum_le

/-- Canonical small-Euler small-tail record from the standard `log log Y + 1`
Mertens-style prime reciprocal upper bound. -/
def
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_smallEulerRoughLogLogMertens
    (roughCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (h : TrackBLinearPrimeExpSmallPrimeReciprocalLogLogUpperFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass
        (trackBLinearPrimeExpNoMassCoreFacts_of_smallEulerRough roughCoeff)) :=
  trackBLinearPrimeExpNoMassSmallTailEventRealFacts_of_smallEulerRoughReciprocalSum
    roughCoeff
    (trackBLinearPrimeExpSmallCutoff_recip_sum_le_of_loglogUpper h)

/-- Event-witness small-tail record from the canonical small-tail record.  This
lets callers use the all-events geometry wrapper even if their estimate was
first packaged in the canonical `SmallTailRealFacts` interface. -/
def trackBLinearPrimeExpSmallTailEventRealFacts_of_real
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts core) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      core where
  badSmall := fun j _r => {omega | core.smallFactor omega j ^ 2 < core.smallFloor j}
  small_bad_subset := by
    intro _j _r _hr _hmean omega homega
    exact homega
  small_bad_event_real_le := by
    intro j r hr hmean
    exact hsmall.small_bad_real_le j r hr hmean

/-- Event-witness small-tail record from a pointwise small-factor floor. -/
def trackBLinearPrimeExpSmallTailEventRealFacts_of_pointwise
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (hsmall : ∀ omega j, core.smallFloor j ≤ core.smallFactor omega j ^ 2) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
      core where
  badSmall := fun _ _ => ∅
  small_bad_subset := by
    intro j r _hr _hmean omega hbad
    exact False.elim ((not_lt_of_ge (hsmall omega j)) hbad)
  small_bad_event_real_le := by
    intro j r _hr _hmean
    simp [trackBLinearPrimeExp_productRoughTailBudget_nonneg j]

/-- Event-witness rough-tail record from a pointwise rough-energy floor. -/
def trackBLinearPrimeExpRoughTailEventRealFacts_of_pointwise
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (hrough :
      ∀ omega j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
        core.roughFloor j r ≤
          ∑ p ∈ trackBFreshPrimeLayer
            (trackBLinearPrimeExpScheduleSpec.freshLo j r)
            (trackBLinearPrimeExpScheduleSpec.freshHi j r),
            core.roughCoeff omega j r p ^ 2) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
      core where
  badRough := fun _ _ => ∅
  rough_bad_subset := by
    intro j r hr _hmean omega hbad
    exact False.elim ((not_lt_of_ge (hrough omega j r hr)) hbad)
  rough_bad_event_real_le := by
    intro j r _hr _hmean
    simp [trackBLinearPrimeExp_productRoughTailBudget_nonneg j]

/-- Event-witness `V_j` error-tail record from a pointwise error-energy upper
bound. -/
def trackBLinearPrimeExpVErrorTailEventRealFacts_of_pointwise
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (herror :
      ∀ omega j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
        (∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          core.errorCoeff omega j r p ^ 2) ≤ trackBLinearPrimeExpScheduleSpec.V j) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
      core where
  badError := fun _ _ => ∅
  error_V_bad_subset := by
    intro j r hr _hmean omega hbad
    exact False.elim ((not_lt_of_ge (herror omega j r hr)) hbad)
  error_V_bad_event_real_le := by
    intro j r _hr _hmean
    simp [trackBLinearPrimeExp_productRoughTailBudget_nonneg j]

/-- If the product/rough core has no random mass bad event, the mass-tail event
record is automatic.  Deterministic Mertens or sieve inputs should be supplied
outside this probability field. -/
def trackBLinearPrimeExpProductRoughMassTailEventRealFacts_of_empty
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (hbad : ∀ j r, core.badMass j r = ∅) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts core where
  badMass := fun _ _ => ∅
  mass_bad_subset := by
    intro j r _hr _hmean
    simp [hbad j r]
  mass_bad_event_real_le := by
    intro j r _hr _hmean
    have hbase_nonneg : (0 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
      exact_mod_cast Nat.zero_le (trackBLinearPrimeConcreteBase j)
    have hnonneg : 0 ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹ := by
      exact inv_nonneg.mpr (pow_nonneg hbase_nonneg 14)
    simp [hnonneg]

/-- Fixed-floor convenience form of the empty-mass Packet C adapter. -/
def trackBLinearPrimeExpFixedFloorMassTailEventRealFacts_of_empty
    (fixedCore : TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts)
    (hbad : ∀ j r, fixedCore.badMass j r = ∅) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts
      (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore) :=
  trackBLinearPrimeExpProductRoughMassTailEventRealFacts_of_empty
    (core := trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore)
    (by
      intro j r
      simpa [trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor] using
        hbad j r)

/-- Convert an event-witness small-prime product estimate to the canonical tail
record. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts_of_event
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (h :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        core) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts core where
  small_bad_real_le := by
    intro j r hr hmean
    exact (measureReal_mono (h.small_bad_subset j r hr hmean)).trans
      (h.small_bad_event_real_le j r hr hmean)

/-- Convert an event-witness rough sampled-energy estimate to the canonical
tail record. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts_of_event
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (h :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        core) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts core where
  rough_bad_real_le := by
    intro j r hr hmean
    exact (measureReal_mono (h.rough_bad_subset j r hr hmean)).trans
      (h.rough_bad_event_real_le j r hr hmean)

/-- Convert an event-witness `V_j` error estimate to the canonical tail
record. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts_of_event
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (h :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        core) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts core where
  error_V_bad_real_le := by
    intro j r hr hmean
    exact (measureReal_mono (h.error_V_bad_subset j r hr hmean)).trans
      (h.error_V_bad_event_real_le j r hr hmean)

/-- Convert an event-witness mass/boundary estimate to the canonical tail
record. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts_of_event
    {core :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts}
    (h :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts
        core) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts core where
  mass_bad_real_le := by
    intro j r hr hmean
    exact (measureReal_mono (h.mass_bad_subset j r hr hmean)).trans
      (h.mass_bad_event_real_le j r hr hmean)

/-- Assemble separately proved deterministic, small-tail, rough-tail,
`V_j`-error-tail, and mass-tail inputs into the product/rough package consumed
by the existing Lean route. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts_of_pieces
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts core) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts where
  badMass := core.badMass
  signalCoeff := core.signalCoeff
  errorCoeff := core.errorCoeff
  smallFactor := core.smallFactor
  roughCoeff := core.roughCoeff
  smallFloor := core.smallFloor
  roughFloor := core.roughFloor
  coeff_eq_signal_add_error := core.coeff_eq_signal_add_error
  signal_eq_small_mul_rough := core.signal_eq_small_mul_rough
  smallFloor_nonneg := core.smallFloor_nonneg
  product_floor_ge_four_V := core.product_floor_ge_four_V
  small_bad_real_le := hsmall.small_bad_real_le
  rough_bad_real_le := hrough.rough_bad_real_le
  error_V_bad_real_le := herror.error_V_bad_real_le
  mass_bad_real_le := hmass.mass_bad_real_le

/-- Assemble product/rough `V_j` facts when all four tail estimates are first
proved through convenient bad events containing the canonical threshold
failures. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts_of_eventPieces
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts core) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts :=
  trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts_of_pieces
    core
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts_of_event
      hsmall)
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts_of_event
      hrough)
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts_of_event
      herror)
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts_of_event
      hmass)

/-- The canonical `V_j` error budget supplies the separate error-budget package. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughErrorBudgetRealFacts_of_vError
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughErrorBudgetRealFacts where
  badMass := h.badMass
  signalCoeff := h.signalCoeff
  errorCoeff := h.errorCoeff
  smallFactor := h.smallFactor
  roughCoeff := h.roughCoeff
  smallFloor := h.smallFloor
  roughFloor := h.roughFloor
  errorBudget := fun j _r => trackBLinearPrimeExpScheduleSpec.V j
  coeff_eq_signal_add_error := h.coeff_eq_signal_add_error
  signal_eq_small_mul_rough := h.signal_eq_small_mul_rough
  smallFloor_nonneg := h.smallFloor_nonneg
  product_floor_ge_four_V := h.product_floor_ge_four_V
  error_budget_le_product_floor := h.product_floor_ge_four_V
  small_bad_real_le := h.small_bad_real_le
  rough_bad_real_le := h.rough_bad_real_le
  error_budget_bad_real_le := h.error_V_bad_real_le
  mass_bad_real_le := h.mass_bad_real_le

/-- A separate error-energy budget supplies the real-probability threshold
package by monotonicity of the error bad event. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdRealFacts_of_errorBudget
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughErrorBudgetRealFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdRealFacts where
  badMass := h.badMass
  signalCoeff := h.signalCoeff
  errorCoeff := h.errorCoeff
  smallFactor := h.smallFactor
  roughCoeff := h.roughCoeff
  smallFloor := h.smallFloor
  roughFloor := h.roughFloor
  coeff_eq_signal_add_error := h.coeff_eq_signal_add_error
  signal_eq_small_mul_rough := h.signal_eq_small_mul_rough
  smallFloor_nonneg := h.smallFloor_nonneg
  product_floor_ge_four_V := h.product_floor_ge_four_V
  small_bad_real_le := h.small_bad_real_le
  rough_bad_real_le := h.rough_bad_real_le
  error_bad_real_le := by
    intro j r hr hmean
    let fresh := trackBFreshPrimeLayer
      (trackBLinearPrimeExpScheduleSpec.freshLo j r)
      (trackBLinearPrimeExpScheduleSpec.freshHi j r)
    have hsubset :
        {omega |
          h.smallFloor j * h.roughFloor j r <
            4 * (∑ p ∈ fresh, h.errorCoeff omega j r p ^ 2)} ⊆
          {omega |
            h.errorBudget j r <
              ∑ p ∈ fresh, h.errorCoeff omega j r p ^ 2} := by
      intro omega homega
      have hbudget := h.error_budget_le_product_floor j r hr hmean
      have hfour :
          4 * h.errorBudget j r <
            4 * (∑ p ∈ fresh, h.errorCoeff omega j r p ^ 2) :=
        lt_of_le_of_lt hbudget homega
      exact lt_of_mul_lt_mul_left hfour (by norm_num : (0 : ℝ) ≤ 4)
    exact (measureReal_mono hsubset).trans
      (by simpa [fresh] using h.error_budget_bad_real_le j r hr hmean)
  mass_bad_real_le := h.mass_bad_real_le

/-- Real-probability threshold facts supply the `ENNReal` threshold package. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdFacts_of_real
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdRealFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdFacts where
  badMass := h.badMass
  signalCoeff := h.signalCoeff
  errorCoeff := h.errorCoeff
  smallFactor := h.smallFactor
  roughCoeff := h.roughCoeff
  smallFloor := h.smallFloor
  roughFloor := h.roughFloor
  coeff_eq_signal_add_error := h.coeff_eq_signal_add_error
  signal_eq_small_mul_rough := h.signal_eq_small_mul_rough
  smallFloor_nonneg := h.smallFloor_nonneg
  product_floor_ge_four_V := h.product_floor_ge_four_V
  small_bad_le := by
    intro j r hr hmean
    exact trackBLinearPrimeExp_measure_le_of_real_le (h.small_bad_real_le j r hr hmean)
  rough_bad_le := by
    intro j r hr hmean
    exact trackBLinearPrimeExp_measure_le_of_real_le (h.rough_bad_real_le j r hr hmean)
  error_bad_le := by
    intro j r hr hmean
    exact trackBLinearPrimeExp_measure_le_of_real_le (h.error_bad_real_le j r hr hmean)
  mass_bad_le := by
    intro j r hr hmean
    exact trackBLinearPrimeExp_measure_le_of_real_le (h.mass_bad_real_le j r hr hmean)

/-- Canonical threshold bad events supply the product/rough signal-factor
contract. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSignalFacts_of_threshold
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSignalFacts where
  badSmall := fun j r => {omega | h.smallFactor omega j ^ 2 < h.smallFloor j}
  badRough := fun j r =>
    {omega |
      (∑ p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r),
        h.roughCoeff omega j r p ^ 2) < h.roughFloor j r}
  badError := fun j r =>
    {omega |
      h.smallFloor j * h.roughFloor j r <
        4 * (∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          h.errorCoeff omega j r p ^ 2)}
  badMass := h.badMass
  signalCoeff := h.signalCoeff
  errorCoeff := h.errorCoeff
  smallFactor := h.smallFactor
  roughCoeff := h.roughCoeff
  smallFloor := h.smallFloor
  roughFloor := h.roughFloor
  coeff_eq_signal_add_error := h.coeff_eq_signal_add_error
  signal_eq_small_mul_rough := h.signal_eq_small_mul_rough
  smallFloor_nonneg := h.smallFloor_nonneg
  small_floor_le_sq := by
    intro omega j r hr hmean hsmall hmass
    exact not_lt.mp hsmall
  rough_floor_le_energy := by
    intro omega j r hr hmean hrough hmass
    exact not_lt.mp hrough
  product_floor_ge_four_V := h.product_floor_ge_four_V
  error_energy_le_product_floor := by
    intro omega j r hr hmean hsmall hrough herror hmass
    exact not_lt.mp herror
  small_bad_le := h.small_bad_le
  rough_bad_le := h.rough_bad_le
  error_bad_le := h.error_bad_le
  mass_bad_le := h.mass_bad_le

/-- Separate small-factor and rough-energy lower bounds imply the factorized
product/rough floor contract. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughFloorFacts_of_prodSignal
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSignalFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughFloorFacts where
  badSmall := h.badSmall
  badRough := h.badRough
  badError := h.badError
  badMass := h.badMass
  signalCoeff := h.signalCoeff
  errorCoeff := h.errorCoeff
  smallFloor := h.smallFloor
  roughFloor := h.roughFloor
  coeff_eq_signal_add_error := h.coeff_eq_signal_add_error
  product_floor_le_signal_energy := by
    intro omega j r hr hmean hsmall hrough hmass
    let fresh := trackBFreshPrimeLayer
      (trackBLinearPrimeExpScheduleSpec.freshLo j r)
      (trackBLinearPrimeExpScheduleSpec.freshHi j r)
    let a := h.smallFactor omega j
    let B : ℕ → ℝ := fun p => h.roughCoeff omega j r p
    have hsmallFloor : h.smallFloor j ≤ a ^ 2 := by
      simpa [a] using h.small_floor_le_sq omega j r hr hmean hsmall hmass
    have hroughFloor : h.roughFloor j r ≤ ∑ p ∈ fresh, B p ^ 2 := by
      simpa [fresh, B] using h.rough_floor_le_energy omega j r hr hmean hrough hmass
    have hroughNonneg : 0 ≤ ∑ p ∈ fresh, B p ^ 2 := by
      exact Finset.sum_nonneg fun p hp => sq_nonneg (B p)
    have hmul :
        h.smallFloor j * h.roughFloor j r ≤ a ^ 2 * (∑ p ∈ fresh, B p ^ 2) := by
      exact (mul_le_mul_of_nonneg_left hroughFloor (h.smallFloor_nonneg j)).trans
        (mul_le_mul_of_nonneg_right hsmallFloor hroughNonneg)
    have hsum :
        ∑ p ∈ fresh, h.signalCoeff omega j r p ^ 2 =
          a ^ 2 * (∑ p ∈ fresh, B p ^ 2) := by
      calc
        ∑ p ∈ fresh, h.signalCoeff omega j r p ^ 2 =
            ∑ p ∈ fresh, (a * B p) ^ 2 := by
              apply Finset.sum_congr rfl
              intro p hp
              dsimp [a, B]
              rw [h.signal_eq_small_mul_rough omega j r p hr]
              exact hp
        _ = ∑ p ∈ fresh, a ^ 2 * B p ^ 2 := by
              apply Finset.sum_congr rfl
              intro p hp
              ring
        _ = a ^ 2 * (∑ p ∈ fresh, B p ^ 2) := by
              rw [← Finset.mul_sum]
    exact hmul.trans_eq hsum.symm
  product_floor_ge_four_V := h.product_floor_ge_four_V
  error_energy_le_product_floor := h.error_energy_le_product_floor
  small_bad_le := h.small_bad_le
  rough_bad_le := h.rough_bad_le
  error_bad_le := h.error_bad_le
  mass_bad_le := h.mass_bad_le

/-- Product/rough floors provide the common-floor contract by taking
`energyFloor(j,r) = smallFloor(j) * roughFloor(j,r)`. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationEnergyFloorFacts_of_productRoughFloor
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughFloorFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationEnergyFloorFacts where
  badSmall := h.badSmall
  badRough := h.badRough
  badError := h.badError
  badMass := h.badMass
  signalCoeff := h.signalCoeff
  errorCoeff := h.errorCoeff
  energyFloor := fun j r => h.smallFloor j * h.roughFloor j r
  coeff_eq_signal_add_error := h.coeff_eq_signal_add_error
  signal_floor_le_energy := h.product_floor_le_signal_energy
  floor_ge_four_V := h.product_floor_ge_four_V
  error_energy_le_floor := h.error_energy_le_product_floor
  small_bad_le := h.small_bad_le
  rough_bad_le := h.rough_bad_le
  error_bad_le := h.error_bad_le
  mass_bad_le := h.mass_bad_le

/-- A common floor below signal energy and above four times the error energy
supplies the signal/error decomposition contract. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationEnergyDecompositionFacts_of_energyFloor
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationEnergyFloorFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationEnergyDecompositionFacts where
  badSmall := h.badSmall
  badRough := h.badRough
  badError := h.badError
  badMass := h.badMass
  signalCoeff := h.signalCoeff
  errorCoeff := h.errorCoeff
  coeff_eq_signal_add_error := h.coeff_eq_signal_add_error
  signal_energy_lower := by
    intro omega j r hr hmean hsmall hrough hmass
    exact (h.floor_ge_four_V j r hr hmean).trans
      (h.signal_floor_le_energy omega j r hr hmean hsmall hrough hmass)
  error_energy_le := by
    intro omega j r hr hmean hsmall hrough herror hmass
    exact (h.error_energy_le_floor omega j r hr hmean hsmall hrough herror hmass).trans
      (h.signal_floor_le_energy omega j r hr hmean hsmall hrough hmass)
  small_bad_le := h.small_bad_le
  rough_bad_le := h.rough_bad_le
  error_bad_le := h.error_bad_le
  mass_bad_le := h.mass_bad_le

/-- Signal/error energy estimates imply the four-bad-event variance
concentration contract. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_energyDecomposition
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationEnergyDecompositionFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts where
  badSmall := h.badSmall
  badRough := h.badRough
  badError := h.badError
  badMass := h.badMass
  variance_bad_subset := by
    intro j r hr hmean omega homega
    by_cases hsmall : omega ∈ h.badSmall j r
    · exact Or.inl (Or.inl (Or.inl hsmall))
    by_cases hrough : omega ∈ h.badRough j r
    · exact Or.inl (Or.inl (Or.inr hrough))
    by_cases herror : omega ∈ h.badError j r
    · exact Or.inl (Or.inr herror)
    by_cases hmass : omega ∈ h.badMass j r
    · exact Or.inr hmass
    have hsignal := h.signal_energy_lower omega j r hr hmean hsmall hrough hmass
    have herrorEnergy := h.error_energy_le omega j r hr hmean hsmall hrough herror hmass
    let fresh := trackBFreshPrimeLayer
      (trackBLinearPrimeExpScheduleSpec.freshLo j r)
      (trackBLinearPrimeExpScheduleSpec.freshHi j r)
    let exactCoeff : ℕ → ℝ := fun p =>
      trackBLinearPrimeScheduledFreshCoeff
        trackBLinearPrimeExpScheduleSpec.Q
        trackBLinearPrimeExpScheduleSpec.point
        trackBLinearPrimeExpScheduleSpec.freshLo
        trackBLinearPrimeExpScheduleSpec.freshHi
        omega j (trackBLinearPrimeExpScheduleSpec.point j r) p
    let A : ℕ → ℝ := fun p => h.signalCoeff omega j r p
    let E : ℕ → ℝ := fun p => h.errorCoeff omega j r p
    have hdecomp : ∑ p ∈ fresh, exactCoeff p ^ 2 = ∑ p ∈ fresh, (A p + E p) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [exactCoeff, A, E]
      rw [h.coeff_eq_signal_add_error omega j r p hr]
      exact hp
    have hlower := sum_sq_add_lower_of_four_error_energy_le_signal_energy fresh A E (by
      simpa [fresh, A, E] using herrorEnergy)
    have hV_le_quarter :
        trackBLinearPrimeExpScheduleSpec.V j ≤
          (1 / 4 : ℝ) * (∑ p ∈ fresh, A p ^ 2) := by
      have hs : 4 * trackBLinearPrimeExpScheduleSpec.V j ≤ ∑ p ∈ fresh, A p ^ 2 := by
        simpa [fresh, A] using hsignal
      nlinarith
    have hV_le_exact :
        trackBLinearPrimeExpScheduleSpec.V j ≤ ∑ p ∈ fresh, exactCoeff p ^ 2 := by
      calc
        trackBLinearPrimeExpScheduleSpec.V j ≤
            (1 / 4 : ℝ) * (∑ p ∈ fresh, A p ^ 2) := hV_le_quarter
        _ ≤ ∑ p ∈ fresh, (A p + E p) ^ 2 := hlower
        _ = ∑ p ∈ fresh, exactCoeff p ^ 2 := hdecomp.symm
    exact False.elim
      ((not_lt_of_ge
        (by simpa [trackBLinearPrimeExpVarianceLayerBadSet, fresh, exactCoeff] using hV_le_exact))
        homega)
  small_bad_le := h.small_bad_le
  rough_bad_le := h.rough_bad_le
  error_bad_le := h.error_bad_le
  mass_bad_le := h.mass_bad_le

/-- Common-floor signal/error estimates imply the four-bad-event variance
concentration contract. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_energyFloor
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationEnergyFloorFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts :=
  trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_energyDecomposition
    (trackBLinearPrimeExpGeometryVarianceConcentrationEnergyDecompositionFacts_of_energyFloor h)

/-- Product/rough floors imply the four-bad-event variance concentration
contract. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_productRoughFloor
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughFloorFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts :=
  trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_energyFloor
    (trackBLinearPrimeExpGeometryVarianceConcentrationEnergyFloorFacts_of_productRoughFloor h)

/-- Product/rough signal-factor estimates imply the four-bad-event variance
concentration contract. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_prodSignal
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSignalFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts :=
  trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_productRoughFloor
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughFloorFacts_of_prodSignal h)

/-- Product/rough threshold facts imply the four-bad-event variance
concentration contract. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_prodThreshold
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts :=
  trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_prodSignal
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSignalFacts_of_threshold h)

/-- Product/rough threshold facts with real probability bounds imply the
four-bad-event variance concentration contract. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_prodThresholdReal
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdRealFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts :=
  trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_prodThreshold
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdFacts_of_real h)

/-- Product/rough error-budget real-probability facts imply the four-bad-event
variance concentration contract. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_prodErrorBudgetReal
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughErrorBudgetRealFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts :=
  trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_prodThresholdReal
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdRealFacts_of_errorBudget
      h)

/-- Product/rough real-probability facts with the canonical `V_j` error budget
imply the four-bad-event variance concentration contract. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_prodVErrorReal
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts :=
  trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_prodErrorBudgetReal
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughErrorBudgetRealFacts_of_vError
      h)

/-- Four named product/rough bad events with `base^-14` budgets imply the
fourteenth concentration wrapper by a union bound. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationFourteenthFacts_of_fourEvents
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationFourteenthFacts where
  variance_concentration_fourteenth := by
    intro j r hr hmean
    let eps : ℝ≥0∞ := ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)
    have hAB : mu (h.badSmall j r ∪ h.badRough j r) ≤ eps + eps := by
      calc
        mu (h.badSmall j r ∪ h.badRough j r) ≤
            mu (h.badSmall j r) + mu (h.badRough j r) := measure_union_le _ _
        _ ≤ eps + eps := add_le_add (h.small_bad_le j r hr hmean)
          (h.rough_bad_le j r hr hmean)
    have hABC :
        mu (h.badSmall j r ∪ h.badRough j r ∪ h.badError j r) ≤ eps + eps + eps := by
      calc
        mu ((h.badSmall j r ∪ h.badRough j r) ∪ h.badError j r) ≤
            mu (h.badSmall j r ∪ h.badRough j r) + mu (h.badError j r) :=
          measure_union_le _ _
        _ ≤ (eps + eps) + eps := add_le_add hAB (h.error_bad_le j r hr hmean)
    have hABCD :
        mu (h.badSmall j r ∪ h.badRough j r ∪ h.badError j r ∪ h.badMass j r) ≤
          eps + eps + eps + eps := by
      calc
        mu (((h.badSmall j r ∪ h.badRough j r) ∪ h.badError j r) ∪ h.badMass j r) ≤
            mu (h.badSmall j r ∪ h.badRough j r ∪ h.badError j r) +
              mu (h.badMass j r) := measure_union_le _ _
        _ ≤ (eps + eps + eps) + eps := add_le_add hABC (h.mass_bad_le j r hr hmean)
    have hfour :
        eps + eps + eps + eps =
          ENNReal.ofReal (4 * ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)) := by
      rw [← ENNReal.ofReal_add, ← ENNReal.ofReal_add, ← ENNReal.ofReal_add]
      · ring_nf
      all_goals positivity
    calc
      mu (trackBLinearPrimeExpVarianceLayerBadSet j r) ≤
          mu (h.badSmall j r ∪ h.badRough j r ∪ h.badError j r ∪ h.badMass j r) :=
        measure_mono (h.variance_bad_subset j r hr hmean)
      _ ≤ eps + eps + eps + eps := hABCD
      _ = ENNReal.ofReal (4 * ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 14))⁻¹)) := hfour

/-- Four `base^-14` bad-event budgets imply the standard variance concentration
input. -/
def trackBLinearPrimeExpGeometryVarianceConcentrationFacts_of_fourteenth
    (h : TrackBLinearPrimeExpGeometryVarianceConcentrationFourteenthFacts) :
    TrackBLinearPrimeExpGeometryVarianceConcentrationFacts where
  variance_concentration := by
    intro j r hr hmean
    exact (h.variance_concentration_fourteenth j r hr hmean).trans
      (trackBLinearPrimeExp_four_inv_base_pow_fourteen_le_variancePointBudget j r)

/-- Analytic route that separates deterministic expected-mass lower bounds
from the actual lower-tail concentration theorem.  The concentration field is
allowed to use the deterministic mass lower bound as a hypothesis, matching the
paper-side plan in the small-ball workbench. -/
structure TrackBLinearPrimeExpGeometryMeanConcentrationFacts where
  mean_lower : TrackBLinearPrimeExpLayerMeanLowerFacts
  variance_concentration :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤
        trackBLinearPrimeExpLayerWeightedSupportMass j r →
      mu (trackBLinearPrimeExpVarianceLayerBadSet j r) ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r
  flatness_compl :
    ∀ j, mu (trackBLinearPrimeExpFlatGoodCompl j) ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Add deterministic mean and compact flatness estimates to a separated
variance-concentration theorem. -/
def trackBLinearPrimeExpGeometryMeanConcentrationFacts_of_varianceConcentration
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationFacts)
    (hflat :
      ∀ j, mu (trackBLinearPrimeExpFlatGoodCompl j) ≤
        trackBLinearPrimeExpGeometryFlatBudget j) :
    TrackBLinearPrimeExpGeometryMeanConcentrationFacts where
  mean_lower := hmean
  variance_concentration := hvar.variance_concentration
  flatness_compl := hflat

/-- Add deterministic mean and real-valued layer flatness tails to a separated
variance-concentration theorem. -/
def trackBLinearPrimeExpGeometryMeanConcentrationFacts_of_varianceConcentration_realProbability
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryMeanConcentrationFacts :=
  trackBLinearPrimeExpGeometryMeanConcentrationFacts_of_varianceConcentration
    hmean hvar
    (measure_trackBLinearPrimeExpFlatGood_compl_le_of_layerProbabilityFacts
      (trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_realProbability hflat))

/-- Centered-second-moment route to the layer variance small-ball estimate.
This is a Chebyshev-facing concentration interface for `Vhat`: once the mean is
at least `2 * V_j`, a centered second moment at scale `V_j^2 * base^-12`
implies the required lower-tail probability. -/
structure TrackBLinearPrimeExpGeometryCenteredSecondFacts where
  mean_lower : TrackBLinearPrimeExpLayerMeanLowerFacts
  centeredSecond : ℕ → ℕ → ℝ
  centeredSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
            ∫ omega,
              trackBLinearPrimeExpScheduledVariance
                omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2)
        mu
  centeredSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
          ∫ omega,
            trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2 ∂mu) ≤
        centeredSecond j r
  centeredSecond_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      ENNReal.ofReal
          (4 * centeredSecond j r / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2) ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r
  flatness_compl :
    ∀ j, mu (trackBLinearPrimeExpFlatGoodCompl j) ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Raw-second-moment route to the layer variance small-ball estimate.  This
matches the usual fourth-moment calculation for `Vhat`: prove an upper bound on
`E[Vhat^2]`, and Lean converts it to the centered-second input with the robust
`centered_second_le_four_raw_second` inequality. -/
structure TrackBLinearPrimeExpGeometryRawSecondFacts where
  mean_lower : TrackBLinearPrimeExpLayerMeanLowerFacts
  rawSecond : ℕ → ℕ → ℝ
  rawSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2)
        mu
  rawSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
          omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2 ∂mu) ≤
        rawSecond j r
  rawSecond_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      ENNReal.ofReal
          (4 * (4 * rawSecond j r) / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2) ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r
  flatness_compl :
    ∀ j, mu (trackBLinearPrimeExpFlatGoodCompl j) ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Real-budget version of the centered-second route.  This is often easier to
use in analytic estimates: prove the scalar Chebyshev budget as a real
inequality, then convert to the `ENNReal` probability package. -/
structure TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetFacts where
  mean_lower : TrackBLinearPrimeExpLayerMeanLowerFacts
  centeredSecond : ℕ → ℕ → ℝ
  centeredSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
            ∫ omega,
              trackBLinearPrimeExpScheduledVariance
                omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2)
        mu
  centeredSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
          ∫ omega,
            trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2 ∂mu) ≤
        centeredSecond j r
  centeredSecond_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * centeredSecond j r / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r
  flatness_compl :
    ∀ j, mu (trackBLinearPrimeExpFlatGoodCompl j) ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Centered-second route with an explicit deterministic mean floor.  This is
useful when the analytic estimate proves a much larger mean than `2 * V_j`:
Chebyshev can then use the larger floor in the denominator instead of the
minimal `2 * V_j` lower bound. -/
structure TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetFacts where
  meanFloor : ℕ → ℕ → ℝ
  mean_floor_ge_two_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤ meanFloor j r
  mean_floor_le_mean :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      meanFloor j r ≤ trackBLinearPrimeExpLayerWeightedSupportMass j r
  centeredSecond : ℕ → ℕ → ℝ
  centeredSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
            ∫ omega,
              trackBLinearPrimeExpScheduledVariance
                omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2)
        mu
  centeredSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
          ∫ omega,
            trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2 ∂mu) ≤
        centeredSecond j r
  centeredSecond_mean_floor_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * centeredSecond j r / (meanFloor j r) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r
  flatness_compl :
    ∀ j, mu (trackBLinearPrimeExpFlatGoodCompl j) ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Raw-second version of the explicit mean-floor route.  This is the
fourth-moment-facing analogue of
`TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetFacts`: prove an
upper bound for `E[Vhat^2]`, then Lean converts it to a centered-second
estimate while preserving the larger mean-floor denominator. -/
structure TrackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetFacts where
  meanFloor : ℕ → ℕ → ℝ
  mean_floor_ge_two_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤ meanFloor j r
  mean_floor_le_mean :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      meanFloor j r ≤ trackBLinearPrimeExpLayerWeightedSupportMass j r
  rawSecond : ℕ → ℕ → ℝ
  rawSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2)
        mu
  rawSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
          omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2 ∂mu) ≤
        rawSecond j r
  rawSecond_mean_floor_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * (4 * rawSecond j r) / (meanFloor j r) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r
  flatness_compl :
    ∀ j, mu (trackBLinearPrimeExpFlatGoodCompl j) ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Explicit mean-floor centered-second route with flatness supplied by
layer-indexed one-coefficient tails. -/
structure TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetLayerFlatnessFacts where
  meanFloor : ℕ → ℕ → ℝ
  mean_floor_ge_two_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤ meanFloor j r
  mean_floor_le_mean :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      meanFloor j r ≤ trackBLinearPrimeExpLayerWeightedSupportMass j r
  centeredSecond : ℕ → ℕ → ℝ
  centeredSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
            ∫ omega,
              trackBLinearPrimeExpScheduledVariance
                omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2)
        mu
  centeredSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
          ∫ omega,
            trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2 ∂mu) ≤
        centeredSecond j r
  centeredSecond_mean_floor_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * centeredSecond j r / (meanFloor j r) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r
  flatness_layer : TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts

/-- Explicit mean-floor raw-second route with flatness supplied by layer-indexed
one-coefficient tails. -/
structure TrackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetLayerFlatnessFacts where
  meanFloor : ℕ → ℕ → ℝ
  mean_floor_ge_two_V :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      2 * trackBLinearPrimeExpScheduleSpec.V j ≤ meanFloor j r
  mean_floor_le_mean :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      meanFloor j r ≤ trackBLinearPrimeExpLayerWeightedSupportMass j r
  rawSecond : ℕ → ℕ → ℝ
  rawSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2)
        mu
  rawSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
          omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2 ∂mu) ≤
        rawSecond j r
  rawSecond_mean_floor_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * (4 * rawSecond j r) / (meanFloor j r) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r
  flatness_layer : TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts

/-- Estimates-only centered-second mean-floor package.  The deterministic
mean-floor package is supplied separately, so sieve mass estimates can be kept
independent from concentration and flatness estimates. -/
structure TrackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessEstimates
    (meanFloor : ℕ → ℕ → ℝ) where
  centeredSecond : ℕ → ℕ → ℝ
  centeredSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
            ∫ omega,
              trackBLinearPrimeExpScheduledVariance
                omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2)
        mu
  centeredSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
          ∫ omega,
            trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2 ∂mu) ≤
        centeredSecond j r
  centeredSecond_mean_floor_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * centeredSecond j r / (meanFloor j r) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r
  flatness_layer : TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts

/-- Estimates-only raw-second mean-floor package. -/
structure TrackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessEstimates
    (meanFloor : ℕ → ℕ → ℝ) where
  rawSecond : ℕ → ℕ → ℝ
  rawSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2)
        mu
  rawSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
          omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2 ∂mu) ≤
        rawSecond j r
  rawSecond_mean_floor_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * (4 * rawSecond j r) / (meanFloor j r) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r
  flatness_layer : TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts

/-- Variance-only centered-second estimates against a retained deterministic
mean floor.  Coefficient flatness is supplied separately. -/
structure TrackBLinearPrimeExpGeometryCenteredMeanFloorRealBudgetEstimates
    (meanFloor : ℕ → ℕ → ℝ) where
  centeredSecond : ℕ → ℕ → ℝ
  centeredSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
            ∫ omega,
              trackBLinearPrimeExpScheduledVariance
                omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2)
        mu
  centeredSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
          ∫ omega,
            trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2 ∂mu) ≤
        centeredSecond j r
  centeredSecond_mean_floor_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * centeredSecond j r / (meanFloor j r) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r

/-- Variance-only raw-second estimates against a retained deterministic mean
floor.  Coefficient flatness is supplied separately. -/
structure TrackBLinearPrimeExpGeometryRawMeanFloorRealBudgetEstimates
    (meanFloor : ℕ → ℕ → ℝ) where
  rawSecond : ℕ → ℕ → ℝ
  rawSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2)
        mu
  rawSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
          omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2 ∂mu) ≤
        rawSecond j r
  rawSecond_mean_floor_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * (4 * rawSecond j r) / (meanFloor j r) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r

/-- Real-budget version of the raw-second route. -/
structure TrackBLinearPrimeExpGeometryRawSecondRealBudgetFacts where
  mean_lower : TrackBLinearPrimeExpLayerMeanLowerFacts
  rawSecond : ℕ → ℕ → ℝ
  rawSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2)
        mu
  rawSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
          omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2 ∂mu) ≤
        rawSecond j r
  rawSecond_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * (4 * rawSecond j r) / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r
  flatness_compl :
    ∀ j, mu (trackBLinearPrimeExpFlatGoodCompl j) ≤
      trackBLinearPrimeExpGeometryFlatBudget j

/-- Real-budget centered-second route with flatness supplied by layer-indexed
one-coefficient tails.  This keeps both analytic halves in their smaller
scalar/layer-indexed forms. -/
structure TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessFacts where
  mean_lower : TrackBLinearPrimeExpLayerMeanLowerFacts
  centeredSecond : ℕ → ℕ → ℝ
  centeredSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
            ∫ omega,
              trackBLinearPrimeExpScheduledVariance
                omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2)
        mu
  centeredSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
          ∫ omega,
            trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2 ∂mu) ≤
        centeredSecond j r
  centeredSecond_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * centeredSecond j r / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r
  flatness_layer : TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts

/-- Real-budget raw-second route with flatness supplied by layer-indexed
one-coefficient tails. -/
structure TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessFacts where
  mean_lower : TrackBLinearPrimeExpLayerMeanLowerFacts
  rawSecond : ℕ → ℕ → ℝ
  rawSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2)
        mu
  rawSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
          omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2 ∂mu) ≤
        rawSecond j r
  rawSecond_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * (4 * rawSecond j r) / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r
  flatness_layer : TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts

/-- Estimates-only centered-second real-budget package, without any flatness
input.  This lets analytic work keep variance concentration separate from the
coefficient-flatness budget. -/
structure TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetEstimates where
  centeredSecond : ℕ → ℕ → ℝ
  centeredSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
            ∫ omega,
              trackBLinearPrimeExpScheduledVariance
                omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2)
        mu
  centeredSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
          ∫ omega,
            trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2 ∂mu) ≤
        centeredSecond j r
  centeredSecond_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * centeredSecond j r / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r

/-- Estimates-only raw-second real-budget package, without any flatness input. -/
structure TrackBLinearPrimeExpGeometryRawSecondRealBudgetEstimates where
  rawSecond : ℕ → ℕ → ℝ
  rawSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2)
        mu
  rawSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
          omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2 ∂mu) ≤
        rawSecond j r
  rawSecond_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * (4 * rawSecond j r) / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r

/-- Estimates-only centered-second real-budget package.  The deterministic
mean lower bound is supplied separately, so analytic work can keep reciprocal
mass estimates independent from variance/flatness estimates. -/
structure TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates where
  centeredSecond : ℕ → ℕ → ℝ
  centeredSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
            ∫ omega,
              trackBLinearPrimeExpScheduledVariance
                omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2)
        mu
  centeredSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
          ∫ omega,
            trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2 ∂mu) ≤
        centeredSecond j r
  centeredSecond_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * centeredSecond j r / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r
  flatness_layer : TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts

/-- Estimates-only raw-second real-budget package, with the deterministic mean
lower bound supplied separately. -/
structure TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates where
  rawSecond : ℕ → ℕ → ℝ
  rawSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2)
        mu
  rawSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
          omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2 ∂mu) ≤
        rawSecond j r
  rawSecond_real_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      4 * (4 * rawSecond j r) / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2 ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudgetReal j r
  flatness_layer : TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts

/-- Attach harmonic real-budget coefficient-flatness estimates to
centered-second real-budget variance estimates. -/
def trackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates_of_harmonic
    (hvar : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetEstimates)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates where
  centeredSecond := hvar.centeredSecond
  centeredSecond_integrable := hvar.centeredSecond_integrable
  centeredSecond_le := hvar.centeredSecond_le
  centeredSecond_real_budget := hvar.centeredSecond_real_budget
  flatness_layer :=
    trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_harmonicUpperRealBudget hflat

/-- Attach harmonic real-budget coefficient-flatness estimates to raw-second
real-budget variance estimates. -/
def trackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates_of_harmonic
    (hvar : TrackBLinearPrimeExpGeometryRawSecondRealBudgetEstimates)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates where
  rawSecond := hvar.rawSecond
  rawSecond_integrable := hvar.rawSecond_integrable
  rawSecond_le := hvar.rawSecond_le
  rawSecond_real_budget := hvar.rawSecond_real_budget
  flatness_layer :=
    trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_harmonicUpperRealBudget hflat

/-- Attach reciprocal-mass-upper real-budget coefficient-flatness estimates to
centered-second real-budget variance estimates. -/
def trackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates_of_reciprocal
    (hvar : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetEstimates)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates where
  centeredSecond := hvar.centeredSecond
  centeredSecond_integrable := hvar.centeredSecond_integrable
  centeredSecond_le := hvar.centeredSecond_le
  centeredSecond_real_budget := hvar.centeredSecond_real_budget
  flatness_layer :=
    trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_reciprocalMassUpperRealBudget hflat

/-- Attach reciprocal-mass-upper real-budget coefficient-flatness estimates to
raw-second real-budget variance estimates. -/
def trackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates_of_reciprocal
    (hvar : TrackBLinearPrimeExpGeometryRawSecondRealBudgetEstimates)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates where
  rawSecond := hvar.rawSecond
  rawSecond_integrable := hvar.rawSecond_integrable
  rawSecond_le := hvar.rawSecond_le
  rawSecond_real_budget := hvar.rawSecond_real_budget
  flatness_layer :=
    trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_reciprocalMassUpperRealBudget hflat

/-- Attach arbitrary real-valued coefficient-flatness tail estimates to
centered-second real-budget variance estimates. -/
def trackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates_of_realProbability
    (hvar : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetEstimates)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates where
  centeredSecond := hvar.centeredSecond
  centeredSecond_integrable := hvar.centeredSecond_integrable
  centeredSecond_le := hvar.centeredSecond_le
  centeredSecond_real_budget := hvar.centeredSecond_real_budget
  flatness_layer :=
    trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_realProbability hflat

/-- Attach arbitrary real-valued coefficient-flatness tail estimates to
raw-second real-budget variance estimates. -/
def trackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates_of_realProbability
    (hvar : TrackBLinearPrimeExpGeometryRawSecondRealBudgetEstimates)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates where
  rawSecond := hvar.rawSecond
  rawSecond_integrable := hvar.rawSecond_integrable
  rawSecond_le := hvar.rawSecond_le
  rawSecond_real_budget := hvar.rawSecond_real_budget
  flatness_layer :=
    trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_realProbability hflat

/-- Attach harmonic real-budget coefficient-flatness estimates to centered-second
mean-floor variance estimates. -/
def trackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessEstimates_of_harmonic
    {meanFloor : ℕ → ℕ → ℝ}
    (hvar : TrackBLinearPrimeExpGeometryCenteredMeanFloorRealBudgetEstimates meanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessEstimates meanFloor where
  centeredSecond := hvar.centeredSecond
  centeredSecond_integrable := hvar.centeredSecond_integrable
  centeredSecond_le := hvar.centeredSecond_le
  centeredSecond_mean_floor_real_budget := hvar.centeredSecond_mean_floor_real_budget
  flatness_layer :=
    trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_harmonicUpperRealBudget hflat

/-- Attach harmonic real-budget coefficient-flatness estimates to raw-second
mean-floor variance estimates. -/
def trackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessEstimates_of_harmonic
    {meanFloor : ℕ → ℕ → ℝ}
    (hvar : TrackBLinearPrimeExpGeometryRawMeanFloorRealBudgetEstimates meanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessEstimates meanFloor where
  rawSecond := hvar.rawSecond
  rawSecond_integrable := hvar.rawSecond_integrable
  rawSecond_le := hvar.rawSecond_le
  rawSecond_mean_floor_real_budget := hvar.rawSecond_mean_floor_real_budget
  flatness_layer :=
    trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_harmonicUpperRealBudget hflat

/-- Attach reciprocal-mass-upper real-budget coefficient-flatness estimates to
centered-second mean-floor variance estimates. -/
def trackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessEstimates_of_reciprocal
    {meanFloor : ℕ → ℕ → ℝ}
    (hvar : TrackBLinearPrimeExpGeometryCenteredMeanFloorRealBudgetEstimates meanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessEstimates meanFloor where
  centeredSecond := hvar.centeredSecond
  centeredSecond_integrable := hvar.centeredSecond_integrable
  centeredSecond_le := hvar.centeredSecond_le
  centeredSecond_mean_floor_real_budget := hvar.centeredSecond_mean_floor_real_budget
  flatness_layer :=
    trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_reciprocalMassUpperRealBudget hflat

/-- Attach reciprocal-mass-upper real-budget coefficient-flatness estimates to
raw-second mean-floor variance estimates. -/
def trackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessEstimates_of_reciprocal
    {meanFloor : ℕ → ℕ → ℝ}
    (hvar : TrackBLinearPrimeExpGeometryRawMeanFloorRealBudgetEstimates meanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessEstimates meanFloor where
  rawSecond := hvar.rawSecond
  rawSecond_integrable := hvar.rawSecond_integrable
  rawSecond_le := hvar.rawSecond_le
  rawSecond_mean_floor_real_budget := hvar.rawSecond_mean_floor_real_budget
  flatness_layer :=
    trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_reciprocalMassUpperRealBudget hflat

/-- Attach arbitrary real-valued coefficient-flatness tail estimates to
centered-second mean-floor variance estimates. -/
def trackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessEstimates_of_realProbability
    {meanFloor : ℕ → ℕ → ℝ}
    (hvar : TrackBLinearPrimeExpGeometryCenteredMeanFloorRealBudgetEstimates meanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessEstimates meanFloor where
  centeredSecond := hvar.centeredSecond
  centeredSecond_integrable := hvar.centeredSecond_integrable
  centeredSecond_le := hvar.centeredSecond_le
  centeredSecond_mean_floor_real_budget := hvar.centeredSecond_mean_floor_real_budget
  flatness_layer :=
    trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_realProbability hflat

/-- Attach arbitrary real-valued coefficient-flatness tail estimates to
raw-second mean-floor variance estimates. -/
def trackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessEstimates_of_realProbability
    {meanFloor : ℕ → ℕ → ℝ}
    (hvar : TrackBLinearPrimeExpGeometryRawMeanFloorRealBudgetEstimates meanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessEstimates meanFloor where
  rawSecond := hvar.rawSecond
  rawSecond_integrable := hvar.rawSecond_integrable
  rawSecond_le := hvar.rawSecond_le
  rawSecond_mean_floor_real_budget := hvar.rawSecond_mean_floor_real_budget
  flatness_layer :=
    trackBLinearPrimeExpFlatGoodLayerProbabilityFacts_of_realProbability hflat

/-- Centered-second route with flatness supplied through layer-indexed
one-coefficient tail estimates instead of a compact stage complement bound. -/
structure TrackBLinearPrimeExpGeometryCenteredSecondLayerFlatnessFacts where
  mean_lower : TrackBLinearPrimeExpLayerMeanLowerFacts
  centeredSecond : ℕ → ℕ → ℝ
  centeredSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
            ∫ omega,
              trackBLinearPrimeExpScheduledVariance
                omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2)
        mu
  centeredSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r) -
          ∫ omega,
            trackBLinearPrimeExpScheduledVariance
              omega j (trackBLinearPrimeExpScheduleSpec.point j r) ∂mu) ^ 2 ∂mu) ≤
        centeredSecond j r
  centeredSecond_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      ENNReal.ofReal
          (4 * centeredSecond j r / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2) ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r
  flatness_layer : TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts

/-- Raw-second route with flatness supplied through layer-indexed
one-coefficient tail estimates. -/
structure TrackBLinearPrimeExpGeometryRawSecondLayerFlatnessFacts where
  mean_lower : TrackBLinearPrimeExpLayerMeanLowerFacts
  rawSecond : ℕ → ℕ → ℝ
  rawSecond_integrable :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeExpScheduledVariance
            omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2)
        mu
  rawSecond_le :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∫ omega,
        (trackBLinearPrimeExpScheduledVariance
          omega j (trackBLinearPrimeExpScheduleSpec.point j r)) ^ 2 ∂mu) ≤
        rawSecond j r
  rawSecond_budget :
    ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      ENNReal.ofReal
          (4 * (4 * rawSecond j r) / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2) ≤
        trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r
  flatness_layer : TrackBLinearPrimeExpFlatGoodLayerProbabilityFacts

/-- Layer-indexed flatness tail estimates supply the compact flatness field in
the centered-second package. -/
def trackBLinearPrimeExpGeometryCenteredSecondFacts_of_layerFlatness
    (h : TrackBLinearPrimeExpGeometryCenteredSecondLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometryCenteredSecondFacts where
  mean_lower := h.mean_lower
  centeredSecond := h.centeredSecond
  centeredSecond_integrable := h.centeredSecond_integrable
  centeredSecond_le := h.centeredSecond_le
  centeredSecond_budget := h.centeredSecond_budget
  flatness_compl :=
    measure_trackBLinearPrimeExpFlatGood_compl_le_of_layerProbabilityFacts h.flatness_layer

/-- Layer-indexed flatness tail estimates supply the compact flatness field in
the raw-second package. -/
def trackBLinearPrimeExpGeometryRawSecondFacts_of_layerFlatness
    (h : TrackBLinearPrimeExpGeometryRawSecondLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometryRawSecondFacts where
  mean_lower := h.mean_lower
  rawSecond := h.rawSecond
  rawSecond_integrable := h.rawSecond_integrable
  rawSecond_le := h.rawSecond_le
  rawSecond_budget := h.rawSecond_budget
  flatness_compl :=
    measure_trackBLinearPrimeExpFlatGood_compl_le_of_layerProbabilityFacts h.flatness_layer

/-- Layer-indexed flatness tails supply the compact flatness field in the
real-budget centered-second package. -/
def trackBLinearPrimeExpGeometryCenteredSecondRealBudgetFacts_of_layerFlatness
    (h : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetFacts where
  mean_lower := h.mean_lower
  centeredSecond := h.centeredSecond
  centeredSecond_integrable := h.centeredSecond_integrable
  centeredSecond_le := h.centeredSecond_le
  centeredSecond_real_budget := h.centeredSecond_real_budget
  flatness_compl :=
    measure_trackBLinearPrimeExpFlatGood_compl_le_of_layerProbabilityFacts h.flatness_layer

/-- Layer-indexed flatness tails supply the compact flatness field in the
real-budget raw-second package. -/
def trackBLinearPrimeExpGeometryRawSecondRealBudgetFacts_of_layerFlatness
    (h : TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometryRawSecondRealBudgetFacts where
  mean_lower := h.mean_lower
  rawSecond := h.rawSecond
  rawSecond_integrable := h.rawSecond_integrable
  rawSecond_le := h.rawSecond_le
  rawSecond_real_budget := h.rawSecond_real_budget
  flatness_compl :=
    measure_trackBLinearPrimeExpFlatGood_compl_le_of_layerProbabilityFacts h.flatness_layer

/-- Layer-indexed flatness tails supply the compact flatness field in the
explicit mean-floor centered-second package. -/
def trackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetFacts_of_layerFlatness
    (h : TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetFacts where
  meanFloor := h.meanFloor
  mean_floor_ge_two_V := h.mean_floor_ge_two_V
  mean_floor_le_mean := h.mean_floor_le_mean
  centeredSecond := h.centeredSecond
  centeredSecond_integrable := h.centeredSecond_integrable
  centeredSecond_le := h.centeredSecond_le
  centeredSecond_mean_floor_real_budget := h.centeredSecond_mean_floor_real_budget
  flatness_compl :=
    measure_trackBLinearPrimeExpFlatGood_compl_le_of_layerProbabilityFacts h.flatness_layer

/-- Layer-indexed flatness tails supply the compact flatness field in the
explicit mean-floor raw-second package. -/
def trackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetFacts_of_layerFlatness
    (h : TrackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetFacts where
  meanFloor := h.meanFloor
  mean_floor_ge_two_V := h.mean_floor_ge_two_V
  mean_floor_le_mean := h.mean_floor_le_mean
  rawSecond := h.rawSecond
  rawSecond_integrable := h.rawSecond_integrable
  rawSecond_le := h.rawSecond_le
  rawSecond_mean_floor_real_budget := h.rawSecond_mean_floor_real_budget
  flatness_compl :=
    measure_trackBLinearPrimeExpFlatGood_compl_le_of_layerProbabilityFacts h.flatness_layer

/-- Add a separately proved deterministic mean floor to centered-second
mean-floor layer-flatness estimates. -/
def trackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessFacts_of_estimates
    (hmean : TrackBLinearPrimeExpLayerMeanFloorFacts)
    (h :
      TrackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessEstimates hmean.meanFloor) :
    TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetLayerFlatnessFacts where
  meanFloor := hmean.meanFloor
  mean_floor_ge_two_V := hmean.mean_floor_ge_two_V
  mean_floor_le_mean := hmean.mean_floor_le_mean
  centeredSecond := h.centeredSecond
  centeredSecond_integrable := h.centeredSecond_integrable
  centeredSecond_le := h.centeredSecond_le
  centeredSecond_mean_floor_real_budget := h.centeredSecond_mean_floor_real_budget
  flatness_layer := h.flatness_layer

/-- Add a separately proved deterministic mean floor to raw-second mean-floor
layer-flatness estimates. -/
def trackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessFacts_of_estimates
    (hmean : TrackBLinearPrimeExpLayerMeanFloorFacts)
    (h : TrackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessEstimates hmean.meanFloor) :
    TrackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetLayerFlatnessFacts where
  meanFloor := hmean.meanFloor
  mean_floor_ge_two_V := hmean.mean_floor_ge_two_V
  mean_floor_le_mean := hmean.mean_floor_le_mean
  rawSecond := h.rawSecond
  rawSecond_integrable := h.rawSecond_integrable
  rawSecond_le := h.rawSecond_le
  rawSecond_mean_floor_real_budget := h.rawSecond_mean_floor_real_budget
  flatness_layer := h.flatness_layer

/-- Add a separately proved deterministic mean lower bound to centered-second
real-budget layer-flatness estimates. -/
def trackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessFacts_of_estimates
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (h : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessFacts where
  mean_lower := hmean
  centeredSecond := h.centeredSecond
  centeredSecond_integrable := h.centeredSecond_integrable
  centeredSecond_le := h.centeredSecond_le
  centeredSecond_real_budget := h.centeredSecond_real_budget
  flatness_layer := h.flatness_layer

/-- Add a separately proved deterministic mean lower bound to raw-second
real-budget layer-flatness estimates. -/
def trackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessFacts_of_estimates
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (h : TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessFacts where
  mean_lower := hmean
  rawSecond := h.rawSecond
  rawSecond_integrable := h.rawSecond_integrable
  rawSecond_le := h.rawSecond_le
  rawSecond_real_budget := h.rawSecond_real_budget
  flatness_layer := h.flatness_layer

/-- A real-valued centered-second budget supplies the `ENNReal`
centered-second package. -/
def trackBLinearPrimeExpGeometryCenteredSecondFacts_of_realBudget
    (h : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryCenteredSecondFacts where
  mean_lower := h.mean_lower
  centeredSecond := h.centeredSecond
  centeredSecond_integrable := h.centeredSecond_integrable
  centeredSecond_le := h.centeredSecond_le
  centeredSecond_budget := by
    intro j r hr
    rw [trackBLinearPrimeExpGeometryVarianceLayerPointBudget_eq_ofReal j r]
    exact ENNReal.ofReal_le_ofReal (h.centeredSecond_real_budget j r hr)
  flatness_compl := h.flatness_compl

/-- A centered-second estimate with a larger deterministic mean floor gives the
mean/concentration package using the larger Chebyshev denominator. -/
def trackBLinearPrimeExpGeometryMeanConcentrationFacts_of_centeredSecondMeanFloorRealBudget
    (h : TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryMeanConcentrationFacts where
  mean_lower := by
    refine ⟨?_⟩
    intro j r hr
    exact (h.mean_floor_ge_two_V j r hr).trans (h.mean_floor_le_mean j r hr)
  variance_concentration := by
    intro j r hr _hmean
    let R : Omega → ℝ := fun omega =>
      trackBLinearPrimeExpScheduledVariance
        omega j (trackBLinearPrimeExpScheduleSpec.point j r)
    let A : ℝ := h.meanFloor j r
    have hV_pos : 0 < trackBLinearPrimeExpScheduleSpec.V j := by
      have hbase : (0 : ℝ) < trackBLinearPrimeConcreteBase j := by
        exact_mod_cast trackBLinearPrimeConcreteBase_pos j
      simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteV] using
        pow_pos hbase (20 * trackBLinearPrimeConcreteK)
    have htwoV_pos : 0 < 2 * trackBLinearPrimeExpScheduleSpec.V j := by
      positivity
    have hA_ge_twoV :
        2 * trackBLinearPrimeExpScheduleSpec.V j ≤ A := by
      simpa [A] using h.mean_floor_ge_two_V j r hr
    have hA_pos : 0 < A := lt_of_lt_of_le htwoV_pos hA_ge_twoV
    have hmean_integral : A ≤ ∫ omega, R omega ∂mu := by
      calc
        A ≤ trackBLinearPrimeExpLayerWeightedSupportMass j r := by
          simpa [A] using h.mean_floor_le_mean j r hr
        _ = ∫ omega, R omega ∂mu := by
          dsimp [R]
          exact (integral_trackBLinearPrimeExp_scheduledVariance_eq_weightedSupportMass
            j r hr).symm
    have hcheb :
        mu {omega | R omega < A / 2} ≤
          ENNReal.ofReal (4 * h.centeredSecond j r / A ^ 2) :=
      measure_lt_half_mean_le_centered_second
        R A (h.centeredSecond j r)
        hA_pos
        (by simpa [R] using h.centeredSecond_integrable j r hr)
        hmean_integral
        (by simpa [R] using h.centeredSecond_le j r hr)
    have hV_le_halfA : trackBLinearPrimeExpScheduleSpec.V j ≤ A / 2 := by
      nlinarith
    have hsubset :
        {omega | R omega < trackBLinearPrimeExpScheduleSpec.V j} ⊆
          {omega | R omega < A / 2} := by
      intro omega homega
      exact lt_of_lt_of_le homega hV_le_halfA
    have htarget :
        mu {omega | R omega < trackBLinearPrimeExpScheduleSpec.V j} ≤
          trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r := by
      calc
        mu {omega | R omega < trackBLinearPrimeExpScheduleSpec.V j}
            ≤ mu {omega | R omega < A / 2} := measure_mono hsubset
        _ ≤ ENNReal.ofReal (4 * h.centeredSecond j r / A ^ 2) := hcheb
        _ ≤ trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r := by
          rw [trackBLinearPrimeExpGeometryVarianceLayerPointBudget_eq_ofReal j r]
          exact ENNReal.ofReal_le_ofReal
            (by
              simpa [A] using h.centeredSecond_mean_floor_real_budget j r hr)
    rw [← measure_trackBLinearPrimeExpVarianceBadSet_eq_layer j r hr]
    simpa [R, trackBLinearPrimeExpVarianceBadSet] using htarget
  flatness_compl := h.flatness_compl

/-- A raw second moment estimate gives the explicit mean-floor centered-second
package while preserving the larger mean-floor budget. -/
def trackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetFacts_of_rawSecondMeanFloor
    (h : TrackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetFacts where
  meanFloor := h.meanFloor
  mean_floor_ge_two_V := h.mean_floor_ge_two_V
  mean_floor_le_mean := h.mean_floor_le_mean
  centeredSecond := fun j r => 4 * h.rawSecond j r
  centeredSecond_integrable := by
    intro j r hr
    let R : Omega → ℝ := fun omega =>
      trackBLinearPrimeExpScheduledVariance
        omega j (trackBLinearPrimeExpScheduleSpec.point j r)
    exact
      integrable_centered_square_of_integrable_sq
        (D := R)
        (by
          dsimp [R]
          exact
            integrable_trackBLinearPrimeScheduledVariance
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi j
              (trackBLinearPrimeExpScheduleSpec.point j r))
        (by simpa [R] using h.rawSecond_integrable j r hr)
  centeredSecond_le := by
    intro j r hr
    let R : Omega → ℝ := fun omega =>
      trackBLinearPrimeExpScheduledVariance
        omega j (trackBLinearPrimeExpScheduleSpec.point j r)
    have hR_int : Integrable R mu := by
      dsimp [R]
      exact
        integrable_trackBLinearPrimeScheduledVariance
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi j
          (trackBLinearPrimeExpScheduleSpec.point j r)
    calc
      (∫ omega, (R omega - ∫ omega, R omega ∂mu) ^ 2 ∂mu)
          ≤ 4 * ∫ omega, R omega ^ 2 ∂mu :=
            centered_second_le_four_raw_second
              (D := R) hR_int (by simpa [R] using h.rawSecond_integrable j r hr)
      _ ≤ 4 * h.rawSecond j r := by
            exact mul_le_mul_of_nonneg_left
              (by simpa [R] using h.rawSecond_le j r hr) (by norm_num : (0 : ℝ) ≤ 4)
  centeredSecond_mean_floor_real_budget := by
    intro j r hr
    simpa using h.rawSecond_mean_floor_real_budget j r hr
  flatness_compl := h.flatness_compl

/-- A raw second moment estimate with an explicit mean floor gives the
mean/concentration package through the centered-second mean-floor route. -/
def trackBLinearPrimeExpGeometryMeanConcentrationFacts_of_rawSecondMeanFloorRealBudget
    (h : TrackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryMeanConcentrationFacts :=
  trackBLinearPrimeExpGeometryMeanConcentrationFacts_of_centeredSecondMeanFloorRealBudget
    (trackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetFacts_of_rawSecondMeanFloor h)

/-- A real-valued raw-second budget supplies the `ENNReal` raw-second package. -/
def trackBLinearPrimeExpGeometryRawSecondFacts_of_realBudget
    (h : TrackBLinearPrimeExpGeometryRawSecondRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryRawSecondFacts where
  mean_lower := h.mean_lower
  rawSecond := h.rawSecond
  rawSecond_integrable := h.rawSecond_integrable
  rawSecond_le := h.rawSecond_le
  rawSecond_budget := by
    intro j r hr
    rw [trackBLinearPrimeExpGeometryVarianceLayerPointBudget_eq_ofReal j r]
    exact ENNReal.ofReal_le_ofReal (h.rawSecond_real_budget j r hr)
  flatness_compl := h.flatness_compl

/-- A raw second moment bound gives the centered-second-moment package. -/
def trackBLinearPrimeExpGeometryCenteredSecondFacts_of_rawSecond
    (h : TrackBLinearPrimeExpGeometryRawSecondFacts) :
    TrackBLinearPrimeExpGeometryCenteredSecondFacts where
  mean_lower := h.mean_lower
  centeredSecond := fun j r => 4 * h.rawSecond j r
  centeredSecond_integrable := by
    intro j r hr
    let R : Omega → ℝ := fun omega =>
      trackBLinearPrimeExpScheduledVariance
        omega j (trackBLinearPrimeExpScheduleSpec.point j r)
    exact
      integrable_centered_square_of_integrable_sq
        (D := R)
        (by
          dsimp [R]
          exact
            integrable_trackBLinearPrimeScheduledVariance
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi j
              (trackBLinearPrimeExpScheduleSpec.point j r))
        (by simpa [R] using h.rawSecond_integrable j r hr)
  centeredSecond_le := by
    intro j r hr
    let R : Omega → ℝ := fun omega =>
      trackBLinearPrimeExpScheduledVariance
        omega j (trackBLinearPrimeExpScheduleSpec.point j r)
    have hR_int : Integrable R mu := by
      dsimp [R]
      exact
        integrable_trackBLinearPrimeScheduledVariance
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi j
          (trackBLinearPrimeExpScheduleSpec.point j r)
    calc
      (∫ omega, (R omega - ∫ omega, R omega ∂mu) ^ 2 ∂mu)
          ≤ 4 * ∫ omega, R omega ^ 2 ∂mu :=
            centered_second_le_four_raw_second
              (D := R) hR_int (by simpa [R] using h.rawSecond_integrable j r hr)
      _ ≤ 4 * h.rawSecond j r := by
            exact mul_le_mul_of_nonneg_left
              (by simpa [R] using h.rawSecond_le j r hr) (by norm_num : (0 : ℝ) ≤ 4)
  centeredSecond_budget := by
    intro j r hr
    simpa using h.rawSecond_budget j r hr
  flatness_compl := h.flatness_compl

/-- A centered-second-moment estimate gives the mean/concentration package via
the generic one-sided Chebyshev lemma. -/
def trackBLinearPrimeExpGeometryMeanConcentrationFacts_of_centeredSecond
    (h : TrackBLinearPrimeExpGeometryCenteredSecondFacts) :
    TrackBLinearPrimeExpGeometryMeanConcentrationFacts where
  mean_lower := h.mean_lower
  variance_concentration := by
    intro j r hr hmean
    let R : Omega → ℝ := fun omega =>
      trackBLinearPrimeExpScheduledVariance
        omega j (trackBLinearPrimeExpScheduleSpec.point j r)
    have hV_pos : 0 < trackBLinearPrimeExpScheduleSpec.V j := by
      have hbase : (0 : ℝ) < trackBLinearPrimeConcreteBase j := by
        exact_mod_cast trackBLinearPrimeConcreteBase_pos j
      simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteV] using
        pow_pos hbase (20 * trackBLinearPrimeConcreteK)
    have htwoV_pos : 0 < 2 * trackBLinearPrimeExpScheduleSpec.V j := by
      positivity
    have hmean_integral :
        2 * trackBLinearPrimeExpScheduleSpec.V j ≤ ∫ omega, R omega ∂mu := by
      calc
        2 * trackBLinearPrimeExpScheduleSpec.V j
            ≤ trackBLinearPrimeExpLayerWeightedSupportMass j r := hmean
        _ = ∫ omega, R omega ∂mu := by
            dsimp [R]
            exact (integral_trackBLinearPrimeExp_scheduledVariance_eq_weightedSupportMass
              j r hr).symm
    have hcheb :
        mu {omega | R omega < (2 * trackBLinearPrimeExpScheduleSpec.V j) / 2} ≤
          ENNReal.ofReal
            (4 * h.centeredSecond j r / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2) :=
      measure_lt_half_mean_le_centered_second
        R (2 * trackBLinearPrimeExpScheduleSpec.V j) (h.centeredSecond j r)
        htwoV_pos
        (by simpa [R] using h.centeredSecond_integrable j r hr)
        hmean_integral
        (by simpa [R] using h.centeredSecond_le j r hr)
    have htarget :
        mu {omega | R omega < trackBLinearPrimeExpScheduleSpec.V j} ≤
          trackBLinearPrimeExpGeometryVarianceLayerPointBudget j r := by
      have hhalf :
          (2 * trackBLinearPrimeExpScheduleSpec.V j) / 2 =
            trackBLinearPrimeExpScheduleSpec.V j := by
        ring
      have hcheb_target :
          mu {omega | R omega < trackBLinearPrimeExpScheduleSpec.V j} ≤
            ENNReal.ofReal
              (4 * h.centeredSecond j r / (2 * trackBLinearPrimeExpScheduleSpec.V j) ^ 2) := by
        simpa [hhalf] using hcheb
      exact hcheb_target.trans (h.centeredSecond_budget j r hr)
    rw [← measure_trackBLinearPrimeExpVarianceBadSet_eq_layer j r hr]
    simpa [R, trackBLinearPrimeExpVarianceBadSet] using htarget
  flatness_compl := h.flatness_compl

/-- Mean lower bound plus a concentration theorem gives the small-ball and
flatness facts consumed by the geometry-good probability reducer. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_meanConcentration
    (h : TrackBLinearPrimeExpGeometryMeanConcentrationFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts where
  variance_small_ball := by
    intro j r hr
    exact h.variance_concentration j r hr (h.mean_lower.mean_ge_two_V j r hr)
  flatness_compl := h.flatness_compl

/-- Centered-second estimates with an explicit mean floor give the small-ball
and flatness facts through the stronger mean-floor Chebyshev route. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecondMeanFloorRealBudget
    (h : TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_meanConcentration
    (trackBLinearPrimeExpGeometryMeanConcentrationFacts_of_centeredSecondMeanFloorRealBudget h)

/-- Raw-second estimates with an explicit mean floor give the small-ball and
flatness facts through the stronger mean-floor Chebyshev route. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawSecondMeanFloorRealBudget
    (h : TrackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_meanConcentration
    (trackBLinearPrimeExpGeometryMeanConcentrationFacts_of_rawSecondMeanFloorRealBudget h)

/-- Centered-second mean-floor budgets plus layer-indexed flatness tails give
the small-ball and flatness facts consumed by the probability reducer. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredMeanFloorLayerFlatness
    (h : TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecondMeanFloorRealBudget
    (trackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetFacts_of_layerFlatness h)

/-- Raw-second mean-floor budgets plus layer-indexed flatness tails give the
small-ball and flatness facts consumed by the probability reducer. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawMeanFloorLayerFlatness
    (h : TrackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawSecondMeanFloorRealBudget
    (trackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetFacts_of_layerFlatness h)

/-- Centered-second-moment estimates give the small-ball and flatness facts
consumed by the geometry-good probability reducer. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecond
    (h : TrackBLinearPrimeExpGeometryCenteredSecondFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_meanConcentration
    (trackBLinearPrimeExpGeometryMeanConcentrationFacts_of_centeredSecond h)

/-- Real-valued centered-second budgets give the small-ball and flatness facts
consumed by the probability reducer. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecondRealBudget
    (h : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecond
    (trackBLinearPrimeExpGeometryCenteredSecondFacts_of_realBudget h)

/-- Real-valued centered-second budgets plus layer-indexed flatness tails give
the small-ball and flatness facts consumed by the probability reducer. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecondRealBudgetLayerFlatness
    (h : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecondRealBudget
    (trackBLinearPrimeExpGeometryCenteredSecondRealBudgetFacts_of_layerFlatness h)

/-- Centered-second real-budget layer-flatness estimates plus a separate mean
lower package give the small-ball and flatness facts. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecondRealBudgetEstimates
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (h : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecondRealBudgetLayerFlatness
    (trackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessFacts_of_estimates
      hmean h)

/-- Centered-second estimates plus layer-indexed coefficient-flatness tails
give the small-ball and flatness facts consumed by the probability reducer. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecondLayerFlatness
    (h : TrackBLinearPrimeExpGeometryCenteredSecondLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecond
    (trackBLinearPrimeExpGeometryCenteredSecondFacts_of_layerFlatness h)

/-- Raw second moment estimates give the small-ball and flatness facts consumed
by the geometry-good probability reducer. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawSecond
    (h : TrackBLinearPrimeExpGeometryRawSecondFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecond
    (trackBLinearPrimeExpGeometryCenteredSecondFacts_of_rawSecond h)

/-- Real-valued raw-second budgets give the small-ball and flatness facts
consumed by the probability reducer. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawSecondRealBudget
    (h : TrackBLinearPrimeExpGeometryRawSecondRealBudgetFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawSecond
    (trackBLinearPrimeExpGeometryRawSecondFacts_of_realBudget h)

/-- Real-valued raw-second budgets plus layer-indexed flatness tails give the
small-ball and flatness facts consumed by the probability reducer. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawSecondRealBudgetLayerFlatness
    (h : TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawSecondRealBudget
    (trackBLinearPrimeExpGeometryRawSecondRealBudgetFacts_of_layerFlatness h)

/-- Raw-second real-budget layer-flatness estimates plus a separate mean lower
package give the small-ball and flatness facts. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawSecondRealBudgetEstimates
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (h : TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawSecondRealBudgetLayerFlatness
    (trackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessFacts_of_estimates
      hmean h)

/-- Raw second moment estimates plus layer-indexed coefficient-flatness tails
give the small-ball and flatness facts consumed by the probability reducer. -/
def trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawSecondLayerFlatness
    (h : TrackBLinearPrimeExpGeometryRawSecondLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts :=
  trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawSecond
    (trackBLinearPrimeExpGeometryRawSecondFacts_of_layerFlatness h)

/-- The paper-side small-ball and flatness estimates are exactly the pointwise
concrete probability facts expected by the Lean geometry-good reducer. -/
def trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_smallBallFlatness
    (h : TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts) :
    TrackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts where
  variance_layer_bad_le := h.variance_small_ball
  flat_compl_le := h.flatness_compl

/-- Small-ball plus flatness estimates imply the concrete summed probability
facts for `trackBLinearPrimeExpGeometryGood`. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_smallBallFlatness
    (h : TrackBLinearPrimeExpGeometrySmallBallFlatnessFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_pointwise
    (trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_smallBallFlatness h)

/-- A separated lower-tail concentration theorem, deterministic mean lower
bound, and real-valued layer flatness tails give the concrete geometry-good
probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_concentration_realProbability
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_smallBallFlatness
    (trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_meanConcentration
      (trackBLinearPrimeExpGeometryMeanConcentrationFacts_of_varianceConcentration_realProbability
        hmean hvar hflat))

/-- Four named product/rough bad events, deterministic mean lower bound, and
real-valued layer flatness tails give the concrete geometry-good probability
inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_fourEvents_realProbability
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_concentration_realProbability
    hmean
    (trackBLinearPrimeExpGeometryVarianceConcentrationFacts_of_fourteenth
      (trackBLinearPrimeExpGeometryVarianceConcentrationFourteenthFacts_of_fourEvents hvar))
    hflat

/-- Common-floor signal/error estimates, deterministic mean lower bound, and
real-valued layer flatness tails give the concrete geometry-good probability
inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_energyFloor_realProbability
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationEnergyFloorFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_fourEvents_realProbability
    hmean
    (trackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts_of_energyFloor hvar)
    hflat

/-- Product/rough floor estimates, deterministic mean lower bound, and
real-valued layer flatness tails give the concrete geometry-good probability
inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_productRoughFloor_realProbability
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughFloorFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_energyFloor_realProbability
    hmean
    (trackBLinearPrimeExpGeometryVarianceConcentrationEnergyFloorFacts_of_productRoughFloor
      hvar)
    hflat

/-- Product/rough signal-factor estimates, deterministic mean lower bound, and
real-valued layer flatness tails give the concrete geometry-good probability
inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_prodSignal_realProbability
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSignalFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_productRoughFloor_realProbability
    hmean
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughFloorFacts_of_prodSignal
      hvar)
    hflat

/-- Product/rough threshold estimates, deterministic mean lower bound, and
real-valued layer flatness tails give the concrete geometry-good probability
inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_prodThreshold_realProbability
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_prodSignal_realProbability
    hmean
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSignalFacts_of_threshold
      hvar)
    hflat

/-- Product/rough threshold estimates with real probability bounds, deterministic
mean lower bound, and real-valued layer flatness tails give the concrete
geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_prodThresholdReal
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdRealFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_prodThreshold_realProbability
    hmean
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdFacts_of_real
      hvar)
    hflat

/-- Product/rough error-budget estimates with real probability bounds,
deterministic mean lower bound, and real-valued layer flatness tails give the
concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_prodErrorBudgetReal
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughErrorBudgetRealFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_prodThresholdReal
    hmean
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdRealFacts_of_errorBudget
      hvar)
    hflat

/-- Product/rough estimates with the canonical `V_j` error budget, deterministic
mean lower bound, and real-valued layer flatness tails give the concrete
geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_prodVErrorReal
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_prodErrorBudgetReal
    hmean
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughErrorBudgetRealFacts_of_vError
      hvar)
    hflat

/-- Boundary-safe support-bulk mass split into support and fresh-prime pieces,
product/rough estimates with the canonical `V_j` error budget, and real-valued
layer flatness tails give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_splitMass_prodVErrorReal
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hprime : TrackBLinearPrimeExpFreshPrimeMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_prodVErrorReal
    (trackBLinearPrimeExpLayerMeanLowerFacts_of_supportBulk
      (trackBLinearPrimeExpSupportBulkMassFacts_of_support_and_prime hsupport hprime))
    hvar hflat

/-- Boundary-safe support-bulk mass split into support and fresh-prime pieces,
plus separately proved product/rough deterministic and tail records, give the
concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_splitMass_prodVErrorPieces
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hprime : TrackBLinearPrimeExpFreshPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_splitMass_prodVErrorReal
    hsupport hprime
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts_of_pieces
      core hsmall hrough herror hmass)
    hflat

/-- Full fresh-layer reciprocal-mass estimates plus separately proved
product/rough deterministic and tail records give the concrete geometry-good
probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_prodVErrorPieces
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_splitMass_prodVErrorPieces
    hsupport
    (trackBLinearPrimeExpFreshPrimeMassFacts_of_freshLayer hlayer)
    core hsmall hrough herror hmass hflat

/-- Boundary-safe split mass, exact product/rough tail records, and
event-witness coefficient-flatness tails give the concrete geometry-good
probability inputs. -/
def
    trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_splitMass_prodVErrorPiecesFlat
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hprime : TrackBLinearPrimeExpFreshPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_splitMass_prodVErrorPieces
    hsupport hprime core hsmall hrough herror hmass
    (trackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts_of_event hflat)

/-- Full fresh-layer mass, exact product/rough tail records, and event-witness
coefficient-flatness tails give the concrete geometry-good probability inputs. -/
def
    trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_prodVErrorPiecesFlat
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_prodVErrorPieces
    hsupport hlayer core hsmall hrough herror hmass
    (trackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts_of_event hflat)

/-- Boundary-safe support-bulk mass split into support and fresh-prime pieces,
plus event-witness product/rough tail records, give the concrete geometry-good
probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_splitMass_prodVErrorEventPieces
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hprime : TrackBLinearPrimeExpFreshPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_splitMass_prodVErrorReal
    hsupport hprime
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts_of_eventPieces
      core hsmall hrough herror hmass)
    hflat

/-- Full fresh-layer reciprocal-mass estimates plus event-witness product/rough
tail records give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_prodVErrorEventPieces
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_splitMass_prodVErrorEventPieces
    hsupport
    (trackBLinearPrimeExpFreshPrimeMassFacts_of_freshLayer hlayer)
    core hsmall hrough herror hmass hflat

/-- Boundary-safe split mass, event-witness product/rough tails, and
event-witness coefficient-flatness tails give the concrete geometry-good
probability inputs. -/
def
    trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_splitMass_prodVErrorAllEvents
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hprime : TrackBLinearPrimeExpFreshPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_splitMass_prodVErrorEventPieces
    hsupport hprime core hsmall hrough herror hmass
    (trackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts_of_event hflat)

/-- Full fresh-layer mass, event-witness product/rough tails, and event-witness
coefficient-flatness tails give the concrete geometry-good probability inputs. -/
def
    trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_prodVErrorAllEvents
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_prodVErrorEventPieces
    hsupport hlayer core hsmall hrough herror hmass
    (trackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts_of_event hflat)

/-- Full fresh-layer mass, fixed-floor product/rough tails for canonical
threshold events, and event-witness coefficient-flatness tails give the
concrete geometry-good probability inputs. -/
def
    trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_fixedFloorPiecesFlat
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (fixedCore : TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_prodVErrorPiecesFlat
    hsupport hlayer
    (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore)
    hsmall hrough herror hmass hflat

/-- Full fresh-layer mass and canonical fixed-floor product/rough tails give
the concrete geometry-good probability inputs when the mass bad event is
empty. -/
def
    trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_fixedFloorPiecesEmptyMass
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (fixedCore : TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts)
    (hbad : ∀ j r, fixedCore.badMass j r = ∅)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_fixedFloorPiecesFlat
    hsupport hlayer fixedCore hsmall hrough herror
    (trackBLinearPrimeExpFixedFloorMassTailRealFacts_of_empty fixedCore hbad)
    hflat

/-- No-mass fixed-floor core, canonical product/rough tails, and full
fresh-layer mass give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_noMassFixedFloorPieces
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core))
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core))
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core))
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_fixedFloorPiecesEmptyMass
    hsupport hlayer (trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass core)
    (by intro j r; rfl)
    hsmall hrough herror hflat

/-- Full fresh-layer mass, fixed-floor product/rough tails through enlarged bad
events, and event-witness coefficient-flatness tails give the concrete
geometry-good probability inputs. -/
def
    trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_fixedFloorAllEvents
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (fixedCore : TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_prodVErrorAllEvents
    hsupport hlayer
    (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore)
    hsmall hrough herror hmass hflat

/-- Full fresh-layer mass and fixed-floor product/rough event tails give the
concrete geometry-good probability inputs when the mass bad event is empty. -/
def
    trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_fixedFloorEmptyMass
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (fixedCore : TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts)
    (hbad : ∀ j r, fixedCore.badMass j r = ∅)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_fixedFloorAllEvents
    hsupport hlayer fixedCore hsmall hrough herror
    (trackBLinearPrimeExpFixedFloorMassTailEventRealFacts_of_empty fixedCore hbad)
    hflat

/-- No-mass fixed-floor core, event-witness product/rough tails, and full
fresh-layer mass give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_noMassFixedFloorEvents
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core))
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core))
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core))
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_freshLayer_fixedFloorEmptyMass
    hsupport hlayer (trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass core)
    (by intro j r; rfl)
    hsmall hrough herror hflat

/-- No-mass fixed-floor core, pointwise small/rough/error threshold exclusions,
and full fresh-layer mass give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_noMassPointwise
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (hsmall : ∀ omega j,
      trackBLinearPrimeExpProductRoughSmallFloor j ≤ core.smallFactor omega j ^ 2)
    (hrough : ∀ omega j r,
      r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      trackBLinearPrimeExpProductRoughRoughFloor j r ≤
        ∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          core.roughCoeff omega j r p ^ 2)
    (herror : ∀ omega j r,
      r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∑ p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r),
        core.errorCoeff omega j r p ^ 2) ≤ trackBLinearPrimeExpScheduleSpec.V j)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_noMassFixedFloorPieces
    hsupport hlayer core
    (trackBLinearPrimeExpSmallTailRealFacts_of_pointwise
      (core := trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core)
      (by
        intro omega j
        simpa [trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass,
          trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor,
          trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass] using hsmall omega j))
    (trackBLinearPrimeExpRoughTailRealFacts_of_pointwise
      (core := trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core)
      (by
        intro omega j r hr
        simpa [trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass,
          trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor,
          trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass] using hrough omega j r hr))
    (trackBLinearPrimeExpVErrorTailRealFacts_of_pointwise
      (core := trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core)
      (by
        intro omega j r hr
        simpa [trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass,
          trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor,
          trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass] using herror omega j r hr))
    hflat

/-- Centered-second mean-floor estimates give the pointwise geometry-good
probability inputs. -/
def trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_centeredMeanFloor
    (h : TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_smallBallFlatness
    (trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecondMeanFloorRealBudget h)

/-- Raw-second mean-floor estimates give the pointwise geometry-good probability
inputs. -/
def trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_rawMeanFloor
    (h : TrackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_smallBallFlatness
    (trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawSecondMeanFloorRealBudget h)

/-- Centered-second mean-floor estimates with layer-indexed flatness tails give
the pointwise geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_centeredMeanFloorLayerFlatness
    (h : TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_smallBallFlatness
    (trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredMeanFloorLayerFlatness h)

/-- Raw-second mean-floor estimates with layer-indexed flatness tails give the
pointwise geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_rawMeanFloorLayerFlatness
    (h : TrackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_smallBallFlatness
    (trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawMeanFloorLayerFlatness h)

/-- Centered-second mean-floor estimates give the concrete summed
geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredMeanFloor
    (h : TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_pointwise
    (trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_centeredMeanFloor h)

/-- Raw-second mean-floor estimates give the concrete summed geometry-good
probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawMeanFloor
    (h : TrackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_pointwise
    (trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_rawMeanFloor h)

/-- Centered-second mean-floor estimates with layer-indexed flatness tails give
the concrete summed geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredMeanFloorLayerFlatness
    (h : TrackBLinearPrimeExpGeometryCenteredSecondMeanFloorRealBudgetLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_pointwise
    (trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_centeredMeanFloorLayerFlatness
      h)

/-- Raw-second mean-floor estimates with layer-indexed flatness tails give the
concrete summed geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawMeanFloorLayerFlatness
    (h : TrackBLinearPrimeExpGeometryRawSecondMeanFloorRealBudgetLayerFlatnessFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_pointwise
    (trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_rawMeanFloorLayerFlatness h)

/-- Separate deterministic mean-floor facts plus centered-second estimates give
the pointwise geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_centeredMeanFloorEstimates
    (hmean : TrackBLinearPrimeExpLayerMeanFloorFacts)
    (h :
      TrackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessEstimates hmean.meanFloor) :
    TrackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_centeredMeanFloorLayerFlatness
    (trackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessFacts_of_estimates hmean h)

/-- Separate deterministic mean-floor facts plus raw-second estimates give the
pointwise geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_rawMeanFloorEstimates
    (hmean : TrackBLinearPrimeExpLayerMeanFloorFacts)
    (h : TrackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessEstimates hmean.meanFloor) :
    TrackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_rawMeanFloorLayerFlatness
    (trackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessFacts_of_estimates hmean h)

/-- Separate deterministic mean-floor facts plus centered-second estimates give
the concrete summed geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredMeanFloorEstimates
    (hmean : TrackBLinearPrimeExpLayerMeanFloorFacts)
    (h :
      TrackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessEstimates hmean.meanFloor) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_pointwise
    (trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_centeredMeanFloorEstimates
      hmean h)

/-- Separate deterministic mean-floor facts plus raw-second estimates give the
concrete summed geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawMeanFloorEstimates
    (hmean : TrackBLinearPrimeExpLayerMeanFloorFacts)
    (h : TrackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessEstimates hmean.meanFloor) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_pointwise
    (trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_rawMeanFloorEstimates
      hmean h)

/-- Retained mean floor plus centered-second variance estimates and harmonic
flatness budget give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredMeanFloor_harmonic
    (hmean : TrackBLinearPrimeExpLayerMeanFloorFacts)
    (hvar : TrackBLinearPrimeExpGeometryCenteredMeanFloorRealBudgetEstimates hmean.meanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredMeanFloorEstimates
    hmean
    (trackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessEstimates_of_harmonic
      hvar hflat)

/-- Retained mean floor plus raw-second variance estimates and harmonic flatness
budget give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawMeanFloor_harmonic
    (hmean : TrackBLinearPrimeExpLayerMeanFloorFacts)
    (hvar : TrackBLinearPrimeExpGeometryRawMeanFloorRealBudgetEstimates hmean.meanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawMeanFloorEstimates
    hmean
    (trackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessEstimates_of_harmonic
      hvar hflat)

/-- Retained mean floor plus centered-second variance estimates and reciprocal
flatness budget give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredMeanFloor_reciprocal
    (hmean : TrackBLinearPrimeExpLayerMeanFloorFacts)
    (hvar : TrackBLinearPrimeExpGeometryCenteredMeanFloorRealBudgetEstimates hmean.meanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredMeanFloorEstimates
    hmean
    (trackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessEstimates_of_reciprocal
      hvar hflat)

/-- Retained mean floor plus raw-second variance estimates and reciprocal
flatness budget give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawMeanFloor_reciprocal
    (hmean : TrackBLinearPrimeExpLayerMeanFloorFacts)
    (hvar : TrackBLinearPrimeExpGeometryRawMeanFloorRealBudgetEstimates hmean.meanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawMeanFloorEstimates
    hmean
    (trackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessEstimates_of_reciprocal
      hvar hflat)

/-- Retained mean floor plus centered-second variance estimates and arbitrary
real-valued flatness tails give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredMeanFloor_realProbability
    (hmean : TrackBLinearPrimeExpLayerMeanFloorFacts)
    (hvar : TrackBLinearPrimeExpGeometryCenteredMeanFloorRealBudgetEstimates hmean.meanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredMeanFloorEstimates
    hmean
    (trackBLinearPrimeExpGeometryCenteredMeanFloorLayerFlatnessEstimates_of_realProbability
      hvar hflat)

/-- Retained mean floor plus raw-second variance estimates and arbitrary
real-valued flatness tails give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawMeanFloor_realProbability
    (hmean : TrackBLinearPrimeExpLayerMeanFloorFacts)
    (hvar : TrackBLinearPrimeExpGeometryRawMeanFloorRealBudgetEstimates hmean.meanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawMeanFloorEstimates
    hmean
    (trackBLinearPrimeExpGeometryRawMeanFloorLayerFlatnessEstimates_of_realProbability
      hvar hflat)

/-- Named concrete mass floors plus centered-second mean-floor variance
estimates and harmonic flatness give the concrete geometry-good probability
inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_concreteMeanFloor_centered_harmonic
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar :
      TrackBLinearPrimeExpGeometryCenteredMeanFloorRealBudgetEstimates
        trackBLinearPrimeExpConcreteMeanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredMeanFloor_harmonic
    (trackBLinearPrimeExpConcreteMeanFloorFacts_of_concreteFloors hmass) hvar hflat

/-- Named concrete mass floors plus raw-second mean-floor variance estimates and
harmonic flatness give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_concreteMeanFloor_raw_harmonic
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar :
      TrackBLinearPrimeExpGeometryRawMeanFloorRealBudgetEstimates
        trackBLinearPrimeExpConcreteMeanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawMeanFloor_harmonic
    (trackBLinearPrimeExpConcreteMeanFloorFacts_of_concreteFloors hmass) hvar hflat

/-- Named concrete mass floors plus centered-second mean-floor variance
estimates and reciprocal-mass flatness give the concrete geometry-good
probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_concreteMeanFloor_centered_recip
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar :
      TrackBLinearPrimeExpGeometryCenteredMeanFloorRealBudgetEstimates
        trackBLinearPrimeExpConcreteMeanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredMeanFloor_reciprocal
    (trackBLinearPrimeExpConcreteMeanFloorFacts_of_concreteFloors hmass) hvar hflat

/-- Named concrete mass floors plus raw-second mean-floor variance estimates and
reciprocal-mass flatness give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_concreteMeanFloor_raw_recip
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar :
      TrackBLinearPrimeExpGeometryRawMeanFloorRealBudgetEstimates
        trackBLinearPrimeExpConcreteMeanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawMeanFloor_reciprocal
    (trackBLinearPrimeExpConcreteMeanFloorFacts_of_concreteFloors hmass) hvar hflat

/-- Named concrete mass floors plus centered-second mean-floor variance
estimates and arbitrary real-valued flatness tails give the concrete
geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_concreteMeanFloor_centered_realProb
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar :
      TrackBLinearPrimeExpGeometryCenteredMeanFloorRealBudgetEstimates
        trackBLinearPrimeExpConcreteMeanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredMeanFloor_realProbability
    (trackBLinearPrimeExpConcreteMeanFloorFacts_of_concreteFloors hmass) hvar hflat

/-- Named concrete mass floors plus raw-second mean-floor variance estimates and
arbitrary real-valued flatness tails give the concrete geometry-good probability
inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_concreteMeanFloor_raw_realProb
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar :
      TrackBLinearPrimeExpGeometryRawMeanFloorRealBudgetEstimates
        trackBLinearPrimeExpConcreteMeanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawMeanFloor_realProbability
    (trackBLinearPrimeExpConcreteMeanFloorFacts_of_concreteFloors hmass) hvar hflat

/-- Centered-second real-budget estimates plus a separate mean lower package
give the pointwise geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_centeredSecondRealBudgetEstimates
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (h : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_smallBallFlatness
    (trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_centeredSecondRealBudgetEstimates
      hmean h)

/-- Raw-second real-budget estimates plus a separate mean lower package give
the pointwise geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_rawSecondRealBudgetEstimates
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (h : TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_smallBallFlatness
    (trackBLinearPrimeExpGeometrySmallBallFlatnessFacts_of_rawSecondRealBudgetEstimates
      hmean h)

/-- Centered-second real-budget estimates plus a separate mean lower package
give the concrete summed geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredSecondRealBudgetEstimates
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (h : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_pointwise
    (trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_centeredSecondRealBudgetEstimates
      hmean h)

/-- Raw-second real-budget estimates plus a separate mean lower package give
the concrete summed geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawSecondRealBudgetEstimates
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (h : TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_pointwise
    (trackBLinearPrimeExpGeometryGoodPointwiseProbabilityFacts_of_rawSecondRealBudgetEstimates
      hmean h)

/-- Named concrete reciprocal-mass floors plus centered-second real-budget
estimates give the concrete summed geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_concreteFloors_centeredEstimates
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (h : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredSecondRealBudgetEstimates
    (trackBLinearPrimeExpLayerMeanLowerFacts_of_concreteFloors hmass) h

/-- Subset reciprocal-mass floors plus centered-second real-budget estimates
give the concrete summed geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_subsetMass_centeredEstimates
    (hmass : TrackBLinearPrimeExpConcreteFloorSubsetMassFacts)
    (h : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredSecondRealBudgetEstimates
    (trackBLinearPrimeExpLayerMeanLowerFacts_of_subsetMass hmass) h

/-- Boundary-safe support-bulk mass facts plus centered-second real-budget
estimates give the concrete summed geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_supportBulk_centeredEstimates
    (hmass : TrackBLinearPrimeExpSupportBulkMassFacts)
    (h : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredSecondRealBudgetEstimates
    (trackBLinearPrimeExpLayerMeanLowerFacts_of_supportBulk hmass) h

/-- Named concrete reciprocal-mass floors plus raw-second real-budget estimates
give the concrete summed geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_concreteFloors_rawEstimates
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (h : TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawSecondRealBudgetEstimates
    (trackBLinearPrimeExpLayerMeanLowerFacts_of_concreteFloors hmass) h

/-- Subset reciprocal-mass floors plus raw-second real-budget estimates give
the concrete summed geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_subsetMass_rawEstimates
    (hmass : TrackBLinearPrimeExpConcreteFloorSubsetMassFacts)
    (h : TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawSecondRealBudgetEstimates
    (trackBLinearPrimeExpLayerMeanLowerFacts_of_subsetMass hmass) h

/-- Boundary-safe support-bulk mass facts plus raw-second real-budget estimates
give the concrete summed geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_supportBulk_rawEstimates
    (hmass : TrackBLinearPrimeExpSupportBulkMassFacts)
    (h : TrackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawSecondRealBudgetEstimates
    (trackBLinearPrimeExpLayerMeanLowerFacts_of_supportBulk hmass) h

/-- Mean lower bound plus centered-second variance estimates and harmonic
flatness budget give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centered_harmonic
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetEstimates)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredSecondRealBudgetEstimates
    hmean
    (trackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates_of_harmonic
      hvar hflat)

/-- Mean lower bound plus raw-second variance estimates and harmonic flatness
budget give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_raw_harmonic
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryRawSecondRealBudgetEstimates)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerHarmonicUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawSecondRealBudgetEstimates
    hmean
    (trackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates_of_harmonic
      hvar hflat)

/-- Mean lower bound plus centered-second variance estimates and reciprocal
flatness budget give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centered_reciprocal
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetEstimates)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredSecondRealBudgetEstimates
    hmean
    (trackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates_of_reciprocal
      hvar hflat)

/-- Mean lower bound plus raw-second variance estimates and reciprocal
flatness budget give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_raw_reciprocal
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryRawSecondRealBudgetEstimates)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerReciprocalMassUpperRealBudgetFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawSecondRealBudgetEstimates
    hmean
    (trackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates_of_reciprocal
      hvar hflat)

/-- Mean lower bound plus centered-second variance estimates and arbitrary
real-valued flatness tails give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centered_realProbability
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryCenteredSecondRealBudgetEstimates)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_centeredSecondRealBudgetEstimates
    hmean
    (trackBLinearPrimeExpGeometryCenteredSecondRealBudgetLayerFlatnessEstimates_of_realProbability
      hvar hflat)

/-- Mean lower bound plus raw-second variance estimates and arbitrary
real-valued flatness tails give the concrete geometry-good probability inputs. -/
def trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_raw_realProbability
    (hmean : TrackBLinearPrimeExpLayerMeanLowerFacts)
    (hvar : TrackBLinearPrimeExpGeometryRawSecondRealBudgetEstimates)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts) :
    TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts :=
  trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_rawSecondRealBudgetEstimates
    hmean
    (trackBLinearPrimeExpGeometryRawSecondRealBudgetLayerFlatnessEstimates_of_realProbability
      hvar hflat)

/-- The concrete probability inputs control the geometry-good complement by the
concrete summable stage budget. -/
theorem measure_trackBLinearPrimeExpGeometryGood_compl_le_concreteFail
    (h : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts) (j : ℕ) :
    mu (trackBLinearPrimeExpGeometryGood j)ᶜ ≤
      trackBLinearPrimeExpGeometryGoodConcreteFail j := by
  have hnonneg : 0 ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (by positivity) 8)
  calc
    mu (trackBLinearPrimeExpGeometryGood j)ᶜ
        ≤ (∑ r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j,
            mu (trackBLinearPrimeExpVarianceLayerBadSet j r)) +
            mu (trackBLinearPrimeExpFlatGoodCompl j) :=
          measure_trackBLinearPrimeExpGeometryGood_compl_le_variance_layer_sum_add_flatCompl j
    _ ≤ trackBLinearPrimeExpGeometryVarianceLayerSumBudget j +
          trackBLinearPrimeExpGeometryFlatBudget j := by
        exact add_le_add (h.variance_layer_sum_le j) (h.flat_compl_le j)
    _ = trackBLinearPrimeExpGeometryGoodConcreteFail j := by
        rw [trackBLinearPrimeExpGeometryVarianceLayerSumBudget,
          trackBLinearPrimeExpGeometryFlatBudget,
          trackBLinearPrimeExpGeometryGoodConcreteFail]
        rw [← ENNReal.ofReal_add hnonneg hnonneg]
        congr
        ring

/-- Stage facts for the exponential schedule using `trackBLinearPrimeExpGeometryGood`
and the concrete summable geometry failure budget. -/
def trackBLinearPrimeExpScheduleStageFactsWithGeometryGoodConcrete
    (_h : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts) :
    TrackBLinearPrimeScheduleStageFacts
      (trackBLinearPrimeExpScheduleSpecWithGood
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :=
  trackBLinearPrimeExpScheduleStageFactsWithGood
    trackBLinearPrimeExpGeometryGood
    trackBLinearPrimeExpGeometryGoodConcreteFail
    (by
      simpa [trackBLinearPrimeExpScheduleSpecWithGood] using
        trackBLinearPrimeExpGeometryGoodConcreteFail_tsum_ne_top)

/-- Good-event facts for the exponential schedule using
`trackBLinearPrimeExpGeometryGood` and the concrete summable geometry failure
budget. -/
noncomputable def trackBLinearPrimeExpScheduleGoodEventFactsWithGeometryGoodConcrete
    (h : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts) :
    TrackBLinearPrimeScheduleGoodEventFacts
      (trackBLinearPrimeExpScheduleSpecWithGood
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :=
  trackBLinearPrimeExpScheduleGoodEventFactsWithGood
    trackBLinearPrimeExpGeometryGood
    trackBLinearPrimeExpGeometryGoodConcreteFail
    measurableSet_trackBLinearPrimeExpGeometryGood
    (measure_trackBLinearPrimeExpGeometryGood_compl_le_concreteFail h)

/-- The exponential one-point upper tail bound is just the probability bound
`P(E) <= 1`, since the scalar tail-upper budget is still `1`. -/
theorem trackBLinearPrimeExp_tail_prob_le_tailUpper
    (j N : ℕ)
    (_hN : N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j) :
      mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi
              trackBLinearPrimeExpScheduleSpec.good)
            trackBLinearPrimeExpScheduleSpec.M trackBLinearPrimeExpScheduleSpec.buffer j N)
        ≤ trackBLinearPrimeExpScheduleSpec.tailUpper j := by
  have hprob :
      mu
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi
              trackBLinearPrimeExpScheduleSpec.good)
            trackBLinearPrimeExpScheduleSpec.M trackBLinearPrimeExpScheduleSpec.buffer j N)
        ≤ 1 := by
    simpa using
      (measure_mono
        (Set.subset_univ
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi
              trackBLinearPrimeExpScheduleSpec.good)
            trackBLinearPrimeExpScheduleSpec.M
            trackBLinearPrimeExpScheduleSpec.buffer j N))).trans
        (by simp)
  exact
    (ENNReal.toReal_mono ENNReal.one_ne_top hprob).trans_eq
      (by simp [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteTailUpper])

/-- The exponential product lower comparison follows from the one-point lower
comparison by the same elementary scalar inequality as the concrete wrapper. -/
theorem trackBLinearPrimeExp_tail_product_compare_lower
    (one_point_compare_lower :
      ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
          trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
        trackBLinearPrimeExpScheduleSpec.gaussianTail j N -
            trackBLinearPrimeExpScheduleSpec.onePointSlack j ≤
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore
                trackBLinearPrimeExpScheduleSpec.Q
                trackBLinearPrimeExpScheduleSpec.point
                trackBLinearPrimeExpScheduleSpec.freshLo
                trackBLinearPrimeExpScheduleSpec.freshHi
                trackBLinearPrimeExpScheduleSpec.good)
              trackBLinearPrimeExpScheduleSpec.M
              trackBLinearPrimeExpScheduleSpec.buffer j N))
    (j N N' : ℕ)
    (hN : N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j)
    (hN' : N' ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j)
    (_hne : N ≠ N') :
      trackBLinearPrimeExpScheduleSpec.gaussianTail j N *
          trackBLinearPrimeExpScheduleSpec.gaussianTail j N'
        ≤
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore
                trackBLinearPrimeExpScheduleSpec.Q
                trackBLinearPrimeExpScheduleSpec.point
                trackBLinearPrimeExpScheduleSpec.freshLo
                trackBLinearPrimeExpScheduleSpec.freshHi
                trackBLinearPrimeExpScheduleSpec.good)
              trackBLinearPrimeExpScheduleSpec.M
              trackBLinearPrimeExpScheduleSpec.buffer j N) *
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore
                trackBLinearPrimeExpScheduleSpec.Q
                trackBLinearPrimeExpScheduleSpec.point
                trackBLinearPrimeExpScheduleSpec.freshLo
                trackBLinearPrimeExpScheduleSpec.freshHi
                trackBLinearPrimeExpScheduleSpec.good)
              trackBLinearPrimeExpScheduleSpec.M
              trackBLinearPrimeExpScheduleSpec.buffer j N') +
            trackBLinearPrimeExpScheduleSpec.productSlack j := by
  set s : ℝ := (((trackBLinearPrimeConcreteBase j : ℝ) ^ 10))⁻¹
  set p : ℝ :=
    mu.real
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeScheduledCore
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          trackBLinearPrimeExpScheduleSpec.good)
        trackBLinearPrimeExpScheduleSpec.M trackBLinearPrimeExpScheduleSpec.buffer j N)
  set q : ℝ :=
    mu.real
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeScheduledCore
          trackBLinearPrimeExpScheduleSpec.Q
          trackBLinearPrimeExpScheduleSpec.point
          trackBLinearPrimeExpScheduleSpec.freshLo
          trackBLinearPrimeExpScheduleSpec.freshHi
          trackBLinearPrimeExpScheduleSpec.good)
        trackBLinearPrimeExpScheduleSpec.M trackBLinearPrimeExpScheduleSpec.buffer j N')
  have hp : (1 : ℝ) / 2 - s ≤ p := by
    have hp0 := one_point_compare_lower j N hN
    simpa [p, s, trackBLinearPrimeExpScheduleSpec,
      trackBLinearPrimeConcreteGaussianTail, trackBLinearPrimeConcreteOnePointSlack] using hp0
  have hq : (1 : ℝ) / 2 - s ≤ q := by
    have hq0 := one_point_compare_lower j N' hN'
    simpa [q, s, trackBLinearPrimeExpScheduleSpec,
      trackBLinearPrimeConcreteGaussianTail, trackBLinearPrimeConcreteOnePointSlack] using hq0
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
  simpa [s, trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteGaussianTail,
    trackBLinearPrimeConcreteProductSlack] using hfinal

/-- The only non-scalar tail fields still needed for the exponential schedule. -/
structure TrackBLinearPrimeExpScheduleTailComparisonFacts where
  one_point_compare_lower :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      trackBLinearPrimeExpScheduleSpec.gaussianTail j N -
          trackBLinearPrimeExpScheduleSpec.onePointSlack j ≤
        mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi
              trackBLinearPrimeExpScheduleSpec.good)
            trackBLinearPrimeExpScheduleSpec.M trackBLinearPrimeExpScheduleSpec.buffer j N)
  pair_compare_upper :
    ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      N' ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      N ≠ N' →
        mu.real
            (trackBThresholdPairExceedanceEvent
              (trackBLinearPrimeScheduledCore
                trackBLinearPrimeExpScheduleSpec.Q
                trackBLinearPrimeExpScheduleSpec.point
                trackBLinearPrimeExpScheduleSpec.freshLo
                trackBLinearPrimeExpScheduleSpec.freshHi
                trackBLinearPrimeExpScheduleSpec.good)
              trackBLinearPrimeExpScheduleSpec.M
              trackBLinearPrimeExpScheduleSpec.buffer j N N')
          ≤ trackBLinearPrimeExpScheduleSpec.gaussianPair j N N' +
            trackBLinearPrimeExpScheduleSpec.twoPointSlack j

/-- Exponential tail-comparison input in a Berry-Esseen-style error-budget
form.  The one-point theorem can be proved as an absolute approximation to the
Gaussian proxy, and the two-point theorem can use a separate real error term;
Lean then checks both errors against the schedule slack fields. -/
structure TrackBLinearPrimeExpScheduleTailErrorFacts where
  onePointError : ℕ → ℕ → ℝ
  pairError : ℕ → ℕ → ℕ → ℝ
  one_point_abs_error :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      |mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi
              trackBLinearPrimeExpScheduleSpec.good)
            trackBLinearPrimeExpScheduleSpec.M trackBLinearPrimeExpScheduleSpec.buffer j N) -
        trackBLinearPrimeExpScheduleSpec.gaussianTail j N| ≤ onePointError j N
  one_point_error_budget :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      onePointError j N ≤ trackBLinearPrimeExpScheduleSpec.onePointSlack j
  pair_error_upper :
    ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      N' ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      N ≠ N' →
        mu.real
            (trackBThresholdPairExceedanceEvent
              (trackBLinearPrimeScheduledCore
                trackBLinearPrimeExpScheduleSpec.Q
                trackBLinearPrimeExpScheduleSpec.point
                trackBLinearPrimeExpScheduleSpec.freshLo
                trackBLinearPrimeExpScheduleSpec.freshHi
                trackBLinearPrimeExpScheduleSpec.good)
              trackBLinearPrimeExpScheduleSpec.M
              trackBLinearPrimeExpScheduleSpec.buffer j N N')
          ≤ trackBLinearPrimeExpScheduleSpec.gaussianPair j N N' + pairError j N N'
  pair_error_budget :
    ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      N' ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      N ≠ N' →
        pairError j N N' ≤ trackBLinearPrimeExpScheduleSpec.twoPointSlack j

/-- Convert Berry-Esseen-style real error budgets into the existing exponential
tail-comparison fields. -/
def trackBLinearPrimeExpScheduleTailComparisonFacts_of_error
    (h : TrackBLinearPrimeExpScheduleTailErrorFacts) :
    TrackBLinearPrimeExpScheduleTailComparisonFacts where
  one_point_compare_lower := by
    intro j N hN
    have h_abs := h.one_point_abs_error j N hN
    have h_budget := h.one_point_error_budget j N hN
    rcases abs_le.mp h_abs with ⟨h_lower, _h_upper⟩
    linarith
  pair_compare_upper := by
    intro j N N' hN hN' hne
    have h_pair := h.pair_error_upper j N N' hN hN' hne
    have h_budget := h.pair_error_budget j N N' hN hN' hne
    linarith

/-- Assemble exponential Gaussian-tail facts from the remaining comparison
fields plus the closed scalar arithmetic shared with the concrete schedule. -/
def trackBLinearPrimeExpScheduleGaussianTailFacts_of_comparison
    (h : TrackBLinearPrimeExpScheduleTailComparisonFacts) :
    TrackBLinearPrimeScheduleGaussianTailFacts trackBLinearPrimeExpScheduleSpec where
  countMean_le_Q_beta := by
    intro j
    simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_countMean_le_Q_beta j
  tailUpper_nonneg := by
    intro j
    simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_tailUpper_nonneg j
  pairCovUpper_nonneg := by
    intro j
    simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_pairCovUpper_nonneg j
  countSecond_budget := by
    intro j
    simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_countSecond_budget j
  gaussian_one_point_lower := by
    intro j N _hN
    simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_gaussian_one_point_lower j N
  one_point_compare_lower := h.one_point_compare_lower
  tail_prob_le_tailUpper := trackBLinearPrimeExp_tail_prob_le_tailUpper
  pair_compare_upper := h.pair_compare_upper
  gaussian_pair_cov_upper := by
    intro j N N' _hN _hN' _hne
    simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_gaussian_pair_cov_upper j N N'
  tail_product_compare_lower :=
    trackBLinearPrimeExp_tail_product_compare_lower h.one_point_compare_lower
  pairCovBudget_le_pairCovUpper := by
    intro j
    simpa [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_pairCovBudget_le_pairCovUpper j

/-- Assemble exponential Gaussian-tail facts from Berry-Esseen-style real error
budgets. -/
def trackBLinearPrimeExpScheduleGaussianTailFacts_of_error
    (h : TrackBLinearPrimeExpScheduleTailErrorFacts) :
    TrackBLinearPrimeScheduleGaussianTailFacts trackBLinearPrimeExpScheduleSpec :=
  trackBLinearPrimeExpScheduleGaussianTailFacts_of_comparison
    (trackBLinearPrimeExpScheduleTailComparisonFacts_of_error h)

/-- The exponential with-good one-point upper tail bound is just the probability
bound `P(E) <= 1`, since the scalar tail-upper budget is still `1`. -/
theorem trackBLinearPrimeExpWithGood_tail_prob_le_tailUpper
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞)
    (j N : ℕ)
    (_hN : N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j) :
      mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N)
        ≤ (trackBLinearPrimeExpScheduleSpecWithGood good failGood).tailUpper j := by
  have hprob :
      mu
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N)
        ≤ 1 := by
    simpa using
      (measure_mono
        (Set.subset_univ
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N))).trans
        (by simp)
  exact
    (ENNReal.toReal_mono ENNReal.one_ne_top hprob).trans_eq
      (by simp [trackBLinearPrimeExpScheduleSpecWithGood,
        trackBLinearPrimeConcreteTailUpper])

/-- The exponential with-good product lower comparison follows from the
one-point lower comparison by the same elementary algebra as the all-space
wrapper. -/
theorem trackBLinearPrimeExpWithGood_tail_product_compare_lower
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞)
    (one_point_compare_lower :
      ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).gaussianTail j N -
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).onePointSlack j ≤
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N))
    (j N N' : ℕ)
    (hN : N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j)
    (hN' : N' ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j)
    (_hne : N ≠ N') :
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood).gaussianTail j N *
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).gaussianTail j N'
        ≤
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N) *
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N') +
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).productSlack j := by
  set s : ℝ := (((trackBLinearPrimeConcreteBase j : ℝ) ^ 10))⁻¹
  set p : ℝ :=
    mu.real
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeScheduledCore
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N)
  set q : ℝ :=
    mu.real
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeScheduledCore
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N')
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

/-- Exponential with-good one-point exceedance is the raw scheduled fresh-prime
linear exceedance intersected with the good event.  This is the convenient form
for conditional Berry-Esseen estimates. -/
theorem trackBLinearPrimeExpWithGoodThresholdExceedanceEvent_eq_good_inter_raw
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) (j N : ℕ) :
    trackBThresholdExceedanceEvent
        (trackBLinearPrimeScheduledCore
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N =
      good j ∩
        trackBThresholdExceedanceEvent
          (trackBLinearPrimeScheduledCoreRaw
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi)
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N := by
  simpa [trackBLinearPrimeScheduledCore, trackBLinearPrimeScheduledCoreRaw] using
    trackBLinearPrimeThresholdExceedanceEvent_eq_good_inter_raw
      (trackBLinearPrimeScheduledFreshSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi)
      (trackBLinearPrimeScheduledFreshCoeff
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi)
      good
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer
      j N
      (by
        simpa [trackBLinearPrimeExpScheduleSpecWithGood] using
          trackBLinearPrimeConcreteM_add_buffer_pos j)

/-- Exponential with-good pair exceedance is the raw scheduled fresh-prime
linear pair exceedance intersected with the good event. -/
theorem trackBLinearPrimeExpWithGoodThresholdPairExceedanceEvent_eq_good_inter_raw
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) (j N N' : ℕ) :
    trackBThresholdPairExceedanceEvent
        (trackBLinearPrimeScheduledCore
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N N' =
      good j ∩
        trackBThresholdPairExceedanceEvent
          (trackBLinearPrimeScheduledCoreRaw
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi)
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N N' := by
  simpa [trackBLinearPrimeScheduledCore, trackBLinearPrimeScheduledCoreRaw] using
    trackBLinearPrimeThresholdPairExceedanceEvent_eq_good_inter_raw
      (trackBLinearPrimeScheduledFreshSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi)
      (trackBLinearPrimeScheduledFreshCoeff
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi)
      good
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer
      j N N'
      (by
        simpa [trackBLinearPrimeExpScheduleSpecWithGood] using
          trackBLinearPrimeConcreteM_add_buffer_pos j)

/-- The only non-scalar tail fields still needed for the exponential schedule
with a configurable analytic good event. -/
structure TrackBLinearPrimeExpScheduleWithGoodTailComparisonFacts
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) where
  one_point_compare_lower :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood).gaussianTail j N -
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).onePointSlack j ≤
        mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N)
  pair_compare_upper :
    ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      N' ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      N ≠ N' →
        mu.real
            (trackBThresholdPairExceedanceEvent
              (trackBLinearPrimeScheduledCore
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N N')
          ≤ (trackBLinearPrimeExpScheduleSpecWithGood good failGood).gaussianPair j N N' +
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).twoPointSlack j

/-- Exponential with-good tail-comparison input in a Berry-Esseen-style
error-budget form. -/
structure TrackBLinearPrimeExpScheduleWithGoodTailErrorFacts
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) where
  onePointError : ℕ → ℕ → ℝ
  pairError : ℕ → ℕ → ℕ → ℝ
  one_point_abs_error :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      |mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
            (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N) -
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).gaussianTail j N| ≤
        onePointError j N
  one_point_error_budget :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      onePointError j N ≤
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).onePointSlack j
  pair_error_upper :
    ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      N' ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      N ≠ N' →
        mu.real
            (trackBThresholdPairExceedanceEvent
              (trackBLinearPrimeScheduledCore
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good)
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N N')
          ≤ (trackBLinearPrimeExpScheduleSpecWithGood good failGood).gaussianPair j N N' +
            pairError j N N'
  pair_error_budget :
    ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      N' ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      N ≠ N' →
        pairError j N N' ≤
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).twoPointSlack j

/-- Exponential with-good tail-error input stated directly for the raw
scheduled fresh-prime linear core, intersected with the good event.  This is
the form produced by conditioning on the complement of the fresh-prime signs. -/
structure TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) where
  onePointError : ℕ → ℕ → ℝ
  pairError : ℕ → ℕ → ℕ → ℝ
  one_point_abs_error :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      |mu.real
          (good j ∩
            trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCoreRaw
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi)
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N) -
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).gaussianTail j N| ≤
        onePointError j N
  one_point_error_budget :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      onePointError j N ≤
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).onePointSlack j
  pair_error_upper :
    ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      N' ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      N ≠ N' →
        mu.real
            (good j ∩
              trackBThresholdPairExceedanceEvent
                (trackBLinearPrimeScheduledCoreRaw
                  (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
                  (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
                  (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
                  (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi)
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).M
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j N N')
          ≤ (trackBLinearPrimeExpScheduleSpecWithGood good failGood).gaussianPair j N N' +
            pairError j N N'
  pair_error_budget :
    ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      N' ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      N ≠ N' →
        pairError j N N' ≤
          (trackBLinearPrimeExpScheduleSpecWithGood good failGood).twoPointSlack j

/-- Convert raw scheduled-core tail-error facts to masked with-good tail-error
facts using the positive-threshold raw/masked event identities. -/
def trackBLinearPrimeExpScheduleWithGoodTailErrorFacts_of_rawError
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts good failGood) :
    TrackBLinearPrimeExpScheduleWithGoodTailErrorFacts good failGood where
  onePointError := h.onePointError
  pairError := h.pairError
  one_point_abs_error := by
    intro j N hN
    simpa [trackBLinearPrimeExpWithGoodThresholdExceedanceEvent_eq_good_inter_raw
      good failGood j N] using h.one_point_abs_error j N hN
  one_point_error_budget := h.one_point_error_budget
  pair_error_upper := by
    intro j N N' hN hN' hne
    simpa [trackBLinearPrimeExpWithGoodThresholdPairExceedanceEvent_eq_good_inter_raw
      good failGood j N N'] using h.pair_error_upper j N N' hN hN' hne
  pair_error_budget := h.pair_error_budget

/-- Convert Berry-Esseen-style real error budgets into the existing with-good
tail-comparison fields. -/
def trackBLinearPrimeExpScheduleWithGoodTailComparisonFacts_of_error
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeExpScheduleWithGoodTailErrorFacts good failGood) :
    TrackBLinearPrimeExpScheduleWithGoodTailComparisonFacts good failGood where
  one_point_compare_lower := by
    intro j N hN
    have h_abs := h.one_point_abs_error j N hN
    have h_budget := h.one_point_error_budget j N hN
    rcases abs_le.mp h_abs with ⟨h_lower, _h_upper⟩
    linarith
  pair_compare_upper := by
    intro j N N' hN hN' hne
    have h_pair := h.pair_error_upper j N N' hN hN' hne
    have h_budget := h.pair_error_budget j N N' hN hN' hne
    linarith

/-- Convert raw scheduled-core tail-error facts directly into the existing
with-good tail-comparison fields. -/
def trackBLinearPrimeExpScheduleWithGoodTailComparisonFacts_of_rawError
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts good failGood) :
    TrackBLinearPrimeExpScheduleWithGoodTailComparisonFacts good failGood :=
  trackBLinearPrimeExpScheduleWithGoodTailComparisonFacts_of_error
    (trackBLinearPrimeExpScheduleWithGoodTailErrorFacts_of_rawError h)

/-- Assemble exponential with-good Gaussian-tail facts from the remaining
comparison fields plus the closed scalar arithmetic shared with the concrete
schedule. -/
def trackBLinearPrimeExpScheduleWithGoodGaussianTailFacts_of_comparison
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeExpScheduleWithGoodTailComparisonFacts good failGood) :
    TrackBLinearPrimeScheduleGaussianTailFacts
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood) where
  countMean_le_Q_beta := by
    intro j
    simpa [trackBLinearPrimeExpScheduleSpecWithGood, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_countMean_le_Q_beta j
  tailUpper_nonneg := by
    intro j
    simpa [trackBLinearPrimeExpScheduleSpecWithGood, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_tailUpper_nonneg j
  pairCovUpper_nonneg := by
    intro j
    simpa [trackBLinearPrimeExpScheduleSpecWithGood, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_pairCovUpper_nonneg j
  countSecond_budget := by
    intro j
    simpa [trackBLinearPrimeExpScheduleSpecWithGood, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_countSecond_budget j
  gaussian_one_point_lower := by
    intro j N _hN
    simpa [trackBLinearPrimeExpScheduleSpecWithGood, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_gaussian_one_point_lower j N
  one_point_compare_lower := h.one_point_compare_lower
  tail_prob_le_tailUpper :=
    trackBLinearPrimeExpWithGood_tail_prob_le_tailUpper good failGood
  pair_compare_upper := h.pair_compare_upper
  gaussian_pair_cov_upper := by
    intro j N N' _hN _hN' _hne
    simpa [trackBLinearPrimeExpScheduleSpecWithGood, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_gaussian_pair_cov_upper j N N'
  tail_product_compare_lower :=
    trackBLinearPrimeExpWithGood_tail_product_compare_lower
      good failGood h.one_point_compare_lower
  pairCovBudget_le_pairCovUpper := by
    intro j
    simpa [trackBLinearPrimeExpScheduleSpecWithGood, trackBLinearPrimeConcreteScheduleSpec] using
      trackBLinearPrimeConcrete_pairCovBudget_le_pairCovUpper j

/-- Assemble exponential with-good Gaussian-tail facts from Berry-Esseen-style
real error budgets. -/
def trackBLinearPrimeExpScheduleWithGoodGaussianTailFacts_of_error
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeExpScheduleWithGoodTailErrorFacts good failGood) :
    TrackBLinearPrimeScheduleGaussianTailFacts
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood) :=
  trackBLinearPrimeExpScheduleWithGoodGaussianTailFacts_of_comparison
    (trackBLinearPrimeExpScheduleWithGoodTailComparisonFacts_of_error h)

/-- Assemble exponential with-good Gaussian-tail facts from raw scheduled-core
real error budgets. -/
def trackBLinearPrimeExpScheduleWithGoodGaussianTailFacts_of_rawError
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts good failGood) :
    TrackBLinearPrimeScheduleGaussianTailFacts
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood) :=
  trackBLinearPrimeExpScheduleWithGoodGaussianTailFacts_of_comparison
    (trackBLinearPrimeExpScheduleWithGoodTailComparisonFacts_of_rawError h)

/-- Exponential one-point bad-remainder budget.  The corrected endpoint branch
keeps the same summable `base^-8` per-point budget as the diagnostic concrete
schedule. -/
noncomputable def trackBLinearPrimeExpSingleRemainderFail (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹)

/-- The exponential threshold buffer is positive at every stage. -/
theorem trackBLinearPrimeExpBuffer_pos (j : ℕ) :
    0 < trackBLinearPrimeExpScheduleSpec.buffer j := by
  change 0 < trackBLinearPrimeConcreteBuffer j
  unfold trackBLinearPrimeConcreteBuffer
  have hM : 0 < trackBLinearPrimeConcreteM j := trackBLinearPrimeConcreteM_pos j
  linarith

/-- Real-valued scalar budget helper for the exponential remainder
second-moment interface. -/
theorem trackBLinearPrimeExp_remainder_second_budget_of_real_bound
    (remainderSecond : ℕ → ℕ → ℝ) (j N : ℕ)
    (hsecond :
      remainderSecond j N ≤
        (trackBLinearPrimeExpScheduleSpec.buffer j) ^ 2 *
          (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹) :
    ENNReal.ofReal
        (remainderSecond j N / (trackBLinearPrimeExpScheduleSpec.buffer j) ^ 2)
      ≤ trackBLinearPrimeExpSingleRemainderFail j := by
  have hbuffer_sq : 0 < (trackBLinearPrimeExpScheduleSpec.buffer j) ^ 2 :=
    pow_pos (trackBLinearPrimeExpBuffer_pos j) 2
  have hreal :
      remainderSecond j N / (trackBLinearPrimeExpScheduleSpec.buffer j) ^ 2 ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹ := by
    rw [div_le_iff₀ hbuffer_sq]
    simpa [mul_comm] using hsecond
  simpa [trackBLinearPrimeExpSingleRemainderFail] using
    ENNReal.ofReal_le_ofReal hreal

/-- The exponential selected-remainder finite-union budget. -/
theorem trackBLinearPrimeExp_remainder_union_budget (j : ℕ) :
    (trackBLinearPrimeExpScheduleSpec.Q j) •
        trackBLinearPrimeExpSingleRemainderFail j ≤
      trackBLinearPrimeExpScheduleSpec.failOverlap j := by
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
    (trackBLinearPrimeExpScheduleSpec.Q j) •
        trackBLinearPrimeExpSingleRemainderFail j
        = ENNReal.ofReal
            ((trackBLinearPrimeConcreteQ j : ℝ) *
              (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹) := by
          change trackBLinearPrimeConcreteQ j •
              ENNReal.ofReal ((((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹) =
            ENNReal.ofReal
              ((trackBLinearPrimeConcreteQ j : ℝ) *
                (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹)
          rw [← ENNReal.ofReal_nsmul]
          simp [nsmul_eq_mul]
    _ = trackBLinearPrimeExpScheduleSpec.failOverlap j := by
          simp [trackBLinearPrimeExpScheduleSpec, trackBLinearPrimeConcreteFailOverlap,
            hreal]
    _ ≤ trackBLinearPrimeExpScheduleSpec.failOverlap j := le_rfl

/-- The only analytic selected-remainder field still needed for the
exponential schedule. -/
structure TrackBLinearPrimeExpScheduleRemainderAnalyticFacts where
  one_point_remainder_bad :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      mu
          {omega |
            trackBLinearPrimeScheduledRemainder
                trackBLinearPrimeExpScheduleSpec.Q
                trackBLinearPrimeExpScheduleSpec.point
                trackBLinearPrimeExpScheduleSpec.freshLo
                trackBLinearPrimeExpScheduleSpec.freshHi
                trackBLinearPrimeExpScheduleSpec.good omega j N <
              -trackBLinearPrimeExpScheduleSpec.buffer j}
        ≤ trackBLinearPrimeExpSingleRemainderFail j

/-- Exponential selected-remainder input in the square-moment form produced by
boundary, flat-tail, and complete-transfer estimates. -/
structure TrackBLinearPrimeExpScheduleRemainderSecondMomentFacts where
  remainderSecond : ℕ → ℕ → ℝ
  second_integrable :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeScheduledRemainder
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi
              trackBLinearPrimeExpScheduleSpec.good omega j N) ^ 2) mu
  second_upper :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      (∫ omega,
          (trackBLinearPrimeScheduledRemainder
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi
              trackBLinearPrimeExpScheduleSpec.good omega j N) ^ 2 ∂mu)
        ≤ remainderSecond j N
  second_budget :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      ENNReal.ofReal
          (remainderSecond j N / (trackBLinearPrimeExpScheduleSpec.buffer j) ^ 2)
        ≤ trackBLinearPrimeExpSingleRemainderFail j

/-- Exponential selected-remainder input in the natural real-valued
square-moment budget form.  Analytic estimates usually prove the numerator
bound `E[Rem^2] <= buffer_j^2 * base_j^-8`; Lean converts this to the
`ENNReal` one-point Markov budget. -/
structure TrackBLinearPrimeExpScheduleRemainderSecondMomentRealBudgetFacts where
  remainderSecond : ℕ → ℕ → ℝ
  second_integrable :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeScheduledRemainder
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi
              trackBLinearPrimeExpScheduleSpec.good omega j N) ^ 2) mu
  second_upper :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      (∫ omega,
          (trackBLinearPrimeScheduledRemainder
              trackBLinearPrimeExpScheduleSpec.Q
              trackBLinearPrimeExpScheduleSpec.point
              trackBLinearPrimeExpScheduleSpec.freshLo
              trackBLinearPrimeExpScheduleSpec.freshHi
              trackBLinearPrimeExpScheduleSpec.good omega j N) ^ 2 ∂mu)
        ≤ remainderSecond j N
  second_real_budget :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeExpScheduleSpec.Q trackBLinearPrimeExpScheduleSpec.point j →
      remainderSecond j N ≤
        (trackBLinearPrimeExpScheduleSpec.buffer j) ^ 2 *
          (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹

/-- Assemble exponential selected-remainder facts from the remaining one-point
bad-remainder estimate plus the proved union budget. -/
def trackBLinearPrimeExpScheduleRemainderFacts_of_analytic
    (h : TrackBLinearPrimeExpScheduleRemainderAnalyticFacts) :
    TrackBLinearPrimeScheduleRemainderFacts trackBLinearPrimeExpScheduleSpec where
  singleFail := trackBLinearPrimeExpSingleRemainderFail
  one_point_remainder_bad := h.one_point_remainder_bad
  union_budget := trackBLinearPrimeExp_remainder_union_budget

/-- Assemble exponential one-point selected-remainder facts from square-moment
estimates. -/
def trackBLinearPrimeExpScheduleRemainderAnalyticFacts_of_secondMoment
    (h : TrackBLinearPrimeExpScheduleRemainderSecondMomentFacts) :
    TrackBLinearPrimeExpScheduleRemainderAnalyticFacts where
  one_point_remainder_bad := by
    intro j N hN
    exact
      (measure_trackBLinearPrimeScheduledRemainder_lt_neg_le_second
        trackBLinearPrimeExpScheduleSpec h.remainderSecond j N
        (trackBLinearPrimeExpBuffer_pos j)
        (h.second_integrable j N hN) (h.second_upper j N hN)).trans
        (h.second_budget j N hN)

/-- Directly assemble exponential schedule remainder facts from square moments. -/
def trackBLinearPrimeExpScheduleRemainderFacts_of_secondMoment
    (h : TrackBLinearPrimeExpScheduleRemainderSecondMomentFacts) :
    TrackBLinearPrimeScheduleRemainderFacts trackBLinearPrimeExpScheduleSpec :=
  trackBLinearPrimeExpScheduleRemainderFacts_of_analytic
    (trackBLinearPrimeExpScheduleRemainderAnalyticFacts_of_secondMoment h)

/-- Convert natural real-budget square-moment selected-remainder facts to the
existing `ENNReal` second-moment package. -/
def trackBLinearPrimeExpScheduleRemainderSecondMomentFacts_of_realBudget
    (h : TrackBLinearPrimeExpScheduleRemainderSecondMomentRealBudgetFacts) :
    TrackBLinearPrimeExpScheduleRemainderSecondMomentFacts where
  remainderSecond := h.remainderSecond
  second_integrable := h.second_integrable
  second_upper := h.second_upper
  second_budget := by
    intro j N hN
    exact trackBLinearPrimeExp_remainder_second_budget_of_real_bound
      h.remainderSecond j N (h.second_real_budget j N hN)

/-- Assemble exponential one-point selected-remainder facts from natural
real-budget square-moment estimates. -/
def trackBLinearPrimeExpScheduleRemainderAnalyticFacts_of_secondMomentRealBudget
    (h : TrackBLinearPrimeExpScheduleRemainderSecondMomentRealBudgetFacts) :
    TrackBLinearPrimeExpScheduleRemainderAnalyticFacts :=
  trackBLinearPrimeExpScheduleRemainderAnalyticFacts_of_secondMoment
    (trackBLinearPrimeExpScheduleRemainderSecondMomentFacts_of_realBudget h)

/-- Directly assemble exponential schedule remainder facts from natural
real-budget square moments. -/
def trackBLinearPrimeExpScheduleRemainderFacts_of_secondMomentRealBudget
    (h : TrackBLinearPrimeExpScheduleRemainderSecondMomentRealBudgetFacts) :
    TrackBLinearPrimeScheduleRemainderFacts trackBLinearPrimeExpScheduleSpec :=
  trackBLinearPrimeExpScheduleRemainderFacts_of_secondMoment
    (trackBLinearPrimeExpScheduleRemainderSecondMomentFacts_of_realBudget h)

/-- The exponential with-good threshold buffer is positive at every stage. -/
theorem trackBLinearPrimeExpWithGoodBuffer_pos
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) (j : ℕ) :
    0 < (trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j := by
  simpa [trackBLinearPrimeExpScheduleSpecWithGood] using trackBLinearPrimeExpBuffer_pos j

/-- The exponential with-good selected-remainder finite-union budget. -/
theorem trackBLinearPrimeExpWithGood_remainder_union_budget
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) (j : ℕ) :
    ((trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q j) •
        trackBLinearPrimeExpSingleRemainderFail j ≤
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood).failOverlap j := by
  simpa [trackBLinearPrimeExpScheduleSpecWithGood] using
    trackBLinearPrimeExp_remainder_union_budget j

/-- The only analytic selected-remainder field still needed for the
exponential schedule with a configurable analytic good event. -/
structure TrackBLinearPrimeExpScheduleWithGoodRemainderAnalyticFacts
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) where
  one_point_remainder_bad :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      mu
          {omega |
            trackBLinearPrimeScheduledRemainder
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
                (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good omega j N <
              -(trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j}
        ≤ trackBLinearPrimeExpSingleRemainderFail j

/-- Exponential with-good selected-remainder input in square-moment form. -/
structure TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentFacts
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) where
  remainderSecond : ℕ → ℕ → ℝ
  second_integrable :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeScheduledRemainder
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good omega j N) ^ 2) mu
  second_upper :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      (∫ omega,
          (trackBLinearPrimeScheduledRemainder
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good omega j N) ^ 2 ∂mu)
        ≤ remainderSecond j N
  second_budget :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      ENNReal.ofReal
          (remainderSecond j N /
            ((trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j) ^ 2)
        ≤ trackBLinearPrimeExpSingleRemainderFail j

/-- Exponential with-good selected-remainder input in the natural real-valued
square-moment budget form. -/
structure TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) where
  remainderSecond : ℕ → ℕ → ℝ
  second_integrable :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      Integrable
        (fun omega =>
          (trackBLinearPrimeScheduledRemainder
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good omega j N) ^ 2) mu
  second_upper :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      (∫ omega,
          (trackBLinearPrimeScheduledRemainder
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshLo
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).freshHi
              (trackBLinearPrimeExpScheduleSpecWithGood good failGood).good omega j N) ^ 2 ∂mu)
        ≤ remainderSecond j N
  second_real_budget :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood).point j →
      remainderSecond j N ≤
        ((trackBLinearPrimeExpScheduleSpecWithGood good failGood).buffer j) ^ 2 *
          (((trackBLinearPrimeConcreteBase j : ℝ) ^ 8))⁻¹

/-- Assemble exponential with-good selected-remainder facts from the remaining
one-point bad-remainder estimate plus the proved union budget. -/
def trackBLinearPrimeExpScheduleWithGoodRemainderFacts_of_analytic
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeExpScheduleWithGoodRemainderAnalyticFacts good failGood) :
    TrackBLinearPrimeScheduleRemainderFacts
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood) where
  singleFail := trackBLinearPrimeExpSingleRemainderFail
  one_point_remainder_bad := h.one_point_remainder_bad
  union_budget := trackBLinearPrimeExpWithGood_remainder_union_budget good failGood

/-- Assemble exponential with-good one-point selected-remainder facts from
square-moment estimates. -/
def trackBLinearPrimeExpScheduleWithGoodRemainderAnalyticFacts_of_secondMoment
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentFacts good failGood) :
    TrackBLinearPrimeExpScheduleWithGoodRemainderAnalyticFacts good failGood where
  one_point_remainder_bad := by
    intro j N hN
    exact
      (measure_trackBLinearPrimeScheduledRemainder_lt_neg_le_second
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood) h.remainderSecond j N
        (trackBLinearPrimeExpWithGoodBuffer_pos good failGood j)
        (h.second_integrable j N hN) (h.second_upper j N hN)).trans
        (h.second_budget j N hN)

/-- Directly assemble exponential with-good schedule remainder facts from square
moments. -/
def trackBLinearPrimeExpScheduleWithGoodRemainderFacts_of_secondMoment
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentFacts good failGood) :
    TrackBLinearPrimeScheduleRemainderFacts
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood) :=
  trackBLinearPrimeExpScheduleWithGoodRemainderFacts_of_analytic
    (trackBLinearPrimeExpScheduleWithGoodRemainderAnalyticFacts_of_secondMoment h)

/-- Convert natural real-budget square-moment with-good selected-remainder
facts to the existing `ENNReal` second-moment package. -/
def trackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentFacts_of_realBudget
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts good failGood) :
    TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentFacts good failGood where
  remainderSecond := h.remainderSecond
  second_integrable := h.second_integrable
  second_upper := h.second_upper
  second_budget := by
    intro j N hN
    simpa [trackBLinearPrimeExpScheduleSpecWithGood] using
      trackBLinearPrimeExp_remainder_second_budget_of_real_bound h.remainderSecond j N
        (by
          simpa [trackBLinearPrimeExpScheduleSpecWithGood] using h.second_real_budget j N hN)

/-- Assemble exponential with-good one-point selected-remainder facts from
natural real-budget square-moment estimates. -/
def trackBLinearPrimeExpScheduleWithGoodRemainderAnalyticFacts_of_secondMomentRealBudget
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts good failGood) :
    TrackBLinearPrimeExpScheduleWithGoodRemainderAnalyticFacts good failGood :=
  trackBLinearPrimeExpScheduleWithGoodRemainderAnalyticFacts_of_secondMoment
    (trackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentFacts_of_realBudget h)

/-- Directly assemble exponential with-good schedule remainder facts from
natural real-budget square moments. -/
def trackBLinearPrimeExpScheduleWithGoodRemainderFacts_of_secondMomentRealBudget
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts good failGood) :
    TrackBLinearPrimeScheduleRemainderFacts
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood) :=
  trackBLinearPrimeExpScheduleWithGoodRemainderFacts_of_secondMoment
    (trackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentFacts_of_realBudget h)

/-- Single Lean-facing analytic package for the corrected exponential endpoint
schedule. -/
structure TrackBLinearPrimeExpScheduleAnalyticFacts where
  geometry : TrackBLinearPrimeExpScheduleDirectGeometryAnalyticFacts
  tails : TrackBLinearPrimeExpScheduleTailComparisonFacts
  remainder : TrackBLinearPrimeExpScheduleRemainderAnalyticFacts

/-- Build the scheduled Gaussian-comparison certificate from the corrected
exponential endpoint analytic package. -/
noncomputable def
    trackBLinearPrimeScheduledGaussianComparisonCertificate_of_expScheduleAnalyticFacts
    (h : TrackBLinearPrimeExpScheduleAnalyticFacts) :
    TrackBLinearPrimeScheduledGaussianComparisonCertificate :=
  trackBLinearPrimeScheduledGaussianComparisonCertificate_of_scheduleDirectGeometryFacts
    trackBLinearPrimeExpScheduleStageFacts
    trackBLinearPrimeExpScheduleGoodEventFacts
    (trackBLinearPrimeExpScheduleDirectGeometryFacts_of_analytic h.geometry)
    (trackBLinearPrimeExpScheduleGaussianTailFacts_of_comparison h.tails)
    (trackBLinearPrimeExpScheduleRemainderFacts_of_analytic h.remainder)

/-- Final theorem handoff for the corrected exponential endpoint schedule.
`Final.lean` should use this only after the analytic package is actually
instantiated. -/
theorem erdos1144_of_trackBLinearPrimeExpScheduleAnalyticFacts
    (h : TrackBLinearPrimeExpScheduleAnalyticFacts) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeScheduledGaussianComparisonCertificate
    (trackBLinearPrimeScheduledGaussianComparisonCertificate_of_expScheduleAnalyticFacts h)

/-- Direct final handoff for the corrected exponential endpoint schedule when
the tail comparison is supplied in Berry-Esseen-style real error-budget form. -/
theorem erdos1144_of_trackBLinearPrimeExpSchedule_tailError
    (hgeometry : TrackBLinearPrimeExpScheduleDirectGeometryAnalyticFacts)
    (htails : TrackBLinearPrimeExpScheduleTailErrorFacts)
    (hremainder : TrackBLinearPrimeExpScheduleRemainderAnalyticFacts) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExpScheduleAnalyticFacts
    { geometry := hgeometry
      tails := trackBLinearPrimeExpScheduleTailComparisonFacts_of_error htails
      remainder := hremainder }

/-- Variant of the corrected exponential analytic package whose remainder
input is supplied by square-moment estimates. -/
structure TrackBLinearPrimeExpScheduleSecondMomentAnalyticFacts where
  geometry : TrackBLinearPrimeExpScheduleDirectGeometryAnalyticFacts
  tails : TrackBLinearPrimeExpScheduleTailComparisonFacts
  remainder : TrackBLinearPrimeExpScheduleRemainderSecondMomentFacts

/-- Variant of the corrected exponential analytic package whose selected
remainder is supplied by a natural real-valued square-moment budget. -/
structure TrackBLinearPrimeExpScheduleSecondMomentRealBudgetAnalyticFacts where
  geometry : TrackBLinearPrimeExpScheduleDirectGeometryAnalyticFacts
  tails : TrackBLinearPrimeExpScheduleTailComparisonFacts
  remainder : TrackBLinearPrimeExpScheduleRemainderSecondMomentRealBudgetFacts

/-- Convert the square-moment remainder variant to the one-point remainder
variant of the exponential analytic package. -/
def trackBLinearPrimeExpScheduleAnalyticFacts_of_secondMoment
    (h : TrackBLinearPrimeExpScheduleSecondMomentAnalyticFacts) :
    TrackBLinearPrimeExpScheduleAnalyticFacts where
  geometry := h.geometry
  tails := h.tails
  remainder := trackBLinearPrimeExpScheduleRemainderAnalyticFacts_of_secondMoment h.remainder

/-- Convert the natural real-budget selected-remainder variant to the
square-moment package. -/
def trackBLinearPrimeExpScheduleSecondMomentAnalyticFacts_of_realBudget
    (h : TrackBLinearPrimeExpScheduleSecondMomentRealBudgetAnalyticFacts) :
    TrackBLinearPrimeExpScheduleSecondMomentAnalyticFacts where
  geometry := h.geometry
  tails := h.tails
  remainder := trackBLinearPrimeExpScheduleRemainderSecondMomentFacts_of_realBudget h.remainder

/-- Convert the natural real-budget selected-remainder variant to the one-point
remainder analytic package. -/
def trackBLinearPrimeExpScheduleAnalyticFacts_of_secondMomentRealBudget
    (h : TrackBLinearPrimeExpScheduleSecondMomentRealBudgetAnalyticFacts) :
    TrackBLinearPrimeExpScheduleAnalyticFacts :=
  trackBLinearPrimeExpScheduleAnalyticFacts_of_secondMoment
    (trackBLinearPrimeExpScheduleSecondMomentAnalyticFacts_of_realBudget h)

/-- Final theorem handoff for the corrected exponential endpoint schedule with
square-moment remainder input. -/
theorem erdos1144_of_trackBLinearPrimeExpScheduleSecondMomentAnalyticFacts
    (h : TrackBLinearPrimeExpScheduleSecondMomentAnalyticFacts) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExpScheduleAnalyticFacts
    (trackBLinearPrimeExpScheduleAnalyticFacts_of_secondMoment h)

/-- Direct final handoff for the corrected exponential endpoint schedule with
Berry-Esseen-style real tail errors and square-moment selected-remainder
input. -/
theorem erdos1144_of_trackBLinearPrimeExpSchedule_tailError_secondMoment
    (hgeometry : TrackBLinearPrimeExpScheduleDirectGeometryAnalyticFacts)
    (htails : TrackBLinearPrimeExpScheduleTailErrorFacts)
    (hremainder : TrackBLinearPrimeExpScheduleRemainderSecondMomentFacts) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExpScheduleSecondMomentAnalyticFacts
    { geometry := hgeometry
      tails := trackBLinearPrimeExpScheduleTailComparisonFacts_of_error htails
      remainder := hremainder }

/-- Final theorem handoff for the corrected exponential endpoint schedule with
natural real-budget square-moment selected-remainder input. -/
theorem erdos1144_of_trackBLinearPrimeExpScheduleSecondMomentRealBudgetAnalyticFacts
    (h : TrackBLinearPrimeExpScheduleSecondMomentRealBudgetAnalyticFacts) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExpScheduleSecondMomentAnalyticFacts
    (trackBLinearPrimeExpScheduleSecondMomentAnalyticFacts_of_realBudget h)

/-- Direct final handoff for the corrected exponential endpoint schedule with
Berry-Esseen-style real tail errors and natural real-budget square-moment
selected-remainder input. -/
theorem erdos1144_of_trackBLinearPrimeExpSchedule_tailError_secondMomentRealBudget
    (hgeometry : TrackBLinearPrimeExpScheduleDirectGeometryAnalyticFacts)
    (htails : TrackBLinearPrimeExpScheduleTailErrorFacts)
    (hremainder : TrackBLinearPrimeExpScheduleRemainderSecondMomentRealBudgetFacts) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExpScheduleSecondMomentRealBudgetAnalyticFacts
    { geometry := hgeometry
      tails := trackBLinearPrimeExpScheduleTailComparisonFacts_of_error htails
      remainder := hremainder }

/-- Direct closure from the corrected exponential endpoint schedule with a
genuine analytic good event.  This generic form is useful when the analytic
geometry/tail/remainder estimates are most naturally stated directly as
schedule fact groups. -/
theorem erdos1144_of_trackBLinearPrimeExpScheduleWithGoodFacts
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (hfail :
      (∑' j, (trackBLinearPrimeExpScheduleSpecWithGood good failGood).failGood j)
        ≠ ⊤)
    (good_measurable : ∀ j, MeasurableSet (good j))
    (prob_good_compl : ∀ j, mu (good j)ᶜ ≤ failGood j)
    (geom :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood))
    (tails :
      TrackBLinearPrimeScheduleGaussianTailFacts
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood))
    (rem :
      TrackBLinearPrimeScheduleRemainderFacts
        (trackBLinearPrimeExpScheduleSpecWithGood good failGood)) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeScheduleDirectGeometryFacts
    (trackBLinearPrimeExpScheduleStageFactsWithGood good failGood hfail)
    (trackBLinearPrimeExpScheduleGoodEventFactsWithGood
      good failGood good_measurable prob_good_compl)
    geom tails rem

/-- Single generic package for the corrected exponential endpoint schedule with
a genuine high-probability good event. -/
structure TrackBLinearPrimeExpScheduleWithGoodFacts where
  good : ℕ → Set Omega
  failGood : ℕ → ℝ≥0∞
  failGood_summable :
    (∑' j, (trackBLinearPrimeExpScheduleSpecWithGood good failGood).failGood j)
      ≠ ⊤
  good_measurable : ∀ j, MeasurableSet (good j)
  prob_good_compl : ∀ j, mu (good j)ᶜ ≤ failGood j
  geometry :
    TrackBLinearPrimeScheduleDirectGeometryFacts
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood)
  tails :
    TrackBLinearPrimeScheduleGaussianTailFacts
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood)
  remainder :
    TrackBLinearPrimeScheduleRemainderFacts
      (trackBLinearPrimeExpScheduleSpecWithGood good failGood)

/-- Final theorem handoff for the corrected exponential endpoint schedule with
a genuine high-probability good event. -/
theorem erdos1144_of_trackBLinearPrimeExpScheduleWithGoodFactsPackage
    (h : TrackBLinearPrimeExpScheduleWithGoodFacts) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExpScheduleWithGoodFacts
    h.failGood_summable h.good_measurable h.prob_good_compl
    h.geometry h.tails h.remainder

/-- Single Lean-facing package for the exponential schedule using
`trackBLinearPrimeExpGeometryGood` as the high-probability good event and the
concrete summable geometry failure budget. -/
structure TrackBLinearPrimeExpScheduleGeometryGoodConcreteAnalyticFacts where
  probability : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts
  geometry :
    TrackBLinearPrimeScheduleDirectGeometryFacts
      (trackBLinearPrimeExpScheduleSpecWithGood
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
  tails :
    TrackBLinearPrimeExpScheduleWithGoodTailComparisonFacts
      trackBLinearPrimeExpGeometryGood
      trackBLinearPrimeExpGeometryGoodConcreteFail
  remainder :
    TrackBLinearPrimeExpScheduleWithGoodRemainderAnalyticFacts
      trackBLinearPrimeExpGeometryGood
      trackBLinearPrimeExpGeometryGoodConcreteFail

/-- Final theorem handoff for the corrected exponential endpoint schedule using
the concrete geometry-good probability budget. -/
theorem erdos1144_of_trackBLinearPrimeExpScheduleGeometryGoodConcreteAnalyticFacts
    (h : TrackBLinearPrimeExpScheduleGeometryGoodConcreteAnalyticFacts) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeScheduleDirectGeometryFacts
    (trackBLinearPrimeExpScheduleStageFactsWithGeometryGoodConcrete h.probability)
    (trackBLinearPrimeExpScheduleGoodEventFactsWithGeometryGoodConcrete h.probability)
    h.geometry
    (trackBLinearPrimeExpScheduleWithGoodGaussianTailFacts_of_comparison h.tails)
    (trackBLinearPrimeExpScheduleWithGoodRemainderFacts_of_analytic h.remainder)

/-- Direct final handoff from the four independent geometry-good concrete
inputs, avoiding manual construction of the endpoint package. -/
theorem erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability
    (hprob : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodTailComparisonFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderAnalyticFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExpScheduleGeometryGoodConcreteAnalyticFacts
    { probability := hprob
      geometry := hgeometry
      tails := htails
      remainder := hremainder }

/-- Direct final handoff from the geometry-good concrete inputs when the tail
comparison is supplied in Berry-Esseen-style real error-budget form. -/
theorem erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_tailError
    (hprob : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderAnalyticFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability
    hprob hgeometry
    (trackBLinearPrimeExpScheduleWithGoodTailComparisonFacts_of_error htails)
    hremainder

/-- Direct final handoff from the geometry-good concrete inputs when the tail
comparison is supplied as raw scheduled-core real error budgets. -/
theorem erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_rawTailError
    (hprob : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderAnalyticFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_tailError
    hprob hgeometry
    (trackBLinearPrimeExpScheduleWithGoodTailErrorFacts_of_rawError htails)
    hremainder

/-- Variant of the geometry-good concrete package whose selected-remainder
input is supplied by square-moment estimates. -/
structure TrackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentAnalyticFacts where
  probability : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts
  geometry :
    TrackBLinearPrimeScheduleDirectGeometryFacts
      (trackBLinearPrimeExpScheduleSpecWithGood
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
  tails :
    TrackBLinearPrimeExpScheduleWithGoodTailComparisonFacts
      trackBLinearPrimeExpGeometryGood
      trackBLinearPrimeExpGeometryGoodConcreteFail
  remainder :
    TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentFacts
      trackBLinearPrimeExpGeometryGood
      trackBLinearPrimeExpGeometryGoodConcreteFail

/-- Variant of the geometry-good concrete package whose selected-remainder
input is supplied by a natural real-valued square-moment budget. -/
structure TrackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentRealBudgetAnalyticFacts where
  probability : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts
  geometry :
    TrackBLinearPrimeScheduleDirectGeometryFacts
      (trackBLinearPrimeExpScheduleSpecWithGood
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
  tails :
    TrackBLinearPrimeExpScheduleWithGoodTailComparisonFacts
      trackBLinearPrimeExpGeometryGood
      trackBLinearPrimeExpGeometryGoodConcreteFail
  remainder :
    TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
      trackBLinearPrimeExpGeometryGood
      trackBLinearPrimeExpGeometryGoodConcreteFail

/-- Convert the square-moment selected-remainder variant to the one-point
selected-remainder variant. -/
def trackBLinearPrimeExpScheduleGeometryGoodConcreteAnalyticFacts_of_secondMoment
    (h : TrackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentAnalyticFacts) :
    TrackBLinearPrimeExpScheduleGeometryGoodConcreteAnalyticFacts where
  probability := h.probability
  geometry := h.geometry
  tails := h.tails
  remainder :=
    trackBLinearPrimeExpScheduleWithGoodRemainderAnalyticFacts_of_secondMoment h.remainder

/-- Convert the natural real-budget selected-remainder variant to the
square-moment geometry-good concrete package. -/
def trackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentAnalyticFacts_of_realBudget
    (h : TrackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentRealBudgetAnalyticFacts) :
    TrackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentAnalyticFacts where
  probability := h.probability
  geometry := h.geometry
  tails := h.tails
  remainder :=
    trackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentFacts_of_realBudget h.remainder

/-- Convert the natural real-budget selected-remainder variant to the one-point
selected-remainder geometry-good concrete package. -/
def trackBLinearPrimeExpScheduleGeometryGoodConcreteAnalyticFacts_of_secondMomentRealBudget
    (h : TrackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentRealBudgetAnalyticFacts) :
    TrackBLinearPrimeExpScheduleGeometryGoodConcreteAnalyticFacts :=
  trackBLinearPrimeExpScheduleGeometryGoodConcreteAnalyticFacts_of_secondMoment
    (trackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentAnalyticFacts_of_realBudget h)

/-- Final theorem handoff for the geometry-good concrete package with
square-moment selected-remainder input. -/
theorem erdos1144_of_trackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentAnalyticFacts
    (h : TrackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentAnalyticFacts) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExpScheduleGeometryGoodConcreteAnalyticFacts
    (trackBLinearPrimeExpScheduleGeometryGoodConcreteAnalyticFacts_of_secondMoment h)

/-- Final theorem handoff for the geometry-good concrete package with natural
real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentRealBudgetAnalyticFacts
    (h : TrackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentRealBudgetAnalyticFacts) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentAnalyticFacts
    (trackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentAnalyticFacts_of_realBudget h)

/-- Direct final handoff from the geometry-good concrete inputs when the
selected-remainder estimate is supplied by square moments. -/
theorem erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_secondMoment
    (hprob : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodTailComparisonFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentAnalyticFacts
    { probability := hprob
      geometry := hgeometry
      tails := htails
      remainder := hremainder }

/-- Direct final handoff from the geometry-good concrete inputs with
Berry-Esseen-style real tail errors and square-moment selected-remainder
input. -/
theorem erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_tailError_secondMoment
    (hprob : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_secondMoment
    hprob hgeometry
    (trackBLinearPrimeExpScheduleWithGoodTailComparisonFacts_of_error htails)
    hremainder

/-- Direct final handoff from the geometry-good concrete inputs with raw
scheduled-core real tail errors and square-moment selected-remainder input. -/
theorem erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_rawTailError_secondMoment
    (hprob : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_tailError_secondMoment
    hprob hgeometry
    (trackBLinearPrimeExpScheduleWithGoodTailErrorFacts_of_rawError htails)
    hremainder

/-- Direct final handoff from the geometry-good concrete inputs when the
selected-remainder estimate is supplied by a natural real square-moment
budget. -/
theorem erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_secondMomentRealBudget
    (hprob : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodTailComparisonFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExpScheduleGeometryGoodConcreteSecondMomentRealBudgetAnalyticFacts
    { probability := hprob
      geometry := hgeometry
      tails := htails
      remainder := hremainder }

/-- Direct final handoff from the geometry-good concrete inputs with
Berry-Esseen-style real tail errors and natural real-budget square-moment
selected-remainder input. -/
theorem erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_tailError_secondMomentRealBudget
    (hprob : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_secondMomentRealBudget
    hprob hgeometry
    (trackBLinearPrimeExpScheduleWithGoodTailComparisonFacts_of_error htails)
    hremainder

/-- Direct final handoff from the geometry-good concrete inputs with raw
scheduled-core real tail errors and natural real-budget square-moment
selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_rawTailError_secondMomentRealBudget
    (hprob : TrackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_tailError_secondMomentRealBudget
    hprob hgeometry
    (trackBLinearPrimeExpScheduleWithGoodTailErrorFacts_of_rawError htails)
    hremainder

/-- Final handoff for the named concrete mean floor, centered-second
real-budget energy estimates, arbitrary real-valued flatness tails, raw
scheduled-core tail errors, and natural real-budget square-moment selected
remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_concreteMeanFloor_centered_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar :
      TrackBLinearPrimeExpGeometryCenteredMeanFloorRealBudgetEstimates
        trackBLinearPrimeExpConcreteMeanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_rawTailError_secondMomentRealBudget
    (trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_concreteMeanFloor_centered_realProb
      hmass hvar hflat)
    hgeometry htails hremainder

/-- Final handoff for the named concrete mean floor, raw-second real-budget
energy estimates, arbitrary real-valued flatness tails, raw scheduled-core
tail errors, and natural real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_concreteMeanFloor_raw_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar :
      TrackBLinearPrimeExpGeometryRawMeanFloorRealBudgetEstimates
        trackBLinearPrimeExpConcreteMeanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_rawTailError_secondMomentRealBudget
    (trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_concreteMeanFloor_raw_realProb
      hmass hvar hflat)
    hgeometry htails hremainder

/-- Final handoff from boundary-safe support-bulk mass facts, centered-second
real-budget energy estimates against the named concrete mean floor, arbitrary
real-valued flatness tails, raw scheduled-core tail errors, and natural
real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_supportBulk_centered_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpSupportBulkMassFacts)
    (hvar :
      TrackBLinearPrimeExpGeometryCenteredMeanFloorRealBudgetEstimates
        trackBLinearPrimeExpConcreteMeanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMeanFloor_centered_realProb_rawTailError_realRemainder
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_supportBulk hmass)
    hvar hflat hgeometry htails hremainder

/-- Final handoff from boundary-safe support-bulk mass facts, raw-second
real-budget energy estimates against the named concrete mean floor, arbitrary
real-valued flatness tails, raw scheduled-core tail errors, and natural
real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_supportBulk_raw_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpSupportBulkMassFacts)
    (hvar :
      TrackBLinearPrimeExpGeometryRawMeanFloorRealBudgetEstimates
        trackBLinearPrimeExpConcreteMeanFloor)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMeanFloor_raw_realProb_rawTailError_realRemainder
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_supportBulk hmass)
    hvar hflat hgeometry htails hremainder

/-- Final handoff from named concrete reciprocal-mass floors, a genuine
lower-tail concentration theorem for the layer variance, arbitrary real-valued
flatness tails, raw scheduled-core tail errors, and natural real-budget
square-moment selected-remainder input.  Unlike the centered/raw second-moment
handoffs, this does not force the analytic small-ball proof through Chebyshev. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_concreteMass_concentration_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_rawTailError_secondMomentRealBudget
    (trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_concentration_realProbability
      (trackBLinearPrimeExpLayerMeanLowerFacts_of_concreteFloors hmass) hvar hflat)
    hgeometry htails hremainder

/-- Final handoff from boundary-safe support-bulk mass facts, a genuine
lower-tail concentration theorem for the layer variance, arbitrary real-valued
flatness tails, raw scheduled-core tail errors, and natural real-budget
square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_supportBulk_concentration_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpSupportBulkMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_concentration_realProb_rawTailError_realRemainder
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_supportBulk hmass)
    hvar hflat hgeometry htails hremainder

/-- Final handoff from named concrete reciprocal-mass floors, four named
product/rough bad events for the layer variance lower tail, arbitrary
real-valued flatness tails, raw scheduled-core tail errors, and natural
real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_concreteMass_fourEvents_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_rawTailError_secondMomentRealBudget
    (trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_fourEvents_realProbability
      (trackBLinearPrimeExpLayerMeanLowerFacts_of_concreteFloors hmass) hvar hflat)
    hgeometry htails hremainder

/-- Final handoff from named concrete reciprocal-mass floors, common-floor
signal/error estimates for the product/rough layer variance lower tail,
arbitrary real-valued flatness tails, raw scheduled-core tail errors, and
natural real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_concreteMass_energyFloor_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationEnergyFloorFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_geometryGoodProbability_rawTailError_secondMomentRealBudget
    (trackBLinearPrimeExpGeometryGoodConcreteProbabilityFacts_of_energyFloor_realProbability
      (trackBLinearPrimeExpLayerMeanLowerFacts_of_concreteFloors hmass) hvar hflat)
    hgeometry htails hremainder

/-- Final handoff from named concrete reciprocal-mass floors, product/rough
factorized floor estimates for the layer variance lower tail, arbitrary
real-valued flatness tails, raw scheduled-core tail errors, and natural
real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_concreteMass_prodRough_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughFloorFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_energyFloor_realProb_rawTailError_realRemainder
    hmass
    (trackBLinearPrimeExpGeometryVarianceConcentrationEnergyFloorFacts_of_productRoughFloor
      hvar)
    hflat hgeometry htails hremainder

/-- Final handoff from named concrete reciprocal-mass floors, product/rough
signal-factor estimates for the layer variance lower tail, arbitrary
real-valued flatness tails, raw scheduled-core tail errors, and natural
real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_concreteMass_prodSignal_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSignalFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_prodRough_realProb_rawTailError_realRemainder
    hmass
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughFloorFacts_of_prodSignal
      hvar)
    hflat hgeometry htails hremainder

/-- Final handoff from named concrete reciprocal-mass floors, product/rough
threshold estimates for the layer variance lower tail, arbitrary real-valued
flatness tails, raw scheduled-core tail errors, and natural real-budget
square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_concreteMass_prodThreshold_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_prodSignal_realProb_rawTailError_realRemainder
    hmass
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSignalFacts_of_threshold
      hvar)
    hflat hgeometry htails hremainder

/-- Final handoff from named concrete reciprocal-mass floors, product/rough
threshold estimates with real probability bounds for the layer variance lower
tail, arbitrary real-valued flatness tails, raw scheduled-core tail errors, and
natural real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_concreteMass_prodThresholdReal_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdRealFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_prodThreshold_realProb_rawTailError_realRemainder
    hmass
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdFacts_of_real
      hvar)
    hflat hgeometry htails hremainder

/-- Final handoff from named concrete reciprocal-mass floors, product/rough
error-budget estimates with real probability bounds for the layer variance
lower tail, arbitrary real-valued flatness tails, raw scheduled-core tail
errors, and natural real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_concreteMass_prodErrorBudgetReal_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughErrorBudgetRealFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_prodThresholdReal_rawTailError_realRemainder
    hmass
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdRealFacts_of_errorBudget
      hvar)
    hflat hgeometry htails hremainder

/-- Final handoff from named concrete reciprocal-mass floors, product/rough
estimates whose scalar error budget is exactly the layer variance target `V j`,
arbitrary real-valued flatness tails, raw scheduled-core tail errors, and
natural real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_concreteMass_prodVErrorReal_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpConcreteFloorReciprocalMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_prodErrorBudgetReal_rawTailError_realRemainder
    hmass
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughErrorBudgetRealFacts_of_vError
      hvar)
    hflat hgeometry htails hremainder

/-- Final handoff from boundary-safe support-bulk mass facts, four named
product/rough bad events for the layer variance lower tail, arbitrary
real-valued flatness tails, raw scheduled-core tail errors, and natural
real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_supportBulk_fourEvents_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpSupportBulkMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationFourEventFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_fourEvents_realProb_rawTailError_realRemainder
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_supportBulk hmass)
    hvar hflat hgeometry htails hremainder

/-- Final handoff from boundary-safe support-bulk mass facts, common-floor
signal/error estimates for the product/rough layer variance lower tail,
arbitrary real-valued flatness tails, raw scheduled-core tail errors, and
natural real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_supportBulk_energyFloor_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpSupportBulkMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationEnergyFloorFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_energyFloor_realProb_rawTailError_realRemainder
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_supportBulk hmass)
    hvar hflat hgeometry htails hremainder

/-- Final handoff from boundary-safe support-bulk mass facts, product/rough
factorized floor estimates for the layer variance lower tail, arbitrary
real-valued flatness tails, raw scheduled-core tail errors, and natural
real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_supportBulk_prodRough_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpSupportBulkMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughFloorFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_prodRough_realProb_rawTailError_realRemainder
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_supportBulk hmass)
    hvar hflat hgeometry htails hremainder

/-- Final handoff from boundary-safe support-bulk mass facts, product/rough
signal-factor estimates for the layer variance lower tail, arbitrary
real-valued flatness tails, raw scheduled-core tail errors, and natural
real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_supportBulk_prodSignal_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpSupportBulkMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSignalFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_prodSignal_realProb_rawTailError_realRemainder
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_supportBulk hmass)
    hvar hflat hgeometry htails hremainder

/-- Final handoff from boundary-safe support-bulk mass facts, product/rough
threshold estimates for the layer variance lower tail, arbitrary real-valued
flatness tails, raw scheduled-core tail errors, and natural real-budget
square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_supportBulk_prodThreshold_realProb_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpSupportBulkMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_prodThreshold_realProb_rawTailError_realRemainder
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_supportBulk hmass)
    hvar hflat hgeometry htails hremainder

/-- Final handoff from boundary-safe support-bulk mass facts, product/rough
threshold estimates with real probability bounds for the layer variance lower
tail, arbitrary real-valued flatness tails, raw scheduled-core tail errors, and
natural real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_supportBulk_prodThresholdReal_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpSupportBulkMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughThresholdRealFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_prodThresholdReal_rawTailError_realRemainder
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_supportBulk hmass)
    hvar hflat hgeometry htails hremainder

/-- Final handoff from boundary-safe support-bulk mass facts, product/rough
error-budget estimates with real probability bounds for the layer variance
lower tail, arbitrary real-valued flatness tails, raw scheduled-core tail
errors, and natural real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_supportBulk_prodErrorBudgetReal_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpSupportBulkMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughErrorBudgetRealFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_prodErrorBudgetReal_rawTailError_realRemainder
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_supportBulk hmass)
    hvar hflat hgeometry htails hremainder

/-- Final handoff from boundary-safe support-bulk mass facts, product/rough
estimates whose scalar error budget is exactly the layer variance target `V j`,
arbitrary real-valued flatness tails, raw scheduled-core tail errors, and
natural real-budget square-moment selected-remainder input. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_supportBulk_prodVErrorReal_rawTailError_realRemainder
    (hmass : TrackBLinearPrimeExpSupportBulkMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_concreteMass_prodVErrorReal_rawTailError_realRemainder
    (trackBLinearPrimeExpConcreteFloorReciprocalMassFacts_of_supportBulk hmass)
    hvar hflat hgeometry htails hremainder

/-- Final handoff for the active product/rough `V_j` error route when the
boundary-safe support-bulk mass input is proved as independent support-side and
fresh-prime reciprocal-mass estimates. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_splitMass_prodVErrorReal_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hprime : TrackBLinearPrimeExpFreshPrimeMassFacts)
    (hvar : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_supportBulk_prodVErrorReal_rawTailError_realRemainder
    (trackBLinearPrimeExpSupportBulkMassFacts_of_support_and_prime hsupport hprime)
    hvar hflat hgeometry htails hremainder

/-- Final handoff for the active product/rough route when both the mass input
and the product/rough variance input are split into independently provable
paper-side estimates. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_splitMass_prodVErrorPieces_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hprime : TrackBLinearPrimeExpFreshPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_splitMass_prodVErrorReal_rawTailError_realRemainder
    hsupport hprime
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts_of_pieces
      core hsmall hrough herror hmass)
    hflat hgeometry htails hremainder

/-- Final handoff for the active product/rough route when the fresh-prime mass
is proved on the full fresh layer and the product/rough variance input is split
into independently provable paper-side estimates. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_freshLayer_prodVErrorPieces_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_splitMass_prodVErrorPieces_rawTailError_realRemainder
    hsupport
    (trackBLinearPrimeExpFreshPrimeMassFacts_of_freshLayer hlayer)
    core hsmall hrough herror hmass hflat hgeometry htails hremainder

/-- Final handoff for the active product/rough route when the mass and
product/rough variance inputs are split, and coefficient flatness is proved
through enlarged one-coefficient bad events. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_splitMass_prodVErrorPiecesFlat_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hprime : TrackBLinearPrimeExpFreshPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_splitMass_prodVErrorPieces_rawTailError_realRemainder
    hsupport hprime core hsmall hrough herror hmass
    (trackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts_of_event hflat)
    hgeometry htails hremainder

/-- Final handoff for the active product/rough route when fresh-prime mass is
proved on the full layer, product/rough variance inputs are split, and
coefficient flatness is proved through enlarged one-coefficient bad events. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_freshLayer_prodVErrorPiecesFlat_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_freshLayer_prodVErrorPieces_rawTailError_realRemainder
    hsupport hlayer core hsmall hrough herror hmass
    (trackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts_of_event hflat)
    hgeometry htails hremainder

/-- Active product/rough final handoff with the first-pass product/rough floor
normalization fixed in Lean.  The analytic proof supplies only the coefficient
decomposition, the four product/rough tail estimates, flatness events, direct
geometry, raw tail errors, and selected-remainder real-budget estimate. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_freshLayer_fixedFloorPiecesFlat_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (fixedCore : TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_freshLayer_prodVErrorPiecesFlat_rawTailError_realRemainder
    hsupport hlayer
    (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore)
    hsmall hrough herror hmass hflat hgeometry htails hremainder

/-- Canonical fixed-floor handoff with no random mass bad event.  Use this when
the small/rough/error estimates are proved for the exact threshold events. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_fixedFloorPiecesEmptyMass_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (fixedCore : TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts)
    (hbad : ∀ j r, fixedCore.badMass j r = ∅)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_freshLayer_fixedFloorPiecesFlat_rawTailError_realRemainder
    hsupport hlayer fixedCore hsmall hrough herror
    (trackBLinearPrimeExpFixedFloorMassTailRealFacts_of_empty fixedCore hbad)
    hflat hgeometry htails hremainder

/-- Canonical no-mass fixed-floor handoff.  Use this when Packet B introduces
no random mass bad event and Packet C proves exact threshold-event estimates. -/
theorem erdos1144_of_trackBLinearPrimeExp_noMassFixedFloorPieces_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core))
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core))
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailRealFacts
        (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core))
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_fixedFloorPiecesEmptyMass_rawTailError_realRemainder
    hsupport hlayer (trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass core)
    (by intro j r; rfl)
    hsmall hrough herror hflat hgeometry htails hremainder

/-- Final handoff for the active product/rough route when the mass input is
split and the four product/rough tail estimates are proved through convenient
bad events containing the canonical threshold failures. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_splitMass_prodVErrorEventPieces_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hprime : TrackBLinearPrimeExpFreshPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_splitMass_prodVErrorReal_rawTailError_realRemainder
    hsupport hprime
    (trackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealFacts_of_eventPieces
      core hsmall hrough herror hmass)
    hflat hgeometry htails hremainder

/-- Final handoff for the active product/rough route when the fresh-prime mass
is proved on the full fresh layer and the product/rough tail estimates are
proved through convenient bad events containing the canonical threshold
failures. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_freshLayer_prodVErrorEventPieces_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_splitMass_prodVErrorEventPieces_rawTailError_realRemainder
    hsupport
    (trackBLinearPrimeExpFreshPrimeMassFacts_of_freshLayer hlayer)
    core hsmall hrough herror hmass hflat hgeometry htails hremainder

/-- Final handoff for the active product/rough route when both the
product/rough tails and coefficient-flatness tails are proved through
convenient enlarged bad events. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_splitMass_prodVErrorAllEvents_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hprime : TrackBLinearPrimeExpFreshPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_splitMass_prodVErrorEventPieces_rawTailError_realRemainder
    hsupport hprime core hsmall hrough herror hmass
    (trackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts_of_event hflat)
    hgeometry htails hremainder

/-- Final handoff for the active product/rough route when fresh-prime mass is
proved on the full layer and both product/rough and coefficient-flatness tails
are proved through convenient enlarged bad events. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_freshLayer_prodVErrorAllEvents_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorRealCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        core)
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        core)
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        core)
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts core)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_freshLayer_prodVErrorEventPieces_rawTailError_realRemainder
    hsupport hlayer core hsmall hrough herror hmass
    (trackBLinearPrimeExpFlatGoodLayerRealProbabilityFacts_of_event hflat)
    hgeometry htails hremainder

/-- Most flexible active product/rough handoff with first-pass product/rough
floors fixed in Lean.  Use this when the four product/rough tail estimates and
coefficient-flatness estimate are all proved through convenient enlarged bad
events. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_freshLayer_fixedFloorAllEvents_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (fixedCore : TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hmass :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughMassTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_freshLayer_prodVErrorAllEvents_rawTailError_realRemainder
    hsupport hlayer
    (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore)
    hsmall hrough herror hmass hflat hgeometry htails hremainder

/-- Active fixed-floor handoff with no random mass bad event.  Packet A still
supplies deterministic mass facts; this wrapper only removes the empty
probability field from Packet C. -/
theorem
    erdos1144_of_trackBLinearPrimeExp_freshLayer_fixedFloorEmptyMass_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (fixedCore : TrackBLinearPrimeExpProductRoughFixedFloorCoreFacts)
    (hbad : ∀ j r, fixedCore.badMass j r = ∅)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor fixedCore))
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_freshLayer_fixedFloorAllEvents_rawTailError_realRemainder
    hsupport hlayer fixedCore hsmall hrough herror
    (trackBLinearPrimeExpFixedFloorMassTailEventRealFacts_of_empty fixedCore hbad)
    hflat hgeometry htails hremainder

/-- Event-witness no-mass fixed-floor handoff.  Use this when Packet C proves
the product/rough estimates through enlarged bad events. -/
theorem erdos1144_of_trackBLinearPrimeExp_noMassFixedFloorEvents_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (hsmall :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughSmallTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core))
    (hrough :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughRoughTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core))
    (herror :
      TrackBLinearPrimeExpGeometryVarianceConcentrationProductRoughVErrorTailEventRealFacts
        (trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core))
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_freshLayer_fixedFloorEmptyMass_rawTailError_realRemainder
    hsupport hlayer (trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass core)
    (by intro j r; rfl)
    hsmall hrough herror hflat hgeometry htails hremainder

/-- No-mass fixed-floor handoff with pointwise small/rough/error threshold
exclusions. -/
theorem erdos1144_of_trackBLinearPrimeExp_noMassPointwise_rawTailError_realRemainder
    (hsupport : TrackBLinearPrimeExpSupportBulkSupportMassFacts)
    (hlayer : TrackBLinearPrimeExpFreshLayerPrimeMassFacts)
    (core : TrackBLinearPrimeExpProductRoughFixedFloorNoMassCoreFacts)
    (hsmall : ∀ omega j,
      trackBLinearPrimeExpProductRoughSmallFloor j ≤ core.smallFactor omega j ^ 2)
    (hrough : ∀ omega j r,
      r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      trackBLinearPrimeExpProductRoughRoughFloor j r ≤
        ∑ p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeExpScheduleSpec.freshLo j r)
          (trackBLinearPrimeExpScheduleSpec.freshHi j r),
          core.roughCoeff omega j r p ^ 2)
    (herror : ∀ omega j r,
      r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeExpScheduleSpec.Q j →
      (∑ p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeExpScheduleSpec.freshLo j r)
        (trackBLinearPrimeExpScheduleSpec.freshHi j r),
        core.errorCoeff omega j r p ^ 2) ≤ trackBLinearPrimeExpScheduleSpec.V j)
    (hflat : TrackBLinearPrimeExpFlatGoodLayerRealProbabilityEventFacts)
    (hgeometry :
      TrackBLinearPrimeScheduleDirectGeometryFacts
        (trackBLinearPrimeExpScheduleSpecWithGood
          trackBLinearPrimeExpGeometryGood
          trackBLinearPrimeExpGeometryGoodConcreteFail))
    (htails :
      TrackBLinearPrimeExpScheduleWithGoodRawTailErrorFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail)
    (hremainder :
      TrackBLinearPrimeExpScheduleWithGoodRemainderSecondMomentRealBudgetFacts
        trackBLinearPrimeExpGeometryGood
        trackBLinearPrimeExpGeometryGoodConcreteFail) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeExp_noMassFixedFloorPieces_rawTailError_realRemainder
    hsupport hlayer core
    (trackBLinearPrimeExpSmallTailRealFacts_of_pointwise
      (core := trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core)
      (by
        intro omega j
        simpa [trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass,
          trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor,
          trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass] using hsmall omega j))
    (trackBLinearPrimeExpRoughTailRealFacts_of_pointwise
      (core := trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core)
      (by
        intro omega j r hr
        simpa [trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass,
          trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor,
          trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass] using hrough omega j r hr))
    (trackBLinearPrimeExpVErrorTailRealFacts_of_pointwise
      (core := trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass core)
      (by
        intro omega j r hr
        simpa [trackBLinearPrimeExpProductRoughVErrorCoreFacts_of_noMass,
          trackBLinearPrimeExpProductRoughVErrorRealCoreFacts_of_fixedFloor,
          trackBLinearPrimeExpFixedFloorCoreFacts_of_noMass] using herror omega j r hr))
    hflat hgeometry htails hremainder

end Problem1144
end Erdos
