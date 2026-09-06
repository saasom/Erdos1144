import Erdos.Problem1144.HarperFreshCoefficientScreen
import Erdos.Problem1144.HarperScreenOrbitMoments
import Erdos.Problem1144.HarperTrackBLinearPrime

open MeasureTheory
open scoped BigOperators

namespace Erdos
namespace Problem1144

/-!
# The middle-prime screen for the active squarefree fresh walk

For an endpoint `N < X * Y`, every coefficient attached to a fresh prime
`p > X` is supported on integers below `Y`.  Consequently a finite flip in
the middle range `(Y, X]` changes neither the coefficient vector nor its
variance/covariance geometry.  It also leaves the whole fresh linear walk
unchanged, since the fresh signs themselves lie above `X`.

This is the exact post-selection screen statement used by Track B: a cloud
may be selected and decorrelated from the small-prime coefficient geometry
before any middle-prime sign is exposed.
-/

/-- A concrete squarefree fresh coefficient at `p > X` only sees prime
coordinates at most `Y` when `N < X * Y`. -/
theorem trackBSquarefreeFreshCoeff_freshSignFlip_eq_of_screen
    (s fresh : Finset ℕ) (omega : Omega) {X Y N p : ℕ}
    (hN : N < X * Y) (hp : p ∈ largePrimeInterval X N)
    (hsLo : ∀ q ∈ s, Y < q) :
    trackBSquarefreeFreshCoeff fresh (freshSignFlip s omega) N p =
      trackBSquarefreeFreshCoeff fresh omega N p := by
  classical
  have hquot : N / p < Y :=
    quotient_cutoff_lt_of_lt_mul_of_largePrimeInterval hN hp
  unfold trackBSquarefreeFreshCoeff
  apply Finset.sum_congr rfl
  intro m hm
  have hmY : m < Y :=
    (mem_trackBSquarefreeFreshCoeffSupport.mp hm).2.1.trans_lt hquot
  have hsmooth : IsXSmooth Y m := isXSmooth_of_lt hmY
  rw [f_freshSignFlip_eq_of_disjoint_sfKernel s omega m
    (disjoint_sfKernel_of_isXSmooth_of_above hsmooth s hsLo)]

/-- Stage/test-point form of the coefficient localization theorem. -/
theorem trackBSquarefreeFreshLinearCoeff_freshSignFlip_eq_of_screen
    (s : Finset ℕ) (freshSet : ℕ → ℕ → Finset ℕ)
    (omega : Omega) {j X Y N p : ℕ}
    (hN : N < X * Y) (hp : p ∈ largePrimeInterval X N)
    (hsLo : ∀ q ∈ s, Y < q) :
    trackBSquarefreeFreshLinearCoeff freshSet
        (freshSignFlip s omega) j N p =
      trackBSquarefreeFreshLinearCoeff freshSet omega j N p := by
  exact trackBSquarefreeFreshCoeff_freshSignFlip_eq_of_screen
    s (freshSet j N) omega hN hp hsLo

/-- By construction, a squarefree fresh coefficient contains no coordinate
from its own declared fresh support.  It is therefore invariant when all of
those fresh signs are flipped. -/
theorem trackBSquarefreeFreshCoeff_freshSignFlip_fresh_eq
    (fresh : Finset ℕ) (omega : Omega) (N p : ℕ) :
    trackBSquarefreeFreshCoeff fresh (freshSignFlip fresh omega) N p =
      trackBSquarefreeFreshCoeff fresh omega N p := by
  classical
  unfold trackBSquarefreeFreshCoeff
  apply Finset.sum_congr rfl
  intro m hm
  have hno : trackBNoFreshFactor fresh m :=
    trackBSquarefreeFreshCoeffSupport_noFresh hm
  rw [f_freshSignFlip_eq_of_disjoint_sfKernel fresh omega m hno.symm]

/-- A squarefree fresh coefficient is unchanged after flipping any subset of
its declared fresh coordinates. -/
theorem trackBSquarefreeFreshCoeff_freshSignFlip_subset_eq
    (fresh t : Finset ℕ) (omega : Omega) (N p : ℕ) (ht : t ⊆ fresh) :
    trackBSquarefreeFreshCoeff fresh (freshSignFlip t omega) N p =
      trackBSquarefreeFreshCoeff fresh omega N p := by
  classical
  unfold trackBSquarefreeFreshCoeff
  apply Finset.sum_congr rfl
  intro m hm
  have hno : trackBNoFreshFactor fresh m :=
    trackBSquarefreeFreshCoeffSupport_noFresh hm
  have hdisj : Disjoint t (sfKernel m) := by
    rw [Finset.disjoint_left]
    intro q hqt hqKernel
    exact Finset.disjoint_left.mp hno.symm (ht hqt) hqKernel
  rw [f_freshSignFlip_eq_of_disjoint_sfKernel t omega m hdisj]

/-- The active squarefree fresh walk is exactly odd under the simultaneous
flip of its own fresh coordinates, despite its coefficients being random in
the complementary prime world. -/
theorem trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_freshSignFlip_eq_neg
    (freshSet : ℕ → ℕ → Finset ℕ) (omega : Omega) (j N : ℕ) :
    trackBLinearPrimeCoreRaw freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet)
        (freshSignFlip (freshSet j N) omega) j N =
      -trackBLinearPrimeCoreRaw freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) omega j N := by
  classical
  unfold trackBLinearPrimeCoreRaw trackBSquarefreeFreshLinearCoeff
  calc
    (∑ p ∈ freshSet j N,
        eps (freshSignFlip (freshSet j N) omega) p *
          trackBSquarefreeFreshCoeff (freshSet j N)
            (freshSignFlip (freshSet j N) omega) N p) =
        ∑ p ∈ freshSet j N,
          -(eps omega p *
            trackBSquarefreeFreshCoeff (freshSet j N) omega N p) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [eps_freshSignFlip_of_mem _ omega hp,
        trackBSquarefreeFreshCoeff_freshSignFlip_fresh_eq]
      ring
    _ = -(∑ p ∈ freshSet j N,
        eps omega p *
          trackBSquarefreeFreshCoeff (freshSet j N) omega N p) := by
      rw [Finset.sum_neg_distrib]

/-- On every finite fresh-sign orbit, the active raw core is the ordinary
Rademacher linear form with the complementary-world coefficients frozen at
the orbit base point. -/
theorem trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_freshSignFlip_subset_eq_orbitLinear
    (freshSet : ℕ → ℕ → Finset ℕ) (omega : Omega) (j N : ℕ)
    (t : Finset ℕ) (ht : t ⊆ freshSet j N) :
    trackBLinearPrimeCoreRaw freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet)
        (freshSignFlip t omega) j N =
      orbitLinear (freshSet j N)
        (fun p => trackBSquarefreeFreshCoeff (freshSet j N) omega N p)
        omega t := by
  classical
  unfold trackBLinearPrimeCoreRaw trackBSquarefreeFreshLinearCoeff
    orbitLinear epsLinearForm
  apply Finset.sum_congr rfl
  intro p _hp
  rw [trackBSquarefreeFreshCoeff_freshSignFlip_subset_eq
    (freshSet j N) t omega N p ht]
  ring

/-- The successful worlds in the exact finite orbit of the concrete
squarefree fresh-prime core. -/
noncomputable def trackBSquarefreeFreshCoreOrbitLargeSet
    (fresh : Finset ℕ) (omega : Omega) (N : ℕ) (U : ℝ) :
    Finset (Finset ℕ) := by
  classical
  exact fresh.powerset.filter fun t =>
    U ≤
      |trackBLinearPrimeCoreRaw
        (fun _j _N => fresh)
        (trackBSquarefreeFreshLinearCoeff (fun _j _N => fresh))
        (freshSignFlip t omega) 0 N|

/-- Fiberwise finite-screen Paley--Zygmund theorem for the actual Track B
core.  Once its conditional variance exceeds `2*U^2`, at least one twelfth of
all fresh-sign assignments make the raw core have magnitude at least `U`.

This conclusion is pointwise in the frozen complementary world, so it remains
valid after selecting and pruning a cloud using only coefficient geometry. -/
theorem card_trackBSquarefreeFreshCoreOrbitLargeSet_lower
    (fresh : Finset ℕ) (omega : Omega) (N : ℕ) (U : ℝ)
    (hV : 0 < trackBLinearPrimeVariance
      (fun _j _N => fresh)
      (trackBSquarefreeFreshLinearCoeff (fun _j _N => fresh)) omega 0 N)
    (hU : U ^ 2 ≤
      trackBLinearPrimeVariance
        (fun _j _N => fresh)
        (trackBSquarefreeFreshLinearCoeff (fun _j _N => fresh)) omega 0 N / 2) :
    ((2 ^ fresh.card : ℕ) : ℝ) / 12 ≤
      ((trackBSquarefreeFreshCoreOrbitLargeSet fresh omega N U).card : ℝ) := by
  let a : ℕ → ℝ := fun p => trackBSquarefreeFreshCoeff fresh omega N p
  have horbit :
      trackBSquarefreeFreshCoreOrbitLargeSet fresh omega N U =
        orbitLargeSet fresh a omega U := by
    classical
    ext t
    simp only [trackBSquarefreeFreshCoreOrbitLargeSet, orbitLargeSet,
      Finset.mem_filter]
    apply and_congr_right
    intro ht
    rw [trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_freshSignFlip_subset_eq_orbitLinear
      (fun _j _N => fresh) omega 0 N t (Finset.mem_powerset.mp ht)]
  rw [horbit]
  apply card_orbitLargeSet_lower fresh a omega U
  · simpa [trackBLinearPrimeVariance, trackBSquarefreeFreshLinearCoeff, a]
      using hV
  · simpa [trackBLinearPrimeVariance, trackBSquarefreeFreshLinearCoeff, a]
      using hU

/-- The conditional variance of the concrete raw core is constant on every
subset-flip orbit of its own fresh coordinates. -/
theorem trackBLinearPrimeVariance_sqfreeFreshCoeff_freshSignFlip_subset_eq
    (freshSet : ℕ → ℕ → Finset ℕ) (omega : Omega) (j N : ℕ)
    (t : Finset ℕ) (ht : t ⊆ freshSet j N) :
    trackBLinearPrimeVariance freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet)
        (freshSignFlip t omega) j N =
      trackBLinearPrimeVariance freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) omega j N := by
  classical
  unfold trackBLinearPrimeVariance trackBSquarefreeFreshLinearCoeff
  apply Finset.sum_congr rfl
  intro p _hp
  rw [trackBSquarefreeFreshCoeff_freshSignFlip_subset_eq
    (freshSet j N) t omega N p ht]

/-- Large-value event for one concrete squarefree fresh-prime core. -/
def trackBSquarefreeFreshCoreLargeEvent
    (fresh : Finset ℕ) (N : ℕ) (U : ℝ) : Set Omega :=
  {omega |
    U ≤
      |trackBLinearPrimeCoreRaw
        (fun _j _N => fresh)
        (trackBSquarefreeFreshLinearCoeff (fun _j _N => fresh)) omega 0 N|}

/-- The orbit-invariant event on which the concrete conditional variance is
positive and at least `2*U^2`. -/
def trackBSquarefreeFreshVarianceThresholdEvent
    (fresh : Finset ℕ) (N : ℕ) (U : ℝ) : Set Omega :=
  {omega |
    0 <
        trackBLinearPrimeVariance
          (fun _j _N => fresh)
          (trackBSquarefreeFreshLinearCoeff (fun _j _N => fresh)) omega 0 N ∧
      U ^ 2 ≤
        trackBLinearPrimeVariance
          (fun _j _N => fresh)
          (trackBSquarefreeFreshLinearCoeff (fun _j _N => fresh)) omega 0 N / 2}

theorem measurableSet_trackBSquarefreeFreshCoreLargeEvent
    (fresh : Finset ℕ) (N : ℕ) (U : ℝ) :
    MeasurableSet (trackBSquarefreeFreshCoreLargeEvent fresh N U) := by
  exact measurableSet_le measurable_const
    (continuous_abs.measurable.comp
      (measurable_trackBLinearPrimeCoreRaw_sqfreeFreshCoeff
        (fun _j _N => fresh) 0 N))

theorem measurableSet_trackBSquarefreeFreshVarianceThresholdEvent
    (fresh : Finset ℕ) (N : ℕ) (U : ℝ) :
    MeasurableSet (trackBSquarefreeFreshVarianceThresholdEvent fresh N U) := by
  let freshSet : ℕ → ℕ → Finset ℕ := fun _j _N => fresh
  let V : Omega → ℝ := fun omega =>
    trackBLinearPrimeVariance freshSet
      (trackBSquarefreeFreshLinearCoeff freshSet) omega 0 N
  have hV : Measurable V :=
    measurable_trackBLinearPrimeVariance freshSet
      (trackBSquarefreeFreshLinearCoeff freshSet)
      (measurable_trackBSquarefreeFreshLinearCoeff freshSet) 0 N
  exact (measurableSet_lt measurable_const hV).inter
    (measurableSet_le measurable_const (hV.div_const 2))

theorem trackBSquarefreeFreshVarianceThresholdEvent_freshSignFlip_subset_iff
    (fresh t : Finset ℕ) (omega : Omega) (N : ℕ) (U : ℝ)
    (ht : t ⊆ fresh) :
    freshSignFlip t omega ∈
        trackBSquarefreeFreshVarianceThresholdEvent fresh N U ↔
      omega ∈ trackBSquarefreeFreshVarianceThresholdEvent fresh N U := by
  unfold trackBSquarefreeFreshVarianceThresholdEvent
  simp only [Set.mem_setOf_eq]
  rw [trackBLinearPrimeVariance_sqfreeFreshCoeff_freshSignFlip_subset_eq
    (fun _j _N => fresh) omega 0 N t ht]

/-- Exact conditional-screen lower bound in the ambient probability space.
On the variance-threshold event, at least one twelfth of every fresh-sign
orbit makes the actual raw core large; finite-flip measure preservation turns
that pointwise fact into a probability bound. -/
theorem measureReal_trackBSquarefreeFreshCoreLarge_inter_varianceThreshold_lower
    (fresh : Finset ℕ) (N : ℕ) (U : ℝ) :
    (1 : ℝ) / 12 *
        mu.real (trackBSquarefreeFreshVarianceThresholdEvent fresh N U) ≤
      mu.real
        (trackBSquarefreeFreshVarianceThresholdEvent fresh N U ∩
          trackBSquarefreeFreshCoreLargeEvent fresh N U) := by
  let G := trackBSquarefreeFreshVarianceThresholdEvent fresh N U
  let E := trackBSquarefreeFreshCoreLargeEvent fresh N U
  apply measureReal_inter_lower_of_orbitEventCount fresh
    (measurableSet_trackBSquarefreeFreshVarianceThresholdEvent fresh N U)
    (measurableSet_trackBSquarefreeFreshCoreLargeEvent fresh N U)
  · intro t ht omega
    exact
      (trackBSquarefreeFreshVarianceThresholdEvent_freshSignFlip_subset_iff
        fresh t omega N U (Finset.mem_powerset.mp ht)).symm
  · intro omega homega
    have hcard := card_trackBSquarefreeFreshCoreOrbitLargeSet_lower
      fresh omega N U homega.1 homega.2
    have hcount :
        orbitEventCount fresh E omega =
          ((trackBSquarefreeFreshCoreOrbitLargeSet fresh omega N U).card : ℝ) := by
      classical
      unfold orbitEventCount trackBSquarefreeFreshCoreOrbitLargeSet E
        trackBSquarefreeFreshCoreLargeEvent
      rfl
    rw [hcount]
    simpa [div_eq_mul_inv, mul_comm] using hcard

/-- Convenient marginal form: any lower bound for the variance-threshold
event transfers to the large raw-core event with the sharp finite-orbit loss
`1/12`. -/
theorem measureReal_trackBSquarefreeFreshCoreLarge_lower_of_varianceThreshold
    (fresh : Finset ℕ) (N : ℕ) (U delta : ℝ)
    (hdelta : delta ≤
      mu.real (trackBSquarefreeFreshVarianceThresholdEvent fresh N U)) :
    delta / 12 ≤
      mu.real (trackBSquarefreeFreshCoreLargeEvent fresh N U) := by
  have hinter :=
    measureReal_trackBSquarefreeFreshCoreLarge_inter_varianceThreshold_lower
      fresh N U
  have hmono :
      mu.real
          (trackBSquarefreeFreshVarianceThresholdEvent fresh N U ∩
            trackBSquarefreeFreshCoreLargeEvent fresh N U) ≤
        mu.real (trackBSquarefreeFreshCoreLargeEvent fresh N U) :=
    measureReal_mono Set.inter_subset_right
  calc
    delta / 12 ≤ (1 : ℝ) / 12 *
        mu.real (trackBSquarefreeFreshVarianceThresholdEvent fresh N U) := by
          nlinarith
    _ ≤ mu.real
        (trackBSquarefreeFreshVarianceThresholdEvent fresh N U ∩
          trackBSquarefreeFreshCoreLargeEvent fresh N U) := hinter
    _ ≤ mu.real (trackBSquarefreeFreshCoreLargeEvent fresh N U) := hmono

/-- The conditional variance geometry of the active squarefree fresh walk is
pointwise invariant under the middle-prime screen. -/
theorem trackBLinearPrimeVariance_sqfreeFreshCoeff_freshSignFlip_eq_of_screen
    (s : Finset ℕ) (freshSet : ℕ → ℕ → Finset ℕ)
    (omega : Omega) {j X Y N : ℕ}
    (hN : N < X * Y)
    (hfresh : ∀ p ∈ freshSet j N, p ∈ largePrimeInterval X N)
    (hsLo : ∀ q ∈ s, Y < q) :
    trackBLinearPrimeVariance freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet)
        (freshSignFlip s omega) j N =
      trackBLinearPrimeVariance freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) omega j N := by
  classical
  unfold trackBLinearPrimeVariance
  apply Finset.sum_congr rfl
  intro p hp
  rw [trackBSquarefreeFreshLinearCoeff_freshSignFlip_eq_of_screen
    s freshSet omega hN (hfresh p hp) hsLo]

/-- The two-endpoint covariance geometry is likewise screen-invariant. -/
theorem trackBLinearPrimeCovariance_sqfreeFreshCoeff_freshSignFlip_eq_of_screen
    (s : Finset ℕ) (freshSet : ℕ → ℕ → Finset ℕ)
    (omega : Omega) {j X Y M N : ℕ}
    (hM : M < X * Y) (hN : N < X * Y)
    (hfreshM : ∀ p ∈ freshSet j M, p ∈ largePrimeInterval X M)
    (hfreshN : ∀ p ∈ freshSet j N, p ∈ largePrimeInterval X N)
    (hsLo : ∀ q ∈ s, Y < q) :
    trackBLinearPrimeCovariance freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet)
        (freshSignFlip s omega) j M N =
      trackBLinearPrimeCovariance freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) omega j M N := by
  classical
  unfold trackBLinearPrimeCovariance trackBLinearPrimeCoeffOn
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpM : p ∈ freshSet j M
  · by_cases hpN : p ∈ freshSet j N
    · simp only [hpM, hpN, if_true]
      rw [trackBSquarefreeFreshLinearCoeff_freshSignFlip_eq_of_screen
          s freshSet omega hM (hfreshM p hpM) hsLo,
        trackBSquarefreeFreshLinearCoeff_freshSignFlip_eq_of_screen
          s freshSet omega hN (hfreshN p hpN) hsLo]
    · simp [hpM, hpN]
  · simp [hpM]

/-- The active squarefree fresh linear walk itself is unchanged by a screen
supported in `(Y, X]`: its coefficients live below `Y`, while its Rademacher
coordinates live above `X`. -/
theorem trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_freshSignFlip_eq_of_screen
    (s : Finset ℕ) (freshSet : ℕ → ℕ → Finset ℕ)
    (omega : Omega) {j X Y N : ℕ}
    (hN : N < X * Y)
    (hfresh : ∀ p ∈ freshSet j N, p ∈ largePrimeInterval X N)
    (hsLo : ∀ q ∈ s, Y < q) (hsHi : ∀ q ∈ s, q ≤ X) :
    trackBLinearPrimeCoreRaw freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet)
        (freshSignFlip s omega) j N =
      trackBLinearPrimeCoreRaw freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) omega j N := by
  classical
  unfold trackBLinearPrimeCoreRaw
  apply Finset.sum_congr rfl
  intro p hp
  have hXp : X < p :=
    (mem_largePrimeInterval.mp (hfresh p hp)).2.1
  have hpNot : p ∉ s := by
    intro hps
    exact (not_lt_of_ge (hsHi p hps)) hXp
  rw [eps_freshSignFlip_of_notMem s omega hpNot,
    trackBSquarefreeFreshLinearCoeff_freshSignFlip_eq_of_screen
      s freshSet omega hN (hfresh p hp) hsLo]

/-- The finite variance/covariance data used to select and decorrelate a
candidate cloud. -/
@[ext] structure TrackBLinearPrimeCloudGeometry (cloud : Finset ℕ) where
  variance : {N // N ∈ cloud} → ℝ
  covariance : {N // N ∈ cloud} → {N // N ∈ cloud} → ℝ

/-- The active squarefree coefficient geometry restricted to one finite
candidate cloud. -/
noncomputable def trackBSquarefreeFreshCloudGeometry
    (freshSet : ℕ → ℕ → Finset ℕ) (omega : Omega)
    (j : ℕ) (cloud : Finset ℕ) : TrackBLinearPrimeCloudGeometry cloud where
  variance := fun N ↦
    trackBLinearPrimeVariance freshSet
      (trackBSquarefreeFreshLinearCoeff freshSet) omega j N.1
  covariance := fun M N ↦
    trackBLinearPrimeCovariance freshSet
      (trackBSquarefreeFreshLinearCoeff freshSet) omega j M.1 N.1

/-- The entire finite cloud geometry is fixed before the middle screen is
exposed.  This is the pointwise no-selection-bias theorem. -/
theorem trackBSquarefreeFreshCloudGeometry_freshSignFlip_eq_of_screen
    (s : Finset ℕ) (freshSet : ℕ → ℕ → Finset ℕ)
    (omega : Omega) (j : ℕ) (cloud : Finset ℕ) {X Y : ℕ}
    (hendpoint : ∀ N ∈ cloud, N < X * Y)
    (hfresh : ∀ N ∈ cloud, ∀ p ∈ freshSet j N,
      p ∈ largePrimeInterval X N)
    (hsLo : ∀ q ∈ s, Y < q) :
    trackBSquarefreeFreshCloudGeometry freshSet (freshSignFlip s omega) j cloud =
      trackBSquarefreeFreshCloudGeometry freshSet omega j cloud := by
  ext M N
  · exact
      trackBLinearPrimeVariance_sqfreeFreshCoeff_freshSignFlip_eq_of_screen
        s freshSet omega (hendpoint M.1 M.2) (hfresh M.1 M.2) hsLo
  · exact
      trackBLinearPrimeCovariance_sqfreeFreshCoeff_freshSignFlip_eq_of_screen
        s freshSet omega (hendpoint M.1 M.2) (hendpoint N.1 N.2)
        (hfresh M.1 M.2) (hfresh N.1 N.2) hsLo

/-- Any deterministic selector or pruning algorithm fed only the finite
coefficient geometry returns exactly the same object after a screen flip. -/
theorem trackBSquarefreeFreshGeometrySelection_freshSignFlip_eq_of_screen
    (cloud : Finset ℕ) {α : Type*}
    (select : TrackBLinearPrimeCloudGeometry cloud → α)
    (s : Finset ℕ) (freshSet : ℕ → ℕ → Finset ℕ)
    (omega : Omega) (j : ℕ) {X Y : ℕ}
    (hendpoint : ∀ N ∈ cloud, N < X * Y)
    (hfresh : ∀ N ∈ cloud, ∀ p ∈ freshSet j N,
      p ∈ largePrimeInterval X N)
    (hsLo : ∀ q ∈ s, Y < q) :
    select (trackBSquarefreeFreshCloudGeometry
        freshSet (freshSignFlip s omega) j cloud) =
      select (trackBSquarefreeFreshCloudGeometry freshSet omega j cloud) := by
  rw [trackBSquarefreeFreshCloudGeometry_freshSignFlip_eq_of_screen
    s freshSet omega j cloud hendpoint hfresh hsLo]

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.trackBSquarefreeFreshCoeff_freshSignFlip_eq_of_screen
#print axioms Erdos.Problem1144.trackBSquarefreeFreshCoeff_freshSignFlip_fresh_eq
#print axioms Erdos.Problem1144.trackBSquarefreeFreshCoeff_freshSignFlip_subset_eq
#print axioms Erdos.Problem1144.trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_freshSignFlip_eq_neg
#print axioms Erdos.Problem1144.card_trackBSquarefreeFreshCoreOrbitLargeSet_lower
#print axioms Erdos.Problem1144.measureReal_trackBSquarefreeFreshCoreLarge_lower_of_varianceThreshold
#print axioms Erdos.Problem1144.trackBLinearPrimeVariance_sqfreeFreshCoeff_freshSignFlip_eq_of_screen
#print axioms Erdos.Problem1144.trackBLinearPrimeCovariance_sqfreeFreshCoeff_freshSignFlip_eq_of_screen
#print axioms Erdos.Problem1144.trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_freshSignFlip_eq_of_screen
#print axioms Erdos.Problem1144.trackBSquarefreeFreshCloudGeometry_freshSignFlip_eq_of_screen
#print axioms Erdos.Problem1144.trackBSquarefreeFreshGeometrySelection_freshSignFlip_eq_of_screen
