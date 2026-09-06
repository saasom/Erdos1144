import Erdos.Problem1144.HarperTrackBThresholdSparse
import Erdos.Problem1144.HarperTrackBFiniteBlock
import Erdos.Problem1144.SquareConvolution

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-!
# Track B linear fresh-prime threshold package

The rough-core sparse route was too optimistic: low influence for a high-degree
Euler-product polynomial does not by itself give Gaussian one-point tails.  The
correct final analytic core should be linear in a fresh layer of prime signs.

This file records that corrected target.  It defines an abstract finite
fresh-prime linear process

```text
  L_{j,N}(omega) = sum_{p in P_{j,N}} eps_p(omega) c_{j,N,p}(omega),
```

with coefficients measurable with respect to the complementary sigma-algebra in
the intended application.  The latter conditioning is not encoded here; the
analytic certificate supplies the resulting threshold count moments directly.

The payoff is that the core/remainder pair plugs into the existing
`TrackBThresholdAbundanceCertificate` without changing the active final theorem
path.
-/

/-- Coefficient restricted to the declared fresh-prime support. -/
noncomputable def trackBLinearPrimeCoeffOn
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (omega : Omega) (j N p : ℕ) : ℝ :=
  if p ∈ freshSet j N then coeff omega j N p else 0

/-- Raw linear fresh-prime process at stage `j` and test point `N`. -/
noncomputable def trackBLinearPrimeCoreRaw
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (omega : Omega) (j N : ℕ) : ℝ :=
  ∑ p ∈ freshSet j N, eps omega p * coeff omega j N p

/-- Masked linear fresh-prime core.  Outside the analytic good event the core
is set to zero so the threshold abundance bridge can charge the good-event
failure separately. -/
noncomputable def trackBLinearPrimeCore
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (omega : Omega) (j N : ℕ) : ℝ := by
  classical
  exact
    if omega ∈ good j then
      trackBLinearPrimeCoreRaw freshSet coeff omega j N
    else
      0

@[simp] theorem trackBLinearPrimeCore_of_mem
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (omega : Omega) (j N : ℕ)
    (hgood : omega ∈ good j) :
    trackBLinearPrimeCore freshSet coeff good omega j N =
      trackBLinearPrimeCoreRaw freshSet coeff omega j N := by
  simp [trackBLinearPrimeCore, hgood]

@[simp] theorem trackBLinearPrimeCore_of_not_mem
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (omega : Omega) (j N : ℕ)
    (hgood : omega ∉ good j) :
    trackBLinearPrimeCore freshSet coeff good omega j N = 0 := by
  simp [trackBLinearPrimeCore, hgood]

/-- The exact remainder left after subtracting the masked linear core from the
normalized complete sum. -/
noncomputable def trackBLinearPrimeRemainder
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (omega : Omega) (j N : ℕ) : ℝ :=
  normSum omega N - trackBLinearPrimeCore freshSet coeff good omega j N

/-- Unmasked remainder after subtracting the raw linear core.  This is useful
when the certificate uses a scaled/masked core but the analytic second-moment
estimate naturally controls `normSum - rawCore`. -/
noncomputable def trackBLinearPrimeRawRemainder
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (omega : Omega) (j N : ℕ) : ℝ :=
  normSum omega N - trackBLinearPrimeCoreRaw freshSet coeff omega j N

/-- Scaling all coefficients scales the raw linear-prime core. -/
theorem trackBLinearPrimeCoreRaw_scaledCoeff_eq_mul
    (freshSet : ℕ → ℕ → Finset ℕ)
    (rawCoeff scaledCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (omega : Omega) (j N : ℕ) (scale : ℝ)
    (hcoeff :
      ∀ p, p ∈ freshSet j N →
        scaledCoeff omega j N p = scale * rawCoeff omega j N p) :
    trackBLinearPrimeCoreRaw freshSet scaledCoeff omega j N =
      scale * trackBLinearPrimeCoreRaw freshSet rawCoeff omega j N := by
  unfold trackBLinearPrimeCoreRaw
  calc
    (∑ p ∈ freshSet j N, eps omega p * scaledCoeff omega j N p)
        = ∑ p ∈ freshSet j N, eps omega p * (scale * rawCoeff omega j N p) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [hcoeff p hp]
    _ = scale * ∑ p ∈ freshSet j N, eps omega p * rawCoeff omega j N p := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro p _hp
          ring

/-- If the formal core is a `0 <= scale <= 1` multiple of the raw core and is
positive, then a bad formal remainder implies a bad raw remainder. -/
theorem trackBLinearPrimeRawRemainder_lt_of_scaledRemainder_lt
    (freshSet : ℕ → ℕ → Finset ℕ)
    (rawCoeff scaledCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (buffer : ℕ → ℝ)
    (omega : Omega) (j N : ℕ) (scale : ℝ)
    (hscale_nonneg : 0 ≤ scale)
    (hscale_le_one : scale ≤ 1)
    (hcoeff :
      ∀ p, p ∈ freshSet j N →
        scaledCoeff omega j N p = scale * rawCoeff omega j N p)
    (hcore_pos :
      0 < trackBLinearPrimeCore freshSet scaledCoeff good omega j N)
    (hrem :
      trackBLinearPrimeRemainder freshSet scaledCoeff good omega j N <
        -buffer j) :
    trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N < -buffer j := by
  have hgood : omega ∈ good j := by
    by_contra hnot
    have hcore_zero :
        trackBLinearPrimeCore freshSet scaledCoeff good omega j N = 0 :=
      trackBLinearPrimeCore_of_not_mem freshSet scaledCoeff good omega j N hnot
    linarith
  have hcore_scaled :
      trackBLinearPrimeCore freshSet scaledCoeff good omega j N =
        scale * trackBLinearPrimeCoreRaw freshSet rawCoeff omega j N := by
    rw [trackBLinearPrimeCore_of_mem freshSet scaledCoeff good omega j N hgood]
    exact
      trackBLinearPrimeCoreRaw_scaledCoeff_eq_mul
        freshSet rawCoeff scaledCoeff omega j N scale hcoeff
  have hraw_pos :
      0 < trackBLinearPrimeCoreRaw freshSet rawCoeff omega j N := by
    by_contra hnot
    have hraw_nonpos :
        trackBLinearPrimeCoreRaw freshSet rawCoeff omega j N ≤ 0 := le_of_not_gt hnot
    have hscaled_nonpos :
        scale * trackBLinearPrimeCoreRaw freshSet rawCoeff omega j N ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hscale_nonneg hraw_nonpos
    linarith
  have hscaled_le_raw :
      scale * trackBLinearPrimeCoreRaw freshSet rawCoeff omega j N ≤
        trackBLinearPrimeCoreRaw freshSet rawCoeff omega j N := by
    nlinarith [hscale_le_one, hraw_pos]
  unfold trackBLinearPrimeRemainder at hrem
  unfold trackBLinearPrimeRawRemainder
  rw [hcore_scaled] at hrem
  linarith

/-- Conditional variance geometry of the linear coefficient vector, expressed
as a deterministic square sum once the complementary environment is fixed. -/
noncomputable def trackBLinearPrimeVariance
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (omega : Omega) (j N : ℕ) : ℝ :=
  ∑ p ∈ freshSet j N, (coeff omega j N p) ^ 2

/-- Coefficient inner product for two test points.  The union support lets the
formula tolerate different fresh-prime supports. -/
noncomputable def trackBLinearPrimeCovariance
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (omega : Omega) (j N N' : ℕ) : ℝ :=
  ∑ p ∈ freshSet j N ∪ freshSet j N',
    trackBLinearPrimeCoeffOn freshSet coeff omega j N p *
      trackBLinearPrimeCoeffOn freshSet coeff omega j N' p

theorem trackBLinearPrimeVariance_nonneg
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (omega : Omega) (j N : ℕ) :
    0 ≤ trackBLinearPrimeVariance freshSet coeff omega j N := by
  classical
  unfold trackBLinearPrimeVariance
  exact Finset.sum_nonneg fun p _ => sq_nonneg (coeff omega j N p)

/-- The conditional variance proxy is measurable whenever the coefficient
vector is pointwise measurable. -/
theorem measurable_trackBLinearPrimeVariance
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (hcoeff : ∀ j N p, Measurable fun omega : Omega => coeff omega j N p)
    (j N : ℕ) :
    Measurable fun omega : Omega =>
      trackBLinearPrimeVariance freshSet coeff omega j N := by
  classical
  unfold trackBLinearPrimeVariance
  exact Finset.measurable_sum _ fun p _hp =>
    (hcoeff j N p).pow_const 2

theorem trackBLinearPrimeCovariance_eq_zero_of_disjoint
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (omega : Omega) (j N N' : ℕ)
    (hdisj : Disjoint (freshSet j N) (freshSet j N')) :
    trackBLinearPrimeCovariance freshSet coeff omega j N N' = 0 := by
  classical
  unfold trackBLinearPrimeCovariance
  refine Finset.sum_eq_zero ?_
  intro p hp
  by_cases hpN : p ∈ freshSet j N
  · have hpN' : p ∉ freshSet j N' := fun hpN' =>
      (Finset.disjoint_left.mp hdisj hpN hpN').elim
    simp [trackBLinearPrimeCoeffOn, hpN, hpN']
  · simp [trackBLinearPrimeCoeffOn, hpN]

theorem trackBLinearPrimeCovariance_abs_le_of_disjoint
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (omega : Omega) (j N N' : ℕ)
    (rho V : ℕ → ℝ)
    (hdisj : Disjoint (freshSet j N) (freshSet j N'))
    (hbudget_nonneg : 0 ≤ rho j * V j) :
    |trackBLinearPrimeCovariance freshSet coeff omega j N N'| ≤ rho j * V j := by
  rw [trackBLinearPrimeCovariance_eq_zero_of_disjoint freshSet coeff omega j N N' hdisj]
  simpa using hbudget_nonneg

@[simp] theorem trackBLinearPrimeCoeffOn_of_mem
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (omega : Omega) (j N p : ℕ)
    (hp : p ∈ freshSet j N) :
    trackBLinearPrimeCoeffOn freshSet coeff omega j N p =
      coeff omega j N p := by
  simp [trackBLinearPrimeCoeffOn, hp]

@[simp] theorem trackBLinearPrimeCoeffOn_of_not_mem
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (omega : Omega) (j N p : ℕ)
    (hp : p ∉ freshSet j N) :
    trackBLinearPrimeCoeffOn freshSet coeff omega j N p = 0 := by
  simp [trackBLinearPrimeCoeffOn, hp]

/-- The raw linear core may be written with the support-restricted coefficient. -/
theorem trackBLinearPrimeCoreRaw_eq_sum_coeffOn
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (omega : Omega) (j N : ℕ) :
    trackBLinearPrimeCoreRaw freshSet coeff omega j N =
      ∑ p ∈ freshSet j N,
        eps omega p * trackBLinearPrimeCoeffOn freshSet coeff omega j N p := by
  classical
  unfold trackBLinearPrimeCoreRaw
  refine Finset.sum_congr rfl fun p hp => ?_
  simp [trackBLinearPrimeCoeffOn, hp]

/-- Measurability of the raw linear core from measurability of the coefficient
functions. -/
theorem measurable_trackBLinearPrimeCoreRaw
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (hcoeff : ∀ j N p, Measurable fun omega : Omega => coeff omega j N p)
    (j N : ℕ) :
    Measurable fun omega : Omega =>
      trackBLinearPrimeCoreRaw freshSet coeff omega j N := by
  classical
  unfold trackBLinearPrimeCoreRaw
  exact Finset.measurable_sum _ fun p _ =>
    (measurable_eps p).mul (hcoeff j N p)

theorem measurable_trackBLinearPrimeCore
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (j N : ℕ)
    (hgood : MeasurableSet (good j))
    (hraw :
      Measurable fun omega : Omega =>
        trackBLinearPrimeCoreRaw freshSet coeff omega j N) :
    Measurable fun omega : Omega =>
      trackBLinearPrimeCore freshSet coeff good omega j N := by
  unfold trackBLinearPrimeCore
  exact Measurable.ite hgood hraw measurable_const

theorem measurableSet_trackBLinearPrimeThresholdExceedanceEvent
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (M buffer : ℕ → ℝ)
    (j N : ℕ)
    (hgood : MeasurableSet (good j))
    (hraw :
      Measurable fun omega : Omega =>
        trackBLinearPrimeCoreRaw freshSet coeff omega j N) :
    MeasurableSet
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeCore freshSet coeff good) M buffer j N) := by
  unfold trackBThresholdExceedanceEvent
  exact measurableSet_le measurable_const
    (measurable_trackBLinearPrimeCore freshSet coeff good j N hgood hraw)

theorem trackBLinearPrimeThresholdExceedanceEvent_subset_good
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (M buffer : ℕ → ℝ)
    (j N : ℕ)
    (hpos : 0 < M j + buffer j) :
    trackBThresholdExceedanceEvent
        (trackBLinearPrimeCore freshSet coeff good) M buffer j N
      ⊆ good j := by
  intro omega homega
  by_contra hgood
  have hzero :
      trackBLinearPrimeCore freshSet coeff good omega j N = 0 := by
    simp [trackBLinearPrimeCore, hgood]
  unfold trackBThresholdExceedanceEvent at homega
  change M j + buffer j ≤
    trackBLinearPrimeCore freshSet coeff good omega j N at homega
  rw [hzero] at homega
  linarith

theorem trackBLinearPrimeThresholdPairExceedanceEvent_subset_good
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (M buffer : ℕ → ℝ)
    (j N N' : ℕ)
    (hpos : 0 < M j + buffer j) :
    trackBThresholdPairExceedanceEvent
        (trackBLinearPrimeCore freshSet coeff good) M buffer j N N'
      ⊆ good j := by
  intro omega homega
  exact
    trackBLinearPrimeThresholdExceedanceEvent_subset_good
      freshSet coeff good M buffer j N hpos homega.1

/-- With positive threshold, the masked one-point exceedance event is exactly
the raw exceedance event intersected with the good event. -/
theorem trackBLinearPrimeThresholdExceedanceEvent_eq_good_inter_raw
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (M buffer : ℕ → ℝ)
    (j N : ℕ)
    (hpos : 0 < M j + buffer j) :
    trackBThresholdExceedanceEvent
        (trackBLinearPrimeCore freshSet coeff good) M buffer j N =
      good j ∩
        trackBThresholdExceedanceEvent
          (trackBLinearPrimeCoreRaw freshSet coeff) M buffer j N := by
  ext omega
  constructor
  · intro homega
    have hgood :
        omega ∈ good j :=
      trackBLinearPrimeThresholdExceedanceEvent_subset_good
        freshSet coeff good M buffer j N hpos homega
    refine ⟨hgood, ?_⟩
    unfold trackBThresholdExceedanceEvent at homega ⊢
    simpa [trackBLinearPrimeCore_of_mem freshSet coeff good omega j N hgood] using homega
  · intro homega
    rcases homega with ⟨hgood, hraw⟩
    unfold trackBThresholdExceedanceEvent at hraw ⊢
    simpa [trackBLinearPrimeCore_of_mem freshSet coeff good omega j N hgood] using hraw

/-- With positive threshold, the masked pair exceedance event is exactly the
raw pair exceedance event intersected with the good event. -/
theorem trackBLinearPrimeThresholdPairExceedanceEvent_eq_good_inter_raw
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (M buffer : ℕ → ℝ)
    (j N N' : ℕ)
    (hpos : 0 < M j + buffer j) :
    trackBThresholdPairExceedanceEvent
        (trackBLinearPrimeCore freshSet coeff good) M buffer j N N' =
      good j ∩
        trackBThresholdPairExceedanceEvent
          (trackBLinearPrimeCoreRaw freshSet coeff) M buffer j N N' := by
  rw [trackBThresholdPairExceedanceEvent,
    trackBLinearPrimeThresholdExceedanceEvent_eq_good_inter_raw
      freshSet coeff good M buffer j N hpos,
    trackBLinearPrimeThresholdExceedanceEvent_eq_good_inter_raw
      freshSet coeff good M buffer j N' hpos,
    trackBThresholdPairExceedanceEvent]
  ext omega
  constructor
  · intro homega
    exact ⟨homega.1.1, ⟨homega.1.2, homega.2.2⟩⟩
  · intro homega
    exact ⟨⟨homega.1, homega.2.1⟩, ⟨homega.1, homega.2.2⟩⟩

/-!
## Concrete squarefree fresh-prime coefficient layer

The active Track B route will use a fresh-prime linear core.  The definitions
below specialize the abstract `freshSet` / `coeff` API to the squarefree
critical contribution: a term `p*m` is placed in the `p`-coordinate exactly
when `p` is in the declared fresh layer and `m` has no fresh prime factor.

The analytic work still has to prove variance, flatness, covariance, and
Berry--Esseen estimates for these coefficients.  This section only records the
finite objects and the elementary algebraic identities that later estimates
should use.
-/

/-- Finite prime layer between two integer endpoints. -/
noncomputable def trackBFreshPrimeLayer (lo hi : ℕ) : Finset ℕ :=
  (Finset.Icc lo hi).filter Nat.Prime

theorem mem_trackBFreshPrimeLayer {lo hi p : ℕ} :
    p ∈ trackBFreshPrimeLayer lo hi ↔ lo ≤ p ∧ p ≤ hi ∧ Nat.Prime p := by
  simp [trackBFreshPrimeLayer, and_assoc]

/-- Crude cardinality bound for a fresh-prime layer. -/
theorem trackBFreshPrimeLayer_card_le_hi {lo hi : ℕ} (hlo : 0 < lo) :
    (trackBFreshPrimeLayer lo hi).card ≤ hi := by
  classical
  calc
    (trackBFreshPrimeLayer lo hi).card ≤ (Finset.Icc lo hi).card := by
      unfold trackBFreshPrimeLayer
      exact Finset.card_filter_le _ _
    _ ≤ hi := by
      rw [Nat.card_Icc]
      omega

theorem trackBFreshPrimeLayer_disjoint_of_lt
    {lo₁ hi₁ lo₂ hi₂ : ℕ} (hsep : hi₁ < lo₂) :
    Disjoint (trackBFreshPrimeLayer lo₁ hi₁) (trackBFreshPrimeLayer lo₂ hi₂) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  have hp_hi₁ : p ≤ hi₁ := (mem_trackBFreshPrimeLayer.mp hp₁).2.1
  have hlo₂_p : lo₂ ≤ p := (mem_trackBFreshPrimeLayer.mp hp₂).1
  omega

theorem trackBFreshPrimeLayer_disjoint_of_separated
    {lo₁ hi₁ lo₂ hi₂ : ℕ} (hsep : hi₁ < lo₂ ∨ hi₂ < lo₁) :
    Disjoint (trackBFreshPrimeLayer lo₁ hi₁) (trackBFreshPrimeLayer lo₂ hi₂) := by
  rcases hsep with hsep | hsep
  · exact trackBFreshPrimeLayer_disjoint_of_lt hsep
  · exact (trackBFreshPrimeLayer_disjoint_of_lt hsep).symm

/-- `m` has no squarefree-kernel coordinate in the chosen fresh layer. -/
def trackBNoFreshFactor (fresh : Finset ℕ) (m : ℕ) : Prop :=
  Disjoint (sfKernel m) fresh

/-- Coefficient support for the `p`-coordinate of a squarefree fresh-prime
linear core at cutoff `N`.  The condition `p*m <= N` is included explicitly so
later estimates can avoid arithmetic through division when convenient. -/
noncomputable def trackBSquarefreeFreshCoeffSupport
    (fresh : Finset ℕ) (N p : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.Icc 1 (N / p)).filter fun m =>
      Squarefree m ∧ ¬ (p ∣ m) ∧ trackBNoFreshFactor fresh m ∧ p * m ≤ N

theorem mem_trackBSquarefreeFreshCoeffSupport
    {fresh : Finset ℕ} {N p m : ℕ} :
    m ∈ trackBSquarefreeFreshCoeffSupport fresh N p ↔
      1 ≤ m ∧ m ≤ N / p ∧ Squarefree m ∧ ¬ (p ∣ m) ∧
        trackBNoFreshFactor fresh m ∧ p * m ≤ N := by
  simp [trackBSquarefreeFreshCoeffSupport, and_assoc]

theorem trackBSquarefreeFreshCoeffSupport_pos
    {fresh : Finset ℕ} {N p m : ℕ}
    (hm : m ∈ trackBSquarefreeFreshCoeffSupport fresh N p) :
    0 < m := by
  exact lt_of_lt_of_le zero_lt_one (mem_trackBSquarefreeFreshCoeffSupport.mp hm).1

theorem trackBSquarefreeFreshCoeffSupport_squarefree
    {fresh : Finset ℕ} {N p m : ℕ}
    (hm : m ∈ trackBSquarefreeFreshCoeffSupport fresh N p) :
    Squarefree m :=
  (mem_trackBSquarefreeFreshCoeffSupport.mp hm).2.2.1

theorem trackBSquarefreeFreshCoeffSupport_not_dvd
    {fresh : Finset ℕ} {N p m : ℕ}
    (hm : m ∈ trackBSquarefreeFreshCoeffSupport fresh N p) :
    ¬ (p ∣ m) :=
  (mem_trackBSquarefreeFreshCoeffSupport.mp hm).2.2.2.1

theorem trackBSquarefreeFreshCoeffSupport_noFresh
    {fresh : Finset ℕ} {N p m : ℕ}
    (hm : m ∈ trackBSquarefreeFreshCoeffSupport fresh N p) :
    trackBNoFreshFactor fresh m :=
  (mem_trackBSquarefreeFreshCoeffSupport.mp hm).2.2.2.2.1

theorem trackBSquarefreeFreshCoeffSupport_mul_le
    {fresh : Finset ℕ} {N p m : ℕ}
    (hm : m ∈ trackBSquarefreeFreshCoeffSupport fresh N p) :
    p * m ≤ N :=
  (mem_trackBSquarefreeFreshCoeffSupport.mp hm).2.2.2.2.2

/-- The concrete coefficient support is a filtered subset of `Icc 1 (N / p)`,
so its cardinality is at most `N / p`. -/
theorem trackBSquarefreeFreshCoeffSupport_card_le_div
    (fresh : Finset ℕ) (N p : ℕ) :
    (trackBSquarefreeFreshCoeffSupport fresh N p).card ≤ N / p := by
  classical
  calc
    (trackBSquarefreeFreshCoeffSupport fresh N p).card
        ≤ (Finset.Icc 1 (N / p)).card := by
      unfold trackBSquarefreeFreshCoeffSupport
      exact Finset.card_filter_le _ _
    _ = N / p := by
      simp

/-- One squarefree coefficient-support term has square at most `1 / p`. -/
theorem trackBSquarefreeFreshCoeffSupport_term_sq_le_inv_prime
    {p m : ℕ} (hp : Nat.Prime p) (hm_one : 1 ≤ m) :
    ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2 ≤ (p : ℝ)⁻¹ := by
  have hp_nat_pos : 0 < p := hp.pos
  have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one hm_one
  have hpm_nat_pos : 0 < p * m := Nat.mul_pos hp_nat_pos hm_pos
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_nat_pos
  have hpm_pos : (0 : ℝ) < ((p * m : ℕ) : ℝ) := by
    exact_mod_cast hpm_nat_pos
  have hpm_ge_p_nat : p ≤ p * m := by
    simpa using Nat.mul_le_mul_left p hm_one
  have hpm_ge_p : (p : ℝ) ≤ ((p * m : ℕ) : ℝ) := by
    exact_mod_cast hpm_ge_p_nat
  have hinv : (((p * m : ℕ) : ℝ))⁻¹ ≤ (p : ℝ)⁻¹ :=
    (inv_le_inv₀ hpm_pos hp_pos).mpr hpm_ge_p
  have hsqrt_sq :
      (Real.sqrt (((p * m : ℕ) : ℝ))) ^ 2 = ((p * m : ℕ) : ℝ) := by
    simpa using Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((p * m : ℕ) : ℝ))
  calc
    ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2
        = (((p * m : ℕ) : ℝ))⁻¹ := by
          rw [inv_pow, hsqrt_sq]
    _ ≤ (p : ℝ)⁻¹ := hinv

/-- Crude diagonal second-moment bound for one fresh-prime coefficient. -/
theorem trackBSquarefreeFreshCoeffSupport_sq_sum_le_div_mul_inv_prime
    (fresh : Finset ℕ) (N p : ℕ) (hp : Nat.Prime p) :
    (∑ m ∈ trackBSquarefreeFreshCoeffSupport fresh N p,
        ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2) ≤
      ((N / p : ℕ) : ℝ) * (p : ℝ)⁻¹ := by
  classical
  calc
    (∑ m ∈ trackBSquarefreeFreshCoeffSupport fresh N p,
        ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2)
        ≤ ∑ _m ∈ trackBSquarefreeFreshCoeffSupport fresh N p, (p : ℝ)⁻¹ := by
          refine Finset.sum_le_sum ?_
          intro m hm
          exact trackBSquarefreeFreshCoeffSupport_term_sq_le_inv_prime hp
            (mem_trackBSquarefreeFreshCoeffSupport.mp hm).1
    _ = ((trackBSquarefreeFreshCoeffSupport fresh N p).card : ℝ) * (p : ℝ)⁻¹ := by
          simp [nsmul_eq_mul]
    _ ≤ ((N / p : ℕ) : ℝ) * (p : ℝ)⁻¹ := by
          have hcard :
              ((trackBSquarefreeFreshCoeffSupport fresh N p).card : ℝ) ≤
                ((N / p : ℕ) : ℝ) := by
            exact_mod_cast trackBSquarefreeFreshCoeffSupport_card_le_div fresh N p
          exact mul_le_mul_of_nonneg_right hcard
            (inv_nonneg.mpr (by exact_mod_cast Nat.zero_le p))

/-- The squarefree-critical coefficient attached to a fresh prime `p`.

In the final application this is used only for `p ∈ fresh`; outside the fresh
layer the existing `trackBLinearPrimeCoeffOn` wrapper sets the coefficient to
zero. -/
noncomputable def trackBSquarefreeFreshCoeff
    (fresh : Finset ℕ) (omega : Omega) (N p : ℕ) : ℝ :=
  ∑ m ∈ trackBSquarefreeFreshCoeffSupport fresh N p,
    f omega m / Real.sqrt (((p * m : ℕ) : ℝ))

/-- The fresh-prime coefficient is a squarefree weighted sum over its
coefficient support. -/
theorem trackBSquarefreeFreshCoeff_eq_squarefreeWeightedSum
    (fresh : Finset ℕ) (omega : Omega) (N p : ℕ) :
    trackBSquarefreeFreshCoeff fresh omega N p =
      squarefreeWeightedSum
        (trackBSquarefreeFreshCoeffSupport fresh N p)
        (fun m => (Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) omega := by
  classical
  unfold trackBSquarefreeFreshCoeff squarefreeWeightedSum
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hm_sq : Squarefree m := trackBSquarefreeFreshCoeffSupport_squarefree hm
  rw [gSquarefree_of_squarefree omega hm_sq]
  ring

/-- The square of one fresh-prime coefficient is integrable. -/
theorem integrable_trackBSquarefreeFreshCoeff_sq
    (fresh : Finset ℕ) (N p : ℕ) :
    Integrable
      (fun omega : Omega => (trackBSquarefreeFreshCoeff fresh omega N p) ^ 2) mu := by
  let S := trackBSquarefreeFreshCoeffSupport fresh N p
  let w : ℕ → ℝ := fun m => (Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹
  have hfun :
      (fun omega : Omega => (trackBSquarefreeFreshCoeff fresh omega N p) ^ 2) =
        fun omega : Omega => (squarefreeWeightedSum S w omega) ^ 2 := by
    funext omega
    rw [trackBSquarefreeFreshCoeff_eq_squarefreeWeightedSum]
  rw [hfun]
  exact integrable_squarefreeWeightedSum_sq S w

/-- Exact diagonal second moment of one fresh-prime coefficient. -/
theorem integral_trackBSquarefreeFreshCoeff_sq_eq
    (fresh : Finset ℕ) (N p : ℕ) :
    ∫ omega,
        (trackBSquarefreeFreshCoeff fresh omega N p) ^ 2 ∂mu =
      ∑ m ∈ trackBSquarefreeFreshCoeffSupport fresh N p,
        ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2 := by
  let S := trackBSquarefreeFreshCoeffSupport fresh N p
  let w : ℕ → ℝ := fun m => (Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹
  have hfun :
      (fun omega : Omega => (trackBSquarefreeFreshCoeff fresh omega N p) ^ 2) =
        fun omega : Omega => (squarefreeWeightedSum S w omega) ^ 2 := by
    funext omega
    rw [trackBSquarefreeFreshCoeff_eq_squarefreeWeightedSum]
  rw [hfun]
  exact
    integral_squarefreeWeightedSum_sq_eq_diag S w
      (fun m hm => trackBSquarefreeFreshCoeffSupport_pos hm)
      (fun m hm => trackBSquarefreeFreshCoeffSupport_squarefree hm)

/-- The absolute value of a concrete fresh-prime coefficient is bounded by the
corresponding deterministic reciprocal-square-root weight sum. -/
theorem abs_trackBSquarefreeFreshCoeff_le_reciprocal_sum
    (fresh : Finset ℕ) (omega : Omega) (N p : ℕ) :
    |trackBSquarefreeFreshCoeff fresh omega N p| ≤
      ∑ m ∈ trackBSquarefreeFreshCoeffSupport fresh N p,
        (Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹ := by
  classical
  unfold trackBSquarefreeFreshCoeff
  calc
    |∑ m ∈ trackBSquarefreeFreshCoeffSupport fresh N p,
        f omega m / Real.sqrt (((p * m : ℕ) : ℝ))|
        ≤
          ∑ m ∈ trackBSquarefreeFreshCoeffSupport fresh N p,
            |f omega m / Real.sqrt (((p * m : ℕ) : ℝ))| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ =
          ∑ m ∈ trackBSquarefreeFreshCoeffSupport fresh N p,
            (Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹ := by
      refine Finset.sum_congr rfl ?_
      intro m _hm
      rw [abs_div, abs_f, abs_of_nonneg (Real.sqrt_nonneg _), one_div]

/-- Crude deterministic support-size flatness bound for a fresh-prime
coefficient: every reciprocal-square-root term is at most `1 / sqrt p`. -/
theorem trackBSquarefreeFreshCoeff_reciprocal_sum_le_card_mul_inv_sqrt
    (fresh : Finset ℕ) (N p : ℕ) (hp_pos : 0 < p) :
    (∑ m ∈ trackBSquarefreeFreshCoeffSupport fresh N p,
        (Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ≤
      ((trackBSquarefreeFreshCoeffSupport fresh N p).card : ℝ) *
        (Real.sqrt ((p : ℕ) : ℝ))⁻¹ := by
  classical
  calc
    (∑ m ∈ trackBSquarefreeFreshCoeffSupport fresh N p,
        (Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹)
        ≤
          ∑ m ∈ trackBSquarefreeFreshCoeffSupport fresh N p,
            (Real.sqrt ((p : ℕ) : ℝ))⁻¹ := by
      refine Finset.sum_le_sum ?_
      intro m hm
      have hm_one : 1 ≤ m := (mem_trackBSquarefreeFreshCoeffSupport.mp hm).1
      have hpm_nat : p ≤ p * m := by
        have hmul := Nat.mul_le_mul_left p hm_one
        simpa using hmul
      have hpm_real : ((p : ℕ) : ℝ) ≤ ((p * m : ℕ) : ℝ) := by
        exact_mod_cast hpm_nat
      have hsqrt :
          Real.sqrt ((p : ℕ) : ℝ) ≤ Real.sqrt (((p * m : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt hpm_real
      have hsqrt_pos : 0 < Real.sqrt ((p : ℕ) : ℝ) :=
        Real.sqrt_pos.2 (by exact_mod_cast hp_pos)
      simpa [one_div] using one_div_le_one_div_of_le hsqrt_pos hsqrt
    _ =
        ((trackBSquarefreeFreshCoeffSupport fresh N p).card : ℝ) *
          (Real.sqrt ((p : ℕ) : ℝ))⁻¹ := by
      simp [nsmul_eq_mul]

/-- Cardinality flatness can be bounded further by the crude divisor scale
`N / p`. -/
theorem trackBSquarefreeFreshCoeff_card_mul_inv_sqrt_le_div_mul_inv_sqrt
    (fresh : Finset ℕ) (N p : ℕ) :
    ((trackBSquarefreeFreshCoeffSupport fresh N p).card : ℝ) *
        (Real.sqrt ((p : ℕ) : ℝ))⁻¹ ≤
      ((N / p : ℕ) : ℝ) * (Real.sqrt ((p : ℕ) : ℝ))⁻¹ := by
  have hcard :
      ((trackBSquarefreeFreshCoeffSupport fresh N p).card : ℝ) ≤
        ((N / p : ℕ) : ℝ) := by
    exact_mod_cast trackBSquarefreeFreshCoeffSupport_card_le_div fresh N p
  exact mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- Stage/test-point form of `trackBSquarefreeFreshCoeff`, matching the
abstract linear-prime certificate API. -/
noncomputable def trackBSquarefreeFreshLinearCoeff
    (freshSet : ℕ → ℕ → Finset ℕ)
    (omega : Omega) (j N p : ℕ) : ℝ :=
  trackBSquarefreeFreshCoeff (freshSet j N) omega N p

/-- Exact expectation of the squarefree fresh-prime variance proxy. -/
theorem integral_trackBLinearPrimeVariance_sqfreeFreshCoeff_eq
    (freshSet : ℕ → ℕ → Finset ℕ) (j N : ℕ) :
    ∫ omega,
        trackBLinearPrimeVariance freshSet
          (trackBSquarefreeFreshLinearCoeff freshSet) omega j N ∂mu =
      ∑ p ∈ freshSet j N,
        ∑ m ∈ trackBSquarefreeFreshCoeffSupport (freshSet j N) N p,
          ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2 := by
  classical
  unfold trackBLinearPrimeVariance trackBSquarefreeFreshLinearCoeff
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro p _hp
    exact integral_trackBSquarefreeFreshCoeff_sq_eq (freshSet j N) N p
  · intro p _hp
    exact integrable_trackBSquarefreeFreshCoeff_sq (freshSet j N) N p

/-- The concrete squarefree fresh-prime core is exactly the abstract raw core
with `trackBSquarefreeFreshLinearCoeff`. -/
theorem trackBLinearPrimeCoreRaw_sqfreeFreshCoeff
    (freshSet : ℕ → ℕ → Finset ℕ) (omega : Omega) (j N : ℕ) :
    trackBLinearPrimeCoreRaw freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) omega j N =
      ∑ p ∈ freshSet j N,
        eps omega p *
          trackBSquarefreeFreshCoeff (freshSet j N) omega N p := by
  rfl

/-- A single supported squarefree fresh-prime term is linear in the fresh sign. -/
theorem eps_mul_squarefreeFreshCoeff_term
    (omega : Omega) {fresh : Finset ℕ} {N p m : ℕ}
    (hp : Nat.Prime p)
    (hm : m ∈ trackBSquarefreeFreshCoeffSupport fresh N p) :
    eps omega p * (f omega m / Real.sqrt (((p * m : ℕ) : ℝ))) =
      f omega (p * m) / Real.sqrt (((p * m : ℕ) : ℝ)) := by
  have hm_pos : 0 < m := trackBSquarefreeFreshCoeffSupport_pos hm
  have hpm : ¬ p ∣ m := trackBSquarefreeFreshCoeffSupport_not_dvd hm
  rw [f_prime_mul_of_not_dvd omega hp hm_pos hpm]
  ring

/-- Pair-indexed squarefree fresh-prime contribution represented by the
products `p*m`.  This is the unmasked squarefree contribution that the concrete
linear coefficient layer isolates. -/
noncomputable def trackBSquarefreeFreshPairContribution
    (fresh : Finset ℕ) (omega : Omega) (N : ℕ) : ℝ :=
  ∑ p ∈ fresh, ∑ m ∈ trackBSquarefreeFreshCoeffSupport fresh N p,
    f omega (p * m) / Real.sqrt (((p * m : ℕ) : ℝ))

/-- Pair index set for the concrete squarefree fresh-prime layer. -/
noncomputable def trackBSquarefreeFreshPairs
    (fresh : Finset ℕ) (N : ℕ) : Finset (Sigma fun _p : ℕ => ℕ) :=
  fresh.sigma fun p => trackBSquarefreeFreshCoeffSupport fresh N p

theorem mem_trackBSquarefreeFreshPairs
    {fresh : Finset ℕ} {N : ℕ} {a : Sigma fun _p : ℕ => ℕ} :
    a ∈ trackBSquarefreeFreshPairs fresh N ↔
      a.1 ∈ fresh ∧ a.2 ∈ trackBSquarefreeFreshCoeffSupport fresh N a.1 := by
  simp [trackBSquarefreeFreshPairs]

/-- Pair contribution as a single sum over the dependent pair index set. -/
theorem trackBSquarefreeFreshPairContribution_eq_sum_pairs
    (fresh : Finset ℕ) (omega : Omega) (N : ℕ) :
    trackBSquarefreeFreshPairContribution fresh omega N =
      ∑ a ∈ trackBSquarefreeFreshPairs fresh N,
        f omega (a.1 * a.2) / Real.sqrt (((a.1 * a.2 : ℕ) : ℝ)) := by
  classical
  unfold trackBSquarefreeFreshPairContribution trackBSquarefreeFreshPairs
  rw [Finset.sum_sigma']

/-- Product set generated by the squarefree fresh-prime pairs. -/
noncomputable def trackBSquarefreeFreshProductSet
    (fresh : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (trackBSquarefreeFreshPairs fresh N).image fun a => a.1 * a.2

/-- Product-indexed squarefree fresh-prime contribution. -/
noncomputable def trackBSquarefreeFreshProductContribution
    (fresh : Finset ℕ) (omega : Omega) (N : ℕ) : ℝ :=
  ∑ n ∈ trackBSquarefreeFreshProductSet fresh N,
    f omega n / Real.sqrt ((n : ℕ) : ℝ)

/-- The product map is injective on the squarefree fresh-prime pairs. -/
theorem trackBSquarefreeFreshPair_product_injective
    {fresh : Finset ℕ} {N : ℕ}
    (hprime : ∀ p, p ∈ fresh → Nat.Prime p) :
    Set.InjOn
      (fun a : Sigma fun _p : ℕ => ℕ => a.1 * a.2)
      (trackBSquarefreeFreshPairs fresh N) := by
  intro a ha b hb hab
  rcases a with ⟨p, m⟩
  rcases b with ⟨q, k⟩
  simp only at hab ⊢
  rcases (mem_trackBSquarefreeFreshPairs.mp ha) with ⟨hp_mem, hm_mem⟩
  rcases (mem_trackBSquarefreeFreshPairs.mp hb) with ⟨hq_mem, hk_mem⟩
  have hp_prime : Nat.Prime p := hprime p hp_mem
  have hq_prime : Nat.Prime q := hprime q hq_mem
  have hpq : p = q := by
    have hp_dvd_qk : p ∣ q * k := by
      rw [← hab]
      exact dvd_mul_right p m
    rcases hp_prime.dvd_mul.mp hp_dvd_qk with hp_dvd_q | hp_dvd_k
    · have hqp : q = p :=
        (hq_prime.dvd_iff_eq hp_prime.ne_one).mp hp_dvd_q
      exact hqp.symm
    · have hk_sf : Squarefree k :=
        trackBSquarefreeFreshCoeffSupport_squarefree hk_mem
      have hno : trackBNoFreshFactor fresh k :=
        trackBSquarefreeFreshCoeffSupport_noFresh hk_mem
      have hp_kernel : p ∈ sfKernel k :=
        (mem_sfKernel_iff_dvd_of_squarefree hk_sf hp_prime).mpr hp_dvd_k
      exact (Finset.disjoint_left.mp hno hp_kernel hp_mem).elim
  subst q
  have hmk : m = k := Nat.mul_left_cancel hp_prime.pos hab
  subst k
  rfl

/-- When products are indexed by the generated product set, the contribution is
the same as the pair contribution. -/
theorem trackBSquarefreeFreshProductContribution_eq_pairContribution
    (fresh : Finset ℕ) (omega : Omega) (N : ℕ)
    (hprime : ∀ p, p ∈ fresh → Nat.Prime p) :
    trackBSquarefreeFreshProductContribution fresh omega N =
      trackBSquarefreeFreshPairContribution fresh omega N := by
  classical
  unfold trackBSquarefreeFreshProductContribution trackBSquarefreeFreshProductSet
  rw [Finset.sum_image (trackBSquarefreeFreshPair_product_injective hprime)]
  rw [← trackBSquarefreeFreshPairContribution_eq_sum_pairs]

theorem mem_trackBSquarefreeFreshProductSet
    {fresh : Finset ℕ} {N n : ℕ} :
    n ∈ trackBSquarefreeFreshProductSet fresh N ↔
      ∃ a ∈ trackBSquarefreeFreshPairs fresh N, a.1 * a.2 = n := by
  classical
  simp [trackBSquarefreeFreshProductSet]

theorem trackBSquarefreeFreshProductSet_le
    {fresh : Finset ℕ} {N n : ℕ}
    (hn : n ∈ trackBSquarefreeFreshProductSet fresh N) :
    n ≤ N := by
  rcases mem_trackBSquarefreeFreshProductSet.mp hn with ⟨a, ha, rfl⟩
  rcases a with ⟨p, m⟩
  exact trackBSquarefreeFreshCoeffSupport_mul_le
    (mem_trackBSquarefreeFreshPairs.mp ha).2

theorem trackBSquarefreeFreshProductSet_squarefree
    {fresh : Finset ℕ} {N n : ℕ}
    (hprime : ∀ p, p ∈ fresh → Nat.Prime p)
    (hn : n ∈ trackBSquarefreeFreshProductSet fresh N) :
    Squarefree n := by
  rcases mem_trackBSquarefreeFreshProductSet.mp hn with ⟨a, ha, rfl⟩
  rcases a with ⟨p, m⟩
  rcases mem_trackBSquarefreeFreshPairs.mp ha with ⟨hp_mem, hm_mem⟩
  have hp_prime : Nat.Prime p := hprime p hp_mem
  have hm_sq : Squarefree m := trackBSquarefreeFreshCoeffSupport_squarefree hm_mem
  have hpm : ¬ p ∣ m := trackBSquarefreeFreshCoeffSupport_not_dvd hm_mem
  have hcop : Nat.Coprime p m := hp_prime.coprime_iff_not_dvd.mpr hpm
  exact (Nat.squarefree_mul hcop).mpr ⟨hp_prime.squarefree, hm_sq⟩

theorem trackBSquarefreeFreshProductContribution_eq_squarefreeWeightedSum
    (fresh : Finset ℕ) (omega : Omega) (N : ℕ)
    (hprime : ∀ p, p ∈ fresh → Nat.Prime p) :
    trackBSquarefreeFreshProductContribution fresh omega N =
      squarefreeWeightedSum (trackBSquarefreeFreshProductSet fresh N)
        (fun n => (Real.sqrt ((n : ℕ) : ℝ))⁻¹) omega := by
  classical
  unfold trackBSquarefreeFreshProductContribution squarefreeWeightedSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn_sq : Squarefree n :=
    trackBSquarefreeFreshProductSet_squarefree hprime hn
  rw [gSquarefree_of_squarefree omega hn_sq, div_eq_mul_inv, mul_comm]

/-- If the declared fresh layer consists of primes, the raw linear core with
the concrete squarefree coefficients is exactly the pair-indexed squarefree
fresh-prime contribution. -/
theorem trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_eq_pairContribution
    (freshSet : ℕ → ℕ → Finset ℕ) (omega : Omega) (j N : ℕ)
    (hprime : ∀ p, p ∈ freshSet j N → Nat.Prime p) :
    trackBLinearPrimeCoreRaw freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) omega j N =
      trackBSquarefreeFreshPairContribution (freshSet j N) omega N := by
  classical
  calc
    trackBLinearPrimeCoreRaw freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) omega j N
        =
      ∑ p ∈ freshSet j N,
        eps omega p *
          trackBSquarefreeFreshCoeff (freshSet j N) omega N p := by
        rfl
    _ =
      ∑ p ∈ freshSet j N,
        ∑ m ∈ trackBSquarefreeFreshCoeffSupport (freshSet j N) N p,
          eps omega p *
            (f omega m / Real.sqrt (((p * m : ℕ) : ℝ))) := by
        refine Finset.sum_congr rfl ?_
        intro p _hp
        unfold trackBSquarefreeFreshCoeff
        rw [Finset.mul_sum]
    _ =
      trackBSquarefreeFreshPairContribution (freshSet j N) omega N := by
        unfold trackBSquarefreeFreshPairContribution
        refine Finset.sum_congr rfl ?_
        intro p hp
        refine Finset.sum_congr rfl ?_
        intro m hm
        exact eps_mul_squarefreeFreshCoeff_term omega (hprime p hp) hm

/-- Combined concrete reindexing theorem: the raw squarefree fresh-prime
linear core is the product-indexed squarefree contribution generated by the
fresh-prime pairs. -/
theorem trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_eq_productContribution
    (freshSet : ℕ → ℕ → Finset ℕ) (omega : Omega) (j N : ℕ)
    (hprime : ∀ p, p ∈ freshSet j N → Nat.Prime p) :
    trackBLinearPrimeCoreRaw freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) omega j N =
      trackBSquarefreeFreshProductContribution (freshSet j N) omega N := by
  rw [trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_eq_pairContribution
    freshSet omega j N hprime]
  exact (trackBSquarefreeFreshProductContribution_eq_pairContribution
    (freshSet j N) omega N hprime).symm

/-- Weighted-sum form of the concrete fresh-prime reindexing theorem.  This is
the version expected by the squarefree second-moment and tail machinery. -/
theorem trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_eq_squarefreeWeightedSum
    (freshSet : ℕ → ℕ → Finset ℕ) (omega : Omega) (j N : ℕ)
    (hprime : ∀ p, p ∈ freshSet j N → Nat.Prime p) :
    trackBLinearPrimeCoreRaw freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) omega j N =
      squarefreeWeightedSum (trackBSquarefreeFreshProductSet (freshSet j N) N)
        (fun n => (Real.sqrt ((n : ℕ) : ℝ))⁻¹) omega := by
  rw [trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_eq_productContribution
    freshSet omega j N hprime]
  exact trackBSquarefreeFreshProductContribution_eq_squarefreeWeightedSum
    (freshSet j N) omega N hprime

/-- On the analytic good event, the masked concrete fresh-prime core is the
squarefree weighted contribution generated by the fresh-prime product set. -/
theorem trackBLinearPrimeCore_sqfreeFreshCoeff_eq_squarefreeWeightedSum_of_mem
    (freshSet : ℕ → ℕ → Finset ℕ) (good : ℕ → Set Omega)
    (omega : Omega) (j N : ℕ)
    (hgood : omega ∈ good j)
    (hprime : ∀ p, p ∈ freshSet j N → Nat.Prime p) :
    trackBLinearPrimeCore freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) good omega j N =
      squarefreeWeightedSum (trackBSquarefreeFreshProductSet (freshSet j N) N)
        (fun n => (Real.sqrt ((n : ℕ) : ℝ))⁻¹) omega := by
  unfold trackBLinearPrimeCore
  simp [hgood, trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_eq_squarefreeWeightedSum
    freshSet omega j N hprime]

@[simp] theorem trackBLinearPrimeCore_sqfreeFreshCoeff_eq_zero_of_not_mem
    (freshSet : ℕ → ℕ → Finset ℕ) (good : ℕ → Set Omega)
    (omega : Omega) (j N : ℕ)
    (hgood : omega ∉ good j) :
    trackBLinearPrimeCore freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) good omega j N = 0 := by
  simp [trackBLinearPrimeCore, hgood]

/-- On the analytic good event, the exact remainder is the normalized complete
sum minus the squarefree weighted fresh-prime contribution. -/
theorem trackBLinearPrimeRemainder_sqfreeFreshCoeff_eq_of_mem
    (freshSet : ℕ → ℕ → Finset ℕ) (good : ℕ → Set Omega)
    (omega : Omega) (j N : ℕ)
    (hgood : omega ∈ good j)
    (hprime : ∀ p, p ∈ freshSet j N → Nat.Prime p) :
    trackBLinearPrimeRemainder freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) good omega j N =
      normSum omega N -
        squarefreeWeightedSum (trackBSquarefreeFreshProductSet (freshSet j N) N)
          (fun n => (Real.sqrt ((n : ℕ) : ℝ))⁻¹) omega := by
  unfold trackBLinearPrimeRemainder
  rw [trackBLinearPrimeCore_sqfreeFreshCoeff_eq_squarefreeWeightedSum_of_mem
    freshSet good omega j N hgood hprime]

/-- The concrete squarefree fresh-prime coefficients are measurable. -/
theorem measurable_trackBSquarefreeFreshLinearCoeff
    (freshSet : ℕ → ℕ → Finset ℕ) (j N p : ℕ) :
    Measurable fun omega : Omega =>
      trackBSquarefreeFreshLinearCoeff freshSet omega j N p := by
  classical
  unfold trackBSquarefreeFreshLinearCoeff trackBSquarefreeFreshCoeff
  exact Finset.measurable_sum _ fun m _ =>
    (measurable_f m).div_const _

/-- The abstract raw-core measurability lemma specialized to the concrete
squarefree fresh-prime coefficients. -/
theorem measurable_trackBLinearPrimeCoreRaw_sqfreeFreshCoeff
    (freshSet : ℕ → ℕ → Finset ℕ) (j N : ℕ) :
    Measurable fun omega : Omega =>
      trackBLinearPrimeCoreRaw freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) omega j N :=
  measurable_trackBLinearPrimeCoreRaw freshSet
    (trackBSquarefreeFreshLinearCoeff freshSet)
    (measurable_trackBSquarefreeFreshLinearCoeff freshSet) j N

theorem measurable_trackBLinearPrimeCore_sqfreeFreshCoeff
    (freshSet : ℕ → ℕ → Finset ℕ) (good : ℕ → Set Omega)
    (j N : ℕ)
    (hgood : MeasurableSet (good j)) :
    Measurable fun omega : Omega =>
      trackBLinearPrimeCore freshSet
        (trackBSquarefreeFreshLinearCoeff freshSet) good omega j N :=
  measurable_trackBLinearPrimeCore freshSet
    (trackBSquarefreeFreshLinearCoeff freshSet) good j N hgood
    (measurable_trackBLinearPrimeCoreRaw_sqfreeFreshCoeff freshSet j N)

theorem measurableSet_trackBThresholdExceedanceEvent_sqfreeFreshCoeff
    (freshSet : ℕ → ℕ → Finset ℕ) (good : ℕ → Set Omega)
    (M buffer : ℕ → ℝ) (j N : ℕ)
    (hgood : MeasurableSet (good j)) :
    MeasurableSet
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeCore freshSet
          (trackBSquarefreeFreshLinearCoeff freshSet) good)
        M buffer j N) :=
  measurableSet_trackBLinearPrimeThresholdExceedanceEvent freshSet
    (trackBSquarefreeFreshLinearCoeff freshSet) good M buffer j N hgood
    (measurable_trackBLinearPrimeCoreRaw_sqfreeFreshCoeff freshSet j N)

/-!
## Scheduled sparse mesh helpers

The final Track B certificate will use a sparse list of test points
`point j r` and a finite fresh-prime interval attached to each index `r`.
The existing linear-prime certificate is indexed by the test point `N`, so the
scheduled fresh set below gathers the fresh layers for all indices mapping to
the same `N`.  In the intended schedule the map `r ↦ point j r` is injective,
and the equality lemma below recovers the single attached layer.
-/

/-- Finite index set for the stage-`j` sparse Track B mesh. -/
noncomputable def trackBLinearPrimeMeshIndexSet (Q : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  Finset.Icc 1 (Q j)

theorem mem_trackBLinearPrimeMeshIndexSet {Q : ℕ → ℕ} {j r : ℕ} :
    r ∈ trackBLinearPrimeMeshIndexSet Q j ↔ 1 ≤ r ∧ r ≤ Q j := by
  simp [trackBLinearPrimeMeshIndexSet]

theorem trackBLinearPrimeMeshIndexSet_card (Q : ℕ → ℕ) (j : ℕ) :
    (trackBLinearPrimeMeshIndexSet Q j).card = Q j := by
  simp [trackBLinearPrimeMeshIndexSet]

/-- Test-point set generated by the stage-`j` sparse mesh. -/
noncomputable def trackBLinearPrimeMeshTestSet
    (Q : ℕ → ℕ) (point : ℕ → ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  (trackBLinearPrimeMeshIndexSet Q j).image (point j)

theorem mem_trackBLinearPrimeMeshTestSet
    {Q : ℕ → ℕ} {point : ℕ → ℕ → ℕ} {j N : ℕ} :
    N ∈ trackBLinearPrimeMeshTestSet Q point j ↔
      ∃ r ∈ trackBLinearPrimeMeshIndexSet Q j, point j r = N := by
  simp [trackBLinearPrimeMeshTestSet]

theorem trackBLinearPrimeMeshTestSet_card_of_injOn
    (Q : ℕ → ℕ) (point : ℕ → ℕ → ℕ) (j : ℕ)
    (hinj : Set.InjOn (point j) (trackBLinearPrimeMeshIndexSet Q j : Set ℕ)) :
    (trackBLinearPrimeMeshTestSet Q point j).card = Q j := by
  rw [trackBLinearPrimeMeshTestSet]
  rw [Finset.card_image_of_injOn]
  · exact trackBLinearPrimeMeshIndexSet_card Q j
  · simpa using hinj

theorem trackBLinearPrimeMesh_injOn_of_strict
    (Q : ℕ → ℕ) (point : ℕ → ℕ → ℕ) (j : ℕ)
    (hstrict :
      ∀ ⦃r s⦄, r ∈ trackBLinearPrimeMeshIndexSet Q j →
        s ∈ trackBLinearPrimeMeshIndexSet Q j → r < s → point j r < point j s) :
    Set.InjOn (point j) (trackBLinearPrimeMeshIndexSet Q j : Set ℕ) := by
  intro r hr s hs hEq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hp : point j r < point j s := hstrict (by simpa using hr) (by simpa using hs) hlt
    rw [hEq] at hp
    exact (lt_irrefl _ hp).elim
  · have hp : point j s < point j r := hstrict (by simpa using hs) (by simpa using hr) hgt
    rw [hEq] at hp
    exact (lt_irrefl _ hp).elim

theorem trackBLinearPrimeMeshTestSet_in_block_of_point_in_block
    (lo hi Q : ℕ → ℕ) (point : ℕ → ℕ → ℕ) (j : ℕ)
    (hpoint :
      ∀ r, r ∈ trackBLinearPrimeMeshIndexSet Q j →
        point j r ∈ Finset.Icc (lo j) (hi j)) :
    ∀ N, N ∈ trackBLinearPrimeMeshTestSet Q point j → N ∈ Finset.Icc (lo j) (hi j) := by
  intro N hN
  rcases mem_trackBLinearPrimeMeshTestSet.mp hN with ⟨r, hr, rfl⟩
  exact hpoint r hr

/-- Fresh-prime layer attached to a test point by a scheduled sparse mesh.
If several indices generate the same test point, this is the union of their
fresh layers.  The final schedule should prove injectivity and use
`trackBLinearPrimeScheduledFreshSet_eq_layer_of_unique` to reduce this union to
one layer. -/
noncomputable def trackBLinearPrimeScheduledFreshSet
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (j N : ℕ) : Finset ℕ :=
  ((trackBLinearPrimeMeshIndexSet Q j).filter fun r => point j r = N).biUnion
    fun r => trackBFreshPrimeLayer (freshLo j r) (freshHi j r)

theorem mem_trackBLinearPrimeScheduledFreshSet
    {Q : ℕ → ℕ} {point freshLo freshHi : ℕ → ℕ → ℕ}
    {j N p : ℕ} :
    p ∈ trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N ↔
      ∃ r ∈ trackBLinearPrimeMeshIndexSet Q j,
        point j r = N ∧ p ∈ trackBFreshPrimeLayer (freshLo j r) (freshHi j r) := by
  classical
  simp [trackBLinearPrimeScheduledFreshSet, and_assoc]

theorem trackBLinearPrimeScheduledFreshSet_prime
    {Q : ℕ → ℕ} {point freshLo freshHi : ℕ → ℕ → ℕ}
    {j N p : ℕ}
    (hp : p ∈ trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N) :
    Nat.Prime p := by
  rcases mem_trackBLinearPrimeScheduledFreshSet.mp hp with ⟨r, _hr, _hpoint, hp_layer⟩
  exact (mem_trackBFreshPrimeLayer.mp hp_layer).2.2

theorem trackBFreshPrimeLayer_subset_scheduledFreshSet_at_point
    {Q : ℕ → ℕ} {point freshLo freshHi : ℕ → ℕ → ℕ}
    {j r : ℕ}
    (hr : r ∈ trackBLinearPrimeMeshIndexSet Q j) :
    trackBFreshPrimeLayer (freshLo j r) (freshHi j r) ⊆
      trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j (point j r) := by
  classical
  intro p hp
  rw [mem_trackBLinearPrimeScheduledFreshSet]
  exact ⟨r, hr, rfl, hp⟩

theorem trackBLinearPrimeScheduledFreshSet_eq_layer_of_unique
    {Q : ℕ → ℕ} {point freshLo freshHi : ℕ → ℕ → ℕ}
    {j r : ℕ}
    (hr : r ∈ trackBLinearPrimeMeshIndexSet Q j)
    (hunique :
      ∀ s, s ∈ trackBLinearPrimeMeshIndexSet Q j → point j s = point j r → s = r) :
    trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j (point j r) =
      trackBFreshPrimeLayer (freshLo j r) (freshHi j r) := by
  classical
  ext p
  constructor
  · intro hp
    rcases mem_trackBLinearPrimeScheduledFreshSet.mp hp with ⟨s, hs, hpoint, hp_layer⟩
    rw [hunique s hs hpoint] at hp_layer
    exact hp_layer
  · intro hp
    exact trackBFreshPrimeLayer_subset_scheduledFreshSet_at_point hr hp

theorem trackBLinearPrimeScheduledFreshSet_disjoint_of_interval_disjoint
    {Q : ℕ → ℕ} {point freshLo freshHi : ℕ → ℕ → ℕ}
    {j N N' : ℕ}
    (_hN : N ∈ trackBLinearPrimeMeshTestSet Q point j)
    (_hN' : N' ∈ trackBLinearPrimeMeshTestSet Q point j)
    (hne : N ≠ N')
    (hsep :
      ∀ r s, r ∈ trackBLinearPrimeMeshIndexSet Q j →
        s ∈ trackBLinearPrimeMeshIndexSet Q j → r ≠ s →
          freshHi j r < freshLo j s ∨ freshHi j s < freshLo j r) :
    Disjoint
      (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N)
      (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N') := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hp'
  rcases mem_trackBLinearPrimeScheduledFreshSet.mp hp with
    ⟨r, hr, hpoint, hp_layer⟩
  rcases mem_trackBLinearPrimeScheduledFreshSet.mp hp' with
    ⟨s, hs, hpoint', hp_layer'⟩
  have hrs : r ≠ s := by
    intro hrs
    apply hne
    rw [← hpoint, ← hpoint', hrs]
  have hdisj :
      Disjoint
        (trackBFreshPrimeLayer (freshLo j r) (freshHi j r))
        (trackBFreshPrimeLayer (freshLo j s) (freshHi j s)) :=
    trackBFreshPrimeLayer_disjoint_of_separated (hsep r s hr hs hrs)
  exact (Finset.disjoint_left.mp hdisj hp_layer hp_layer').elim

/-- Scheduled concrete squarefree fresh-prime coefficient. -/
noncomputable def trackBLinearPrimeScheduledFreshCoeff
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (omega : Omega) (j N p : ℕ) : ℝ :=
  trackBSquarefreeFreshLinearCoeff
    (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi) omega j N p

/-- Scheduled concrete squarefree fresh-prime raw core. -/
noncomputable def trackBLinearPrimeScheduledCoreRaw
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (omega : Omega) (j N : ℕ) : ℝ :=
  trackBLinearPrimeCoreRaw
    (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi)
    (trackBLinearPrimeScheduledFreshCoeff Q point freshLo freshHi) omega j N

/-- Scheduled concrete squarefree fresh-prime masked core. -/
noncomputable def trackBLinearPrimeScheduledCore
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (omega : Omega) (j N : ℕ) : ℝ :=
  trackBLinearPrimeCore
    (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi)
    (trackBLinearPrimeScheduledFreshCoeff Q point freshLo freshHi) good omega j N

/-- Scheduled exact remainder after subtracting the masked fresh-prime core. -/
noncomputable def trackBLinearPrimeScheduledRemainder
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (omega : Omega) (j N : ℕ) : ℝ :=
  trackBLinearPrimeRemainder
    (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi)
    (trackBLinearPrimeScheduledFreshCoeff Q point freshLo freshHi) good omega j N

/-- Scheduled variance of the concrete fresh-prime coefficient vector. -/
noncomputable def trackBLinearPrimeScheduledVariance
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (omega : Omega) (j N : ℕ) : ℝ :=
  trackBLinearPrimeVariance
    (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi)
    (trackBLinearPrimeScheduledFreshCoeff Q point freshLo freshHi) omega j N

/-- Scheduled covariance of two concrete fresh-prime coefficient vectors. -/
noncomputable def trackBLinearPrimeScheduledCovariance
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (omega : Omega) (j N N' : ℕ) : ℝ :=
  trackBLinearPrimeCovariance
    (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi)
    (trackBLinearPrimeScheduledFreshCoeff Q point freshLo freshHi) omega j N N'

theorem trackBLinearPrimeScheduledVariance_nonneg
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (omega : Omega) (j N : ℕ) :
    0 ≤ trackBLinearPrimeScheduledVariance Q point freshLo freshHi omega j N :=
  trackBLinearPrimeVariance_nonneg
    (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi)
    (trackBLinearPrimeScheduledFreshCoeff Q point freshLo freshHi) omega j N

/-- The scheduled squarefree fresh-prime variance proxy is measurable. -/
theorem measurable_trackBLinearPrimeScheduledVariance
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (j N : ℕ) :
    Measurable fun omega : Omega =>
      trackBLinearPrimeScheduledVariance Q point freshLo freshHi omega j N := by
  unfold trackBLinearPrimeScheduledVariance
  exact
    measurable_trackBLinearPrimeVariance
      (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi)
      (trackBLinearPrimeScheduledFreshCoeff Q point freshLo freshHi)
      (by
        intro j N p
        unfold trackBLinearPrimeScheduledFreshCoeff
        exact
          measurable_trackBSquarefreeFreshLinearCoeff
            (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi) j N p)
      j N

/-- The scheduled squarefree fresh-prime variance proxy is integrable. -/
theorem integrable_trackBLinearPrimeScheduledVariance
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (j N : ℕ) :
    Integrable
      (fun omega : Omega =>
        trackBLinearPrimeScheduledVariance Q point freshLo freshHi omega j N) mu := by
  unfold trackBLinearPrimeScheduledVariance trackBLinearPrimeVariance
  exact
    integrable_finset_sum
      (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N)
      fun p _hp => by
        unfold trackBLinearPrimeScheduledFreshCoeff trackBSquarefreeFreshLinearCoeff
        exact integrable_trackBSquarefreeFreshCoeff_sq _ _ _

/-- Exact expectation of the scheduled squarefree fresh-prime variance proxy. -/
theorem integral_trackBLinearPrimeScheduledVariance_eq
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (j N : ℕ) :
    ∫ omega,
        trackBLinearPrimeScheduledVariance Q point freshLo freshHi omega j N ∂mu =
      ∑ p ∈ trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N,
        ∑ m ∈
          trackBSquarefreeFreshCoeffSupport
            (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N) N p,
          ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2 := by
  unfold trackBLinearPrimeScheduledVariance trackBLinearPrimeScheduledFreshCoeff
  exact
    integral_trackBLinearPrimeVariance_sqfreeFreshCoeff_eq
      (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi) j N

theorem trackBLinearPrimeScheduledCovariance_eq_zero_of_disjoint
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (omega : Omega) (j N N' : ℕ)
    (hdisj :
      Disjoint
        (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N)
        (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N')) :
    trackBLinearPrimeScheduledCovariance Q point freshLo freshHi omega j N N' = 0 :=
  trackBLinearPrimeCovariance_eq_zero_of_disjoint
    (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi)
    (trackBLinearPrimeScheduledFreshCoeff Q point freshLo freshHi) omega j N N' hdisj

theorem trackBLinearPrimeScheduledCovariance_abs_le_of_disjoint
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (omega : Omega) (j N N' : ℕ)
    (rho V : ℕ → ℝ)
    (hdisj :
      Disjoint
        (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N)
        (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N'))
    (hbudget_nonneg : 0 ≤ rho j * V j) :
    |trackBLinearPrimeScheduledCovariance Q point freshLo freshHi omega j N N'|
      ≤ rho j * V j :=
  trackBLinearPrimeCovariance_abs_le_of_disjoint
    (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi)
    (trackBLinearPrimeScheduledFreshCoeff Q point freshLo freshHi)
    omega j N N' rho V hdisj hbudget_nonneg

theorem trackBLinearPrimeScheduledCoreRaw_eq_squarefreeWeightedSum
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (omega : Omega) (j N : ℕ) :
    trackBLinearPrimeScheduledCoreRaw Q point freshLo freshHi omega j N =
      squarefreeWeightedSum
        (trackBSquarefreeFreshProductSet
          (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N) N)
        (fun n => (Real.sqrt ((n : ℕ) : ℝ))⁻¹) omega := by
  unfold trackBLinearPrimeScheduledCoreRaw trackBLinearPrimeScheduledFreshCoeff
  exact
    trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_eq_squarefreeWeightedSum
      (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi) omega j N
      (fun p hp => trackBLinearPrimeScheduledFreshSet_prime hp)

theorem trackBLinearPrimeScheduledCore_eq_squarefreeWeightedSum_of_mem
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (omega : Omega) (j N : ℕ)
    (hgood : omega ∈ good j) :
    trackBLinearPrimeScheduledCore Q point freshLo freshHi good omega j N =
      squarefreeWeightedSum
        (trackBSquarefreeFreshProductSet
          (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N) N)
        (fun n => (Real.sqrt ((n : ℕ) : ℝ))⁻¹) omega := by
  unfold trackBLinearPrimeScheduledCore trackBLinearPrimeScheduledFreshCoeff
  exact
    trackBLinearPrimeCore_sqfreeFreshCoeff_eq_squarefreeWeightedSum_of_mem
      (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi) good omega j N hgood
      (fun p hp => trackBLinearPrimeScheduledFreshSet_prime hp)

theorem trackBLinearPrimeScheduledRemainder_eq_of_mem
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (omega : Omega) (j N : ℕ)
    (hgood : omega ∈ good j) :
    trackBLinearPrimeScheduledRemainder Q point freshLo freshHi good omega j N =
      normSum omega N -
        squarefreeWeightedSum
          (trackBSquarefreeFreshProductSet
            (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N) N)
          (fun n => (Real.sqrt ((n : ℕ) : ℝ))⁻¹) omega := by
  unfold trackBLinearPrimeScheduledRemainder trackBLinearPrimeScheduledFreshCoeff
  exact
    trackBLinearPrimeRemainder_sqfreeFreshCoeff_eq_of_mem
      (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi) good omega j N hgood
      (fun p hp => trackBLinearPrimeScheduledFreshSet_prime hp)

theorem measurable_trackBLinearPrimeScheduledCore
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (j N : ℕ)
    (hgood : MeasurableSet (good j)) :
    Measurable fun omega : Omega =>
      trackBLinearPrimeScheduledCore Q point freshLo freshHi good omega j N := by
  unfold trackBLinearPrimeScheduledCore trackBLinearPrimeScheduledFreshCoeff
  exact
    measurable_trackBLinearPrimeCore_sqfreeFreshCoeff
      (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi) good j N hgood

theorem measurableSet_trackBThresholdExceedanceEvent_scheduledCore
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (M buffer : ℕ → ℝ)
    (j N : ℕ)
    (hgood : MeasurableSet (good j)) :
    MeasurableSet
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
        M buffer j N) := by
  unfold trackBLinearPrimeScheduledCore trackBLinearPrimeScheduledFreshCoeff
  exact
    measurableSet_trackBThresholdExceedanceEvent_sqfreeFreshCoeff
      (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi)
      good M buffer j N hgood

/-- Scheduled pair-exceedance events are measurable when the good event is
measurable. -/
theorem measurableSet_trackBThresholdPairExceedanceEvent_scheduledCore
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (M buffer : ℕ → ℝ)
    (j N N' : ℕ)
    (hgood : MeasurableSet (good j)) :
    MeasurableSet
      (trackBThresholdPairExceedanceEvent
        (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
        M buffer j N N') :=
  (measurableSet_trackBThresholdExceedanceEvent_scheduledCore
    Q point freshLo freshHi good M buffer j N hgood).inter
  (measurableSet_trackBThresholdExceedanceEvent_scheduledCore
    Q point freshLo freshHi good M buffer j N' hgood)

/-- Scheduled specialization of the abstract overlap-to-remainder-bad reduction.
This is the deterministic bridge used by the selected-remainder estimate:
bounding many bad exact remainders automatically bounds many points where a
linear-prime exceedance is cancelled by the remainder. -/
theorem trackBLinearPrimeScheduledOverlapMany_subset_remainderBadMany
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (M buffer : ℕ → ℝ) (r : ℕ → ℕ) (j : ℕ) :
    trackBThresholdOverlapMany
        (trackBLinearPrimeMeshTestSet Q point)
        (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
        (trackBLinearPrimeScheduledRemainder Q point freshLo freshHi good)
        M buffer r j ⊆
      {omega |
        r j ≤
          (trackBThresholdRemainderBadSet
            (trackBLinearPrimeMeshTestSet Q point)
            (trackBLinearPrimeScheduledRemainder Q point freshLo freshHi good)
            buffer omega j).card} :=
  trackBThresholdOverlapMany_subset_remainderBadMany
    (trackBLinearPrimeMeshTestSet Q point)
    (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
    (trackBLinearPrimeScheduledRemainder Q point freshLo freshHi good)
    M buffer r j

/-- Measure form of
`trackBLinearPrimeScheduledOverlapMany_subset_remainderBadMany`. -/
theorem measure_trackBLinearPrimeScheduledOverlapMany_le_remainderBadMany
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (M buffer : ℕ → ℝ) (r : ℕ → ℕ) (j : ℕ) :
    mu
        (trackBThresholdOverlapMany
          (trackBLinearPrimeMeshTestSet Q point)
          (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
          (trackBLinearPrimeScheduledRemainder Q point freshLo freshHi good)
          M buffer r j) ≤
      mu
        {omega |
          r j ≤
            (trackBThresholdRemainderBadSet
              (trackBLinearPrimeMeshTestSet Q point)
              (trackBLinearPrimeScheduledRemainder Q point freshLo freshHi good)
              buffer omega j).card} :=
  measure_mono
    (trackBLinearPrimeScheduledOverlapMany_subset_remainderBadMany
      Q point freshLo freshHi good M buffer r j)

/-- Selected-overlap correction for a scaled certificate core.  If the
certificate coefficient is a pointwise `0 <= scale <= 1` multiple of a raw
coefficient, then every selected bad formal remainder is also bad for the raw
unscaled remainder. -/
theorem trackBLinearPrimeScaledOverlapSet_subset_rawRemainderBadSet
    (testSet : ℕ → Finset ℕ)
    (freshSet : ℕ → ℕ → Finset ℕ)
    (rawCoeff scaledCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (M buffer : ℕ → ℝ) (scale : ℕ → ℕ → ℝ)
    (omega : Omega) (j : ℕ)
    (hthreshold_pos : 0 < M j + buffer j)
    (hscale_nonneg : ∀ N, N ∈ testSet j → 0 ≤ scale j N)
    (hscale_le_one : ∀ N, N ∈ testSet j → scale j N ≤ 1)
    (hcoeff :
      ∀ N, N ∈ testSet j →
        ∀ p, p ∈ freshSet j N →
          scaledCoeff omega j N p = scale j N * rawCoeff omega j N p) :
    trackBThresholdOverlapSet testSet
        (trackBLinearPrimeCore freshSet scaledCoeff good)
        (trackBLinearPrimeRemainder freshSet scaledCoeff good)
        M buffer omega j ⊆
      trackBThresholdRemainderBadSet testSet
        (trackBLinearPrimeRawRemainder freshSet rawCoeff) buffer omega j := by
  intro N hN
  rw [mem_trackBThresholdOverlapSet] at hN
  rcases hN with ⟨hNtest, hcore, hrem⟩
  rw [mem_trackBThresholdRemainderBadSet]
  refine ⟨hNtest, ?_⟩
  exact
    trackBLinearPrimeRawRemainder_lt_of_scaledRemainder_lt
      freshSet rawCoeff scaledCoeff good buffer omega j N (scale j N)
      (hscale_nonneg N hNtest) (hscale_le_one N hNtest)
      (hcoeff N hNtest) (lt_of_lt_of_le hthreshold_pos hcore) hrem

/-- Many-overlap version of
`trackBLinearPrimeScaledOverlapSet_subset_rawRemainderBadSet`. -/
theorem trackBLinearPrimeScaledOverlapMany_subset_rawRemainderBadMany
    (testSet : ℕ → Finset ℕ)
    (freshSet : ℕ → ℕ → Finset ℕ)
    (rawCoeff scaledCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (M buffer : ℕ → ℝ) (r : ℕ → ℕ) (scale : ℕ → ℕ → ℝ)
    (j : ℕ)
    (hthreshold_pos : 0 < M j + buffer j)
    (hscale_nonneg : ∀ N, N ∈ testSet j → 0 ≤ scale j N)
    (hscale_le_one : ∀ N, N ∈ testSet j → scale j N ≤ 1)
    (hcoeff :
      ∀ omega N, N ∈ testSet j →
        ∀ p, p ∈ freshSet j N →
          scaledCoeff omega j N p = scale j N * rawCoeff omega j N p) :
    trackBThresholdOverlapMany testSet
        (trackBLinearPrimeCore freshSet scaledCoeff good)
        (trackBLinearPrimeRemainder freshSet scaledCoeff good)
        M buffer r j ⊆
      {omega |
        r j ≤
          (trackBThresholdRemainderBadSet testSet
            (trackBLinearPrimeRawRemainder freshSet rawCoeff) buffer omega j).card} := by
  intro omega homega
  exact le_trans homega
    (Finset.card_le_card
      (trackBLinearPrimeScaledOverlapSet_subset_rawRemainderBadSet
        testSet freshSet rawCoeff scaledCoeff good M buffer scale omega j
        hthreshold_pos hscale_nonneg hscale_le_one (hcoeff omega)))

/-- Union-bound control of scaled-core selected overlap from one-point
unscaled raw-remainder probabilities. -/
theorem measure_trackBLinearPrimeScaledOverlapMany_le_sum_raw_single
    (testSet : ℕ → Finset ℕ)
    (freshSet : ℕ → ℕ → Finset ℕ)
    (rawCoeff scaledCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (M buffer : ℕ → ℝ) (r : ℕ → ℕ) (scale : ℕ → ℕ → ℝ)
    (j : ℕ)
    (hr_pos : 0 < r j)
    (hthreshold_pos : 0 < M j + buffer j)
    (hscale_nonneg : ∀ N, N ∈ testSet j → 0 ≤ scale j N)
    (hscale_le_one : ∀ N, N ∈ testSet j → scale j N ≤ 1)
    (hcoeff :
      ∀ omega N, N ∈ testSet j →
        ∀ p, p ∈ freshSet j N →
          scaledCoeff omega j N p = scale j N * rawCoeff omega j N p) :
    mu
        (trackBThresholdOverlapMany testSet
          (trackBLinearPrimeCore freshSet scaledCoeff good)
          (trackBLinearPrimeRemainder freshSet scaledCoeff good)
          M buffer r j) ≤
      ∑ N ∈ testSet j,
        mu {omega |
          trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N < -buffer j} := by
  exact le_trans
    (measure_mono
      (trackBLinearPrimeScaledOverlapMany_subset_rawRemainderBadMany
        testSet freshSet rawCoeff scaledCoeff good M buffer r scale j
        hthreshold_pos hscale_nonneg hscale_le_one hcoeff))
    (measure_trackBThresholdRemainderBadMany_le_sum_single
      testSet (trackBLinearPrimeRawRemainder freshSet rawCoeff) buffer r j hr_pos)

/-- One-point lower-tail control for the raw linear-prime remainder from its
second moment. -/
theorem measure_trackBLinearPrimeRawRemainder_lt_neg_le_second
    (freshSet : ℕ → ℕ → Finset ℕ)
    (rawCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (buffer : ℕ → ℝ) (rawSecond : ℕ → ℕ → ℝ)
    (j N : ℕ)
    (hbuffer : 0 < buffer j)
    (hint :
      Integrable
        (fun omega =>
          (trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N) ^ 2) mu)
    (hsecond :
      (∫ omega,
          (trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N) ^ 2 ∂mu)
        ≤ rawSecond j N) :
    mu {omega |
        trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N < -buffer j}
      ≤ ENNReal.ofReal (rawSecond j N / (buffer j) ^ 2) := by
  have hsubset :
      {omega |
        trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N < -buffer j} ⊆
        {omega |
          buffer j <
            |trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N|} := by
    intro omega hbad
    change trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N < -buffer j at hbad
    have hlt_neg :
        buffer j <
          -trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N := by
      linarith
    exact lt_of_lt_of_le hlt_neg (neg_le_abs _)
  calc
    mu
        {omega |
          trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N <
            -buffer j}
        ≤ mu
            {omega |
              buffer j <
                |trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N|} :=
          measure_mono hsubset
    _ ≤ ENNReal.ofReal (rawSecond j N / (buffer j) ^ 2) := by
          exact
            measure_abs_error_gt_le_second
              (E := fun omega =>
                trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N)
              (A := buffer j)
              (V := rawSecond j N)
              hbuffer hint hsecond

/-- Finite raw-remainder second-moment budget over the stage test set. -/
noncomputable def trackBLinearPrimeRawRemainderSecondMomentBudget
    (testSet : ℕ → Finset ℕ)
    (buffer : ℕ → ℝ) (rawSecond : ℕ → ℕ → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑ N ∈ testSet j, ENNReal.ofReal (rawSecond j N / (buffer j) ^ 2)

/-- Package form of the scaled-core selected-overlap correction: one-point
raw-remainder bounds plus a finite union budget imply the overlap field for
the scaled formal core/remainder pair. -/
theorem prob_trackBLinearPrimeScaledOverlapMany_le_of_raw_single
    (testSet : ℕ → Finset ℕ)
    (freshSet : ℕ → ℕ → Finset ℕ)
    (rawCoeff scaledCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (M buffer : ℕ → ℝ) (r : ℕ → ℕ) (scale : ℕ → ℕ → ℝ)
    (singleFail failOverlap : ℕ → ℝ≥0∞)
    (r_pos : ∀ j, 0 < r j)
    (threshold_pos : ∀ j, 0 < M j + buffer j)
    (scale_nonneg : ∀ j N, N ∈ testSet j → 0 ≤ scale j N)
    (scale_le_one : ∀ j N, N ∈ testSet j → scale j N ≤ 1)
    (coeff_scaled :
      ∀ omega j N, N ∈ testSet j →
        ∀ p, p ∈ freshSet j N →
          scaledCoeff omega j N p = scale j N * rawCoeff omega j N p)
    (one_point_raw_remainder_bad :
      ∀ j N, N ∈ testSet j →
        mu
            {omega |
              trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N < -buffer j}
          ≤ singleFail j)
    (union_budget :
      ∀ j, (∑ _N ∈ testSet j, singleFail j) ≤ failOverlap j) :
    ∀ j,
      mu
          (trackBThresholdOverlapMany testSet
            (trackBLinearPrimeCore freshSet scaledCoeff good)
            (trackBLinearPrimeRemainder freshSet scaledCoeff good)
            M buffer r j) ≤
        failOverlap j := by
  intro j
  calc
    mu
        (trackBThresholdOverlapMany testSet
          (trackBLinearPrimeCore freshSet scaledCoeff good)
          (trackBLinearPrimeRemainder freshSet scaledCoeff good)
          M buffer r j)
        ≤ ∑ N ∈ testSet j,
            mu
              {omega |
                trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N < -buffer j} := by
          exact
            measure_trackBLinearPrimeScaledOverlapMany_le_sum_raw_single
              testSet freshSet rawCoeff scaledCoeff good M buffer r scale j
              (r_pos j) (threshold_pos j) (scale_nonneg j) (scale_le_one j)
              (coeff_scaled · j)
    _ ≤ ∑ _N ∈ testSet j, singleFail j := by
          exact Finset.sum_le_sum fun N hN => one_point_raw_remainder_bad j N hN
    _ ≤ failOverlap j := union_budget j

/-- Package form of the scaled-core selected-overlap correction using
pointwise raw-remainder second moments directly. -/
theorem prob_trackBLinearPrimeScaledOverlapMany_le_of_raw_second
    (testSet : ℕ → Finset ℕ)
    (freshSet : ℕ → ℕ → Finset ℕ)
    (rawCoeff scaledCoeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (M buffer : ℕ → ℝ) (r : ℕ → ℕ) (scale : ℕ → ℕ → ℝ)
    (rawSecond : ℕ → ℕ → ℝ) (failOverlap : ℕ → ℝ≥0∞)
    (r_pos : ∀ j, 0 < r j)
    (threshold_pos : ∀ j, 0 < M j + buffer j)
    (buffer_pos : ∀ j, 0 < buffer j)
    (scale_nonneg : ∀ j N, N ∈ testSet j → 0 ≤ scale j N)
    (scale_le_one : ∀ j N, N ∈ testSet j → scale j N ≤ 1)
    (coeff_scaled :
      ∀ omega j N, N ∈ testSet j →
        ∀ p, p ∈ freshSet j N →
          scaledCoeff omega j N p = scale j N * rawCoeff omega j N p)
    (raw_second_integrable :
      ∀ j N, N ∈ testSet j →
        Integrable
          (fun omega =>
            (trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N) ^ 2) mu)
    (raw_second_upper :
      ∀ j N, N ∈ testSet j →
        (∫ omega,
            (trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N) ^ 2 ∂mu)
          ≤ rawSecond j N)
    (second_budget :
      ∀ j,
        trackBLinearPrimeRawRemainderSecondMomentBudget testSet buffer rawSecond j ≤
          failOverlap j) :
    ∀ j,
      mu
          (trackBThresholdOverlapMany testSet
            (trackBLinearPrimeCore freshSet scaledCoeff good)
            (trackBLinearPrimeRemainder freshSet scaledCoeff good)
            M buffer r j) ≤
        failOverlap j := by
  intro j
  calc
    mu
        (trackBThresholdOverlapMany testSet
          (trackBLinearPrimeCore freshSet scaledCoeff good)
          (trackBLinearPrimeRemainder freshSet scaledCoeff good)
          M buffer r j)
        ≤ ∑ N ∈ testSet j,
            mu
              {omega |
                trackBLinearPrimeRawRemainder freshSet rawCoeff omega j N < -buffer j} := by
          exact
            measure_trackBLinearPrimeScaledOverlapMany_le_sum_raw_single
              testSet freshSet rawCoeff scaledCoeff good M buffer r scale j
              (r_pos j) (threshold_pos j) (scale_nonneg j) (scale_le_one j)
              (coeff_scaled · j)
    _ ≤ trackBLinearPrimeRawRemainderSecondMomentBudget testSet buffer rawSecond j := by
          unfold trackBLinearPrimeRawRemainderSecondMomentBudget
          exact Finset.sum_le_sum fun N hN =>
            measure_trackBLinearPrimeRawRemainder_lt_neg_le_second
              freshSet rawCoeff buffer rawSecond j N (buffer_pos j)
              (raw_second_integrable j N hN) (raw_second_upper j N hN)
    _ ≤ failOverlap j := second_budget j

/-- A small scheduled certificate for paying the selected-overlap field from a
direct many-bad-remainders estimate. -/
structure TrackBLinearPrimeScheduledRemainderBadManyCertificate
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (buffer : ℕ → ℝ)
    (r : ℕ → ℕ) (failOverlap : ℕ → ℝ≥0∞) : Prop where
  prob_remainder_bad_many :
    ∀ j,
      mu
          {omega |
            r j ≤
              (trackBThresholdRemainderBadSet
                (trackBLinearPrimeMeshTestSet Q point)
                (trackBLinearPrimeScheduledRemainder Q point freshLo freshHi good)
                buffer omega j).card} ≤
        failOverlap j

/-- A direct many-bad-remainders estimate supplies the scheduled
selected-overlap probability field. -/
theorem prob_scheduledOverlapMany_le_of_remainderBadManyCertificate
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (M buffer : ℕ → ℝ)
    (r : ℕ → ℕ) (failOverlap : ℕ → ℝ≥0∞)
    (h :
      TrackBLinearPrimeScheduledRemainderBadManyCertificate
        Q point freshLo freshHi good buffer r failOverlap) :
    ∀ j,
      mu
          (trackBThresholdOverlapMany
            (trackBLinearPrimeMeshTestSet Q point)
            (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
            (trackBLinearPrimeScheduledRemainder Q point freshLo freshHi good)
            M buffer r j) ≤
        failOverlap j := by
  intro j
  exact le_trans
    (measure_trackBLinearPrimeScheduledOverlapMany_le_remainderBadMany
      Q point freshLo freshHi good M buffer r j)
    (h.prob_remainder_bad_many j)

/-- Build the scheduled many-bad-remainders certificate from one-point
bad-remainder probability bounds and a finite union-budget. -/
noncomputable def trackBLinearPrimeScheduledRemainderBadManyCertificate_of_single
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (buffer : ℕ → ℝ)
    (r : ℕ → ℕ) (singleFail failOverlap : ℕ → ℝ≥0∞)
    (r_pos : ∀ j, 0 < r j)
    (one_point_remainder_bad :
      ∀ j N, N ∈ trackBLinearPrimeMeshTestSet Q point j →
        mu
            {omega |
              trackBLinearPrimeScheduledRemainder
                  Q point freshLo freshHi good omega j N < -buffer j}
          ≤ singleFail j)
    (union_budget :
      ∀ j,
        (∑ _N ∈ trackBLinearPrimeMeshTestSet Q point j, singleFail j) ≤
          failOverlap j) :
    TrackBLinearPrimeScheduledRemainderBadManyCertificate
      Q point freshLo freshHi good buffer r failOverlap where
  prob_remainder_bad_many := by
    intro j
    calc
      mu
          {omega |
            r j ≤
              (trackBThresholdRemainderBadSet
                (trackBLinearPrimeMeshTestSet Q point)
                (trackBLinearPrimeScheduledRemainder Q point freshLo freshHi good)
                buffer omega j).card}
          ≤
            ∑ N ∈ trackBLinearPrimeMeshTestSet Q point j,
              mu
                {omega |
                  trackBLinearPrimeScheduledRemainder
                      Q point freshLo freshHi good omega j N < -buffer j} := by
        exact
          measure_trackBThresholdRemainderBadMany_le_sum_single
            (trackBLinearPrimeMeshTestSet Q point)
            (trackBLinearPrimeScheduledRemainder Q point freshLo freshHi good)
            buffer r j (r_pos j)
      _ ≤ ∑ N ∈ trackBLinearPrimeMeshTestSet Q point j, singleFail j := by
        refine Finset.sum_le_sum ?_
        intro N hN
        exact one_point_remainder_bad j N hN
      _ ≤ failOverlap j := union_budget j

/-- Variant of
`trackBLinearPrimeScheduledRemainderBadManyCertificate_of_single` using mesh
injectivity to rewrite the finite union budget as `Q j` copies of the
one-point failure budget. -/
noncomputable def trackBLinearPrimeScheduledRemainderBadManyCertificate_of_single_injOn
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (buffer : ℕ → ℝ)
    (r : ℕ → ℕ) (singleFail failOverlap : ℕ → ℝ≥0∞)
    (r_pos : ∀ j, 0 < r j)
    (mesh_inj :
      ∀ j, Set.InjOn (point j) (trackBLinearPrimeMeshIndexSet Q j : Set ℕ))
    (one_point_remainder_bad :
      ∀ j N, N ∈ trackBLinearPrimeMeshTestSet Q point j →
        mu
            {omega |
              trackBLinearPrimeScheduledRemainder
                  Q point freshLo freshHi good omega j N < -buffer j}
          ≤ singleFail j)
    (union_budget :
      ∀ j, (Q j) • singleFail j ≤ failOverlap j) :
    TrackBLinearPrimeScheduledRemainderBadManyCertificate
      Q point freshLo freshHi good buffer r failOverlap :=
  trackBLinearPrimeScheduledRemainderBadManyCertificate_of_single
    Q point freshLo freshHi good buffer r singleFail failOverlap r_pos
    one_point_remainder_bad
    (fun j => by
      have hcard :
          (trackBLinearPrimeMeshTestSet Q point j).card = Q j :=
        trackBLinearPrimeMeshTestSet_card_of_injOn Q point j (mesh_inj j)
      simpa [hcard] using union_budget j)

/-- Variant of
`trackBLinearPrimeScheduledRemainderBadManyCertificate_of_single_injOn` where
mesh injectivity is obtained from strict growth of the scheduled points. -/
noncomputable def trackBLinearPrimeScheduledRemainderBadManyCertificate_of_single_strict
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (buffer : ℕ → ℝ)
    (r : ℕ → ℕ) (singleFail failOverlap : ℕ → ℝ≥0∞)
    (r_pos : ∀ j, 0 < r j)
    (point_strict :
      ∀ j ⦃r s⦄, r ∈ trackBLinearPrimeMeshIndexSet Q j →
        s ∈ trackBLinearPrimeMeshIndexSet Q j → r < s → point j r < point j s)
    (one_point_remainder_bad :
      ∀ j N, N ∈ trackBLinearPrimeMeshTestSet Q point j →
        mu
            {omega |
              trackBLinearPrimeScheduledRemainder
                  Q point freshLo freshHi good omega j N < -buffer j}
          ≤ singleFail j)
    (union_budget :
      ∀ j, (Q j) • singleFail j ≤ failOverlap j) :
    TrackBLinearPrimeScheduledRemainderBadManyCertificate
      Q point freshLo freshHi good buffer r failOverlap :=
  trackBLinearPrimeScheduledRemainderBadManyCertificate_of_single_injOn
    Q point freshLo freshHi good buffer r singleFail failOverlap r_pos
    (fun j => trackBLinearPrimeMesh_injOn_of_strict Q point j (point_strict j))
    one_point_remainder_bad union_budget

/-- Deterministic absorption for the exact linear-core remainder. -/
theorem normSum_ge_of_trackBLinearPrimeCore_ge_of_remainder_ge
    (freshSet : ℕ → ℕ → Finset ℕ)
    (coeff : Omega → ℕ → ℕ → ℕ → ℝ)
    (good : ℕ → Set Omega)
    (M buffer : ℕ → ℝ)
    (omega : Omega) (j N : ℕ)
    (hcore :
      M j + buffer j ≤
        trackBLinearPrimeCore freshSet coeff good omega j N)
    (hrem :
      -buffer j ≤
        trackBLinearPrimeRemainder freshSet coeff good omega j N) :
    M j ≤ normSum omega N := by
  unfold trackBLinearPrimeRemainder at hrem
  linarith

/-- Linear fresh-prime analytic package.  The probability fields are the same
finite threshold-count inputs consumed by `TrackBThresholdAbundanceCertificate`.
The extra geometry fields state the intended Berry--Esseen coefficient
certificate: variance floor, coefficient flatness, and small off-diagonal
inner products on the good event. -/
structure TrackBLinearPrimeThresholdCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  freshSet : ℕ → ℕ → Finset ℕ
  coeff : Omega → ℕ → ℕ → ℕ → ℝ
  good : ℕ → Set Omega
  r : ℕ → ℕ
  failGood : ℕ → ℝ≥0∞
  failOverlap : ℕ → ℝ≥0∞
  countMean : ℕ → ℝ
  countSecond : ℕ → ℝ
  V : ℕ → ℝ
  flat : ℕ → ℝ
  rho : ℕ → ℝ
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  variance_floor :
    ∀ omega j N, omega ∈ good j → N ∈ testSet j →
      V j ≤ trackBLinearPrimeVariance freshSet coeff omega j N
  coeff_flat :
    ∀ omega j N p, omega ∈ good j → N ∈ testSet j →
      p ∈ freshSet j N → |coeff omega j N p| ≤ flat j
  covariance_bound :
    ∀ omega j N N', omega ∈ good j → N ∈ testSet j → N' ∈ testSet j →
      N ≠ N' →
        |trackBLinearPrimeCovariance freshSet coeff omega j N N'|
          ≤ rho j * V j
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  count_centered_second_integrable :
    ∀ j,
      Integrable
        (fun omega =>
          (trackBThresholdExceedanceCountReal testSet
              (trackBLinearPrimeCore freshSet coeff good) M buffer j omega -
            ∫ omega',
              trackBThresholdExceedanceCountReal testSet
                (trackBLinearPrimeCore freshSet coeff good) M buffer j omega'
                ∂mu) ^ 2)
        mu
  count_mean_lower :
    ∀ j,
      countMean j ≤
        ∫ omega,
          trackBThresholdExceedanceCountReal testSet
            (trackBLinearPrimeCore freshSet coeff good) M buffer j omega ∂mu
  count_centered_second_upper :
    ∀ j,
      (∫ omega,
          (trackBThresholdExceedanceCountReal testSet
              (trackBLinearPrimeCore freshSet coeff good) M buffer j omega -
            ∫ omega',
              trackBThresholdExceedanceCountReal testSet
                (trackBLinearPrimeCore freshSet coeff good) M buffer j omega'
                ∂mu) ^ 2 ∂mu)
        ≤ countSecond j
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
          (trackBThresholdOverlapMany testSet
            (trackBLinearPrimeCore freshSet coeff good)
            (trackBLinearPrimeRemainder freshSet coeff good)
            M buffer r j) ≤
        failOverlap j

/-- The linear fresh-prime package is a specialization of the abstract sparse
threshold-abundance certificate. -/
noncomputable def trackBThresholdAbundanceCertificate_of_linearPrime
    (h : TrackBLinearPrimeThresholdCertificate) :
    TrackBThresholdAbundanceCertificate where
  lo := h.lo
  hi := h.hi
  M := h.M
  buffer := h.buffer
  testSet := h.testSet
  core := trackBLinearPrimeCore h.freshSet h.coeff h.good
  remainder := trackBLinearPrimeRemainder h.freshSet h.coeff h.good
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
  absorb := by
    intro omega j N _hN hcore hrem
    exact
      normSum_ge_of_trackBLinearPrimeCore_ge_of_remainder_ge
        h.freshSet h.coeff h.good h.M h.buffer omega j N hcore hrem
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  count_centered_second_integrable := h.count_centered_second_integrable
  count_mean_lower := h.count_mean_lower
  count_centered_second_upper := h.count_centered_second_upper
  fail_summable := h.fail_summable
  prob_good_compl := h.prob_good_compl
  prob_overlap_many := h.prob_overlap_many

/-- Direct closure from a linear fresh-prime threshold package. -/
theorem erdos1144_of_trackBLinearPrimeThresholdCertificate
    (h : TrackBLinearPrimeThresholdCertificate) :
    Erdos1144 :=
  erdos1144_of_trackBThresholdAbundanceCertificate
    (trackBThresholdAbundanceCertificate_of_linearPrime h)

/-- Linear fresh-prime package in the one-point/two-point tail form expected
from Berry-Esseen.  This is the most convenient interface for the corrected Track B
core: geometry fields record the coefficient estimates, while the tail fields
record the resulting threshold-count inputs. -/
structure TrackBLinearPrimeUniformTailProbabilityCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  freshSet : ℕ → ℕ → Finset ℕ
  coeff : Omega → ℕ → ℕ → ℕ → ℝ
  good : ℕ → Set Omega
  r : ℕ → ℕ
  failGood : ℕ → ℝ≥0∞
  failOverlap : ℕ → ℝ≥0∞
  beta : ℕ → ℝ
  tailUpper : ℕ → ℝ
  pairUpper : ℕ → ℝ
  countMean : ℕ → ℝ
  countRawSecond : ℕ → ℝ
  V : ℕ → ℝ
  flat : ℕ → ℝ
  rho : ℕ → ℝ
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  variance_floor :
    ∀ omega j N, omega ∈ good j → N ∈ testSet j →
      V j ≤ trackBLinearPrimeVariance freshSet coeff omega j N
  coeff_flat :
    ∀ omega j N p, omega ∈ good j → N ∈ testSet j →
      p ∈ freshSet j N → |coeff omega j N p| ≤ flat j
  covariance_bound :
    ∀ omega j N N', omega ∈ good j → N ∈ testSet j → N' ∈ testSet j →
      N ≠ N' →
        |trackBLinearPrimeCovariance freshSet coeff omega j N N'|
          ≤ rho j * V j
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  exceedance_measurable :
    ∀ j N, MeasurableSet
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeCore freshSet coeff good) M buffer j N)
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
        mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeCore freshSet coeff good) M buffer j N)
  tail_prob_le_tailUpper :
    ∀ (j N : ℕ), N ∈ testSet j →
      mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeCore freshSet coeff good) M buffer j N)
        ≤ tailUpper j
  offdiag_pair_prob_le_pairUpper :
    ∀ (j N N' : ℕ), N ∈ testSet j → N' ∈ testSet j → N ≠ N' →
      mu.real
          (trackBThresholdPairExceedanceEvent
            (trackBLinearPrimeCore freshSet coeff good) M buffer j N N')
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
          (trackBThresholdOverlapMany testSet
            (trackBLinearPrimeCore freshSet coeff good)
            (trackBLinearPrimeRemainder freshSet coeff good)
            M buffer r j) ≤
        failOverlap j

/-- Uniform linear fresh-prime tail packages specialize to the generic uniform
sparse threshold package. -/
noncomputable def trackBThresholdUniformTailProbabilityCertificate_of_linearPrime
    (h : TrackBLinearPrimeUniformTailProbabilityCertificate) :
    TrackBThresholdUniformTailProbabilityCertificate where
  lo := h.lo
  hi := h.hi
  M := h.M
  buffer := h.buffer
  testSet := h.testSet
  core := trackBLinearPrimeCore h.freshSet h.coeff h.good
  remainder := trackBLinearPrimeRemainder h.freshSet h.coeff h.good
  good := h.good
  r := h.r
  failGood := h.failGood
  failOverlap := h.failOverlap
  beta := h.beta
  tailUpper := h.tailUpper
  pairUpper := h.pairUpper
  countMean := h.countMean
  countRawSecond := h.countRawSecond
  r_pos := h.r_pos
  countMean_pos := h.countMean_pos
  r_le_half_countMean := h.r_le_half_countMean
  testSet_in_block := h.testSet_in_block
  absorb := by
    intro omega j N _hN hcore hrem
    exact
      normSum_ge_of_trackBLinearPrimeCore_ge_of_remainder_ge
        h.freshSet h.coeff h.good h.M h.buffer omega j N hcore hrem
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  exceedance_measurable := h.exceedance_measurable
  countMean_le_beta_sum := h.countMean_le_beta_sum
  pairBudget_le_countRawSecond := h.pairBudget_le_countRawSecond
  beta_le_tail_prob := h.beta_le_tail_prob
  tail_prob_le_tailUpper := h.tail_prob_le_tailUpper
  offdiag_pair_prob_le_pairUpper := h.offdiag_pair_prob_le_pairUpper
  fail_summable := h.fail_summable
  prob_good_compl := h.prob_good_compl
  prob_overlap_many := h.prob_overlap_many

/-- Direct closure from a uniform one-point/two-point tail package for the linear
fresh-prime core. -/
theorem erdos1144_of_trackBLinearPrimeUniformTailProbabilityCertificate
    (h : TrackBLinearPrimeUniformTailProbabilityCertificate) :
    Erdos1144 :=
  erdos1144_of_trackBThresholdUniformTailProbabilityCertificate
    (trackBThresholdUniformTailProbabilityCertificate_of_linearPrime h)

/-- Linear fresh-prime package using centered covariance errors for threshold
indicators.  This is the preferred final Track B API: the Gaussian comparison
feeds `beta`, `tailUpper`, and `pairCovUpper`, while the count variance is
controlled by the centered covariance adapter in
`HarperTrackBThresholdSparse`. -/
structure TrackBLinearPrimeCovarianceTailCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  freshSet : ℕ → ℕ → Finset ℕ
  coeff : Omega → ℕ → ℕ → ℕ → ℝ
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
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  variance_floor :
    ∀ omega j N, omega ∈ good j → N ∈ testSet j →
      V j ≤ trackBLinearPrimeVariance freshSet coeff omega j N
  coeff_flat :
    ∀ omega j N p, omega ∈ good j → N ∈ testSet j →
      p ∈ freshSet j N → |coeff omega j N p| ≤ flat j
  covariance_bound :
    ∀ omega j N N', omega ∈ good j → N ∈ testSet j → N' ∈ testSet j →
      N ≠ N' →
        |trackBLinearPrimeCovariance freshSet coeff omega j N N'|
          ≤ rho j * V j
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  exceedance_measurable :
    ∀ j N, MeasurableSet
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeCore freshSet coeff good) M buffer j N)
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
        mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeCore freshSet coeff good) M buffer j N)
  tail_prob_le_tailUpper :
    ∀ (j N : ℕ), N ∈ testSet j →
      mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeCore freshSet coeff good) M buffer j N)
        ≤ tailUpper j
  offdiag_pair_cov_le_pairCovUpper :
    ∀ (j N N' : ℕ), N ∈ testSet j → N' ∈ testSet j → N ≠ N' →
      mu.real
          (trackBThresholdPairExceedanceEvent
            (trackBLinearPrimeCore freshSet coeff good) M buffer j N N') -
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeCore freshSet coeff good) M buffer j N) *
            mu.real
              (trackBThresholdExceedanceEvent
                (trackBLinearPrimeCore freshSet coeff good) M buffer j N')
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
          (trackBThresholdOverlapMany testSet
            (trackBLinearPrimeCore freshSet coeff good)
            (trackBLinearPrimeRemainder freshSet coeff good)
            M buffer r j) ≤
        failOverlap j

/-- Linear fresh-prime covariance-tail packages specialize to the generic
centered covariance sparse threshold package. -/
noncomputable def trackBThresholdUniformCovarianceTailCertificate_of_linearPrime
    (h : TrackBLinearPrimeCovarianceTailCertificate) :
    TrackBThresholdUniformCovarianceTailCertificate where
  lo := h.lo
  hi := h.hi
  M := h.M
  buffer := h.buffer
  testSet := h.testSet
  core := trackBLinearPrimeCore h.freshSet h.coeff h.good
  remainder := trackBLinearPrimeRemainder h.freshSet h.coeff h.good
  good := h.good
  r := h.r
  failGood := h.failGood
  failOverlap := h.failOverlap
  beta := h.beta
  tailUpper := h.tailUpper
  pairCovUpper := h.pairCovUpper
  countMean := h.countMean
  countSecond := h.countSecond
  r_pos := h.r_pos
  countMean_pos := h.countMean_pos
  r_le_half_countMean := h.r_le_half_countMean
  testSet_in_block := h.testSet_in_block
  absorb := by
    intro omega j N _hN hcore hrem
    exact
      normSum_ge_of_trackBLinearPrimeCore_ge_of_remainder_ge
        h.freshSet h.coeff h.good h.M h.buffer omega j N hcore hrem
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  exceedance_measurable := h.exceedance_measurable
  countMean_le_beta_sum := h.countMean_le_beta_sum
  covarianceBudget_le_countSecond := h.covarianceBudget_le_countSecond
  beta_le_tail_prob := h.beta_le_tail_prob
  tail_prob_le_tailUpper := h.tail_prob_le_tailUpper
  offdiag_pair_cov_le_pairCovUpper := h.offdiag_pair_cov_le_pairCovUpper
  fail_summable := h.fail_summable
  prob_good_compl := h.prob_good_compl
  prob_overlap_many := h.prob_overlap_many

/-- Direct closure from the preferred centered covariance-tail package for the
linear fresh-prime core. -/
theorem erdos1144_of_trackBLinearPrimeCovarianceTailCertificate
    (h : TrackBLinearPrimeCovarianceTailCertificate) :
    Erdos1144 :=
  erdos1144_of_trackBThresholdUniformCovarianceTailCertificate
    (trackBThresholdUniformCovarianceTailCertificate_of_linearPrime h)

/-- Linear fresh-prime package in the Gaussian-comparison form isolated by the
Track B proof audit.  The Gaussian one-point and pair calculations are kept as
finite deterministic fields (`gaussianTail`, `gaussianPair`, and covariance
slacks); the only remaining probabilistic comparison input is the explicit
one-point and two-point transfer from the Rademacher core to those Gaussian
quantities.

This structure is intentionally one step above
`TrackBLinearPrimeCovarianceTailCertificate`: it records the proof collection's
bookkeeping that

```text
actual pair covariance
  <= Gaussian pair covariance + two-point comparison slack + product slack.
```
-/
structure TrackBLinearPrimeGaussianComparisonCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  freshSet : ℕ → ℕ → Finset ℕ
  coeff : Omega → ℕ → ℕ → ℕ → ℝ
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
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  variance_floor :
    ∀ omega j N, omega ∈ good j → N ∈ testSet j →
      V j ≤ trackBLinearPrimeVariance freshSet coeff omega j N
  coeff_flat :
    ∀ omega j N p, omega ∈ good j → N ∈ testSet j →
      p ∈ freshSet j N → |coeff omega j N p| ≤ flat j
  covariance_bound :
    ∀ omega j N N', omega ∈ good j → N ∈ testSet j → N' ∈ testSet j →
      N ≠ N' →
        |trackBLinearPrimeCovariance freshSet coeff omega j N N'|
          ≤ rho j * V j
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  exceedance_measurable :
    ∀ j N, MeasurableSet
      (trackBThresholdExceedanceEvent
        (trackBLinearPrimeCore freshSet coeff good) M buffer j N)
  countMean_le_beta_sum :
    ∀ j,
      countMean j ≤
        ∑ _N ∈ testSet j, beta j
  covarianceBudget_le_countSecond :
    ∀ j,
      (∑ N ∈ testSet j, ∑ N' ∈ testSet j,
        if N = N' then tailUpper j else pairCovUpper j)
        ≤ countSecond j
  gaussian_one_point_lower :
    ∀ j N, N ∈ testSet j →
      beta j + onePointSlack j ≤ gaussianTail j N
  one_point_compare_lower :
    ∀ j N, N ∈ testSet j →
      gaussianTail j N - onePointSlack j ≤
        mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeCore freshSet coeff good) M buffer j N)
  tail_prob_le_tailUpper :
    ∀ (j N : ℕ), N ∈ testSet j →
      mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeCore freshSet coeff good) M buffer j N)
        ≤ tailUpper j
  pair_compare_upper :
    ∀ (j N N' : ℕ), N ∈ testSet j → N' ∈ testSet j → N ≠ N' →
      mu.real
          (trackBThresholdPairExceedanceEvent
            (trackBLinearPrimeCore freshSet coeff good) M buffer j N N')
        ≤ gaussianPair j N N' + twoPointSlack j
  gaussian_pair_cov_upper :
    ∀ (j N N' : ℕ), N ∈ testSet j → N' ∈ testSet j → N ≠ N' →
      gaussianPair j N N' -
          gaussianTail j N * gaussianTail j N'
        ≤ gaussianPairCovUpper j
  tail_product_compare_lower :
    ∀ (j N N' : ℕ), N ∈ testSet j → N' ∈ testSet j → N ≠ N' →
      gaussianTail j N * gaussianTail j N'
        ≤
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeCore freshSet coeff good) M buffer j N) *
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeCore freshSet coeff good) M buffer j N') +
            productSlack j
  pairCovBudget_le_pairCovUpper :
    ∀ j,
      gaussianPairCovUpper j + twoPointSlack j + productSlack j
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
          (trackBThresholdOverlapMany testSet
            (trackBLinearPrimeCore freshSet coeff good)
            (trackBLinearPrimeRemainder freshSet coeff good)
            M buffer r j) ≤
        failOverlap j

/-- The Gaussian-comparison package supplies the centered covariance-tail
certificate used by the final Track B linear-prime route. -/
noncomputable def trackBLinearPrimeCovarianceTailCertificate_of_gaussianComparison
    (h : TrackBLinearPrimeGaussianComparisonCertificate) :
    TrackBLinearPrimeCovarianceTailCertificate where
  lo := h.lo
  hi := h.hi
  M := h.M
  buffer := h.buffer
  testSet := h.testSet
  freshSet := h.freshSet
  coeff := h.coeff
  good := h.good
  r := h.r
  failGood := h.failGood
  failOverlap := h.failOverlap
  beta := h.beta
  tailUpper := h.tailUpper
  pairCovUpper := h.pairCovUpper
  countMean := h.countMean
  countSecond := h.countSecond
  V := h.V
  flat := h.flat
  rho := h.rho
  r_pos := h.r_pos
  countMean_pos := h.countMean_pos
  r_le_half_countMean := h.r_le_half_countMean
  testSet_in_block := h.testSet_in_block
  variance_floor := h.variance_floor
  coeff_flat := h.coeff_flat
  covariance_bound := h.covariance_bound
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  exceedance_measurable := h.exceedance_measurable
  countMean_le_beta_sum := h.countMean_le_beta_sum
  covarianceBudget_le_countSecond := h.covarianceBudget_le_countSecond
  beta_le_tail_prob := by
    intro j N hN
    have hgauss := h.gaussian_one_point_lower j N hN
    have hcomp := h.one_point_compare_lower j N hN
    linarith
  tail_prob_le_tailUpper := h.tail_prob_le_tailUpper
  offdiag_pair_cov_le_pairCovUpper := by
    intro j N N' hN hN' hne
    set actualPair : ℝ :=
      mu.real
        (trackBThresholdPairExceedanceEvent
          (trackBLinearPrimeCore h.freshSet h.coeff h.good)
          h.M h.buffer j N N')
    set actualTail : ℝ :=
      mu.real
        (trackBThresholdExceedanceEvent
          (trackBLinearPrimeCore h.freshSet h.coeff h.good)
          h.M h.buffer j N)
    set actualTail' : ℝ :=
      mu.real
        (trackBThresholdExceedanceEvent
          (trackBLinearPrimeCore h.freshSet h.coeff h.good)
          h.M h.buffer j N')
    set gaussPair : ℝ := h.gaussianPair j N N'
    set gaussTail : ℝ := h.gaussianTail j N
    set gaussTail' : ℝ := h.gaussianTail j N'
    have hpair :
        actualPair ≤ gaussPair + h.twoPointSlack j := by
      simpa [actualPair, gaussPair] using
        h.pair_compare_upper j N N' hN hN' hne
    have hgauss :
        gaussPair - gaussTail * gaussTail' ≤
          h.gaussianPairCovUpper j := by
      simpa [gaussPair, gaussTail, gaussTail'] using
        h.gaussian_pair_cov_upper j N N' hN hN' hne
    have hprod :
        gaussTail * gaussTail' ≤
          actualTail * actualTail' + h.productSlack j := by
      simpa [gaussTail, gaussTail', actualTail, actualTail'] using
        h.tail_product_compare_lower j N N' hN hN' hne
    have hbudget :
        h.gaussianPairCovUpper j + h.twoPointSlack j +
            h.productSlack j ≤ h.pairCovUpper j :=
      h.pairCovBudget_le_pairCovUpper j
    linarith
  fail_summable := h.fail_summable
  prob_good_compl := h.prob_good_compl
  prob_overlap_many := h.prob_overlap_many

/-- Direct closure from the proof-audit Gaussian-comparison package for the
linear fresh-prime core. -/
theorem erdos1144_of_trackBLinearPrimeGaussianComparisonCertificate
    (h : TrackBLinearPrimeGaussianComparisonCertificate) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeCovarianceTailCertificate
    (trackBLinearPrimeCovarianceTailCertificate_of_gaussianComparison h)

/-!
## Scheduled Gaussian-comparison package

This is the final Lean-facing shape expected from the fresh-prime Track B
analysis.  It replaces the generic `testSet` and `freshSet` fields by an
explicit sparse mesh `point j r` and prime intervals `[freshLo j r, freshHi j r]`.
The converter below unfolds those scheduled objects into the already-proved
generic Gaussian-comparison certificate.
-/

structure TrackBLinearPrimeScheduledGaussianComparisonCertificate where
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
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  testSet_in_block :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet Q point j → N ∈ Finset.Icc (lo j) (hi j)
  variance_floor :
    ∀ omega j N, omega ∈ good j → N ∈ trackBLinearPrimeMeshTestSet Q point j →
      V j ≤ trackBLinearPrimeScheduledVariance Q point freshLo freshHi omega j N
  coeff_flat :
    ∀ omega j N p, omega ∈ good j → N ∈ trackBLinearPrimeMeshTestSet Q point j →
      p ∈ trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N →
        |trackBLinearPrimeScheduledFreshCoeff Q point freshLo freshHi omega j N p|
          ≤ flat j
  covariance_bound :
    ∀ omega j N N',
      omega ∈ good j → N ∈ trackBLinearPrimeMeshTestSet Q point j →
        N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
          (|trackBLinearPrimeScheduledCovariance Q point freshLo freshHi omega j N N'|
            ≤ rho j * V j)
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  good_measurable : ∀ j, MeasurableSet (good j)
  countMean_le_beta_sum :
    ∀ j,
      countMean j ≤
        ∑ _N ∈ trackBLinearPrimeMeshTestSet Q point j, beta j
  covarianceBudget_le_countSecond :
    ∀ j,
      (∑ N ∈ trackBLinearPrimeMeshTestSet Q point j,
        ∑ N' ∈ trackBLinearPrimeMeshTestSet Q point j,
          if N = N' then tailUpper j else pairCovUpper j)
        ≤ countSecond j
  gaussian_one_point_lower :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet Q point j →
      beta j + onePointSlack j ≤ gaussianTail j N
  one_point_compare_lower :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet Q point j →
      gaussianTail j N - onePointSlack j ≤
        mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
            M buffer j N)
  tail_prob_le_tailUpper :
    ∀ (j N : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
      mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
            M buffer j N)
        ≤ tailUpper j
  pair_compare_upper :
    ∀ (j N N' : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
      N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
        mu.real
            (trackBThresholdPairExceedanceEvent
              (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
              M buffer j N N')
          ≤ gaussianPair j N N' + twoPointSlack j
  gaussian_pair_cov_upper :
    ∀ (j N N' : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
      N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
        gaussianPair j N N' - gaussianTail j N * gaussianTail j N'
          ≤ gaussianPairCovUpper j
  tail_product_compare_lower :
    ∀ (j N N' : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
      N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
        gaussianTail j N * gaussianTail j N'
          ≤
            mu.real
              (trackBThresholdExceedanceEvent
                (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
                M buffer j N) *
            mu.real
              (trackBThresholdExceedanceEvent
                (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
                M buffer j N') +
              productSlack j
  pairCovBudget_le_pairCovUpper :
    ∀ j,
      gaussianPairCovUpper j + twoPointSlack j + productSlack j
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
          (trackBThresholdOverlapMany
            (trackBLinearPrimeMeshTestSet Q point)
            (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
            (trackBLinearPrimeScheduledRemainder Q point freshLo freshHi good)
            M buffer r j) ≤
        failOverlap j

/-- Stage-level deterministic and summability data for the scheduled
linear-prime package. -/
structure TrackBLinearPrimeScheduledStageCertificate
    (lo hi Q : ℕ → ℕ) (point : ℕ → ℕ → ℕ) (M : ℕ → ℝ)
    (r : ℕ → ℕ) (failGood failOverlap : ℕ → ℝ≥0∞)
    (countMean countSecond : ℕ → ℝ) where
  r_pos : ∀ j, 0 < r j
  countMean_pos : ∀ j, 0 < countMean j
  r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2
  testSet_in_block :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet Q point j → N ∈ Finset.Icc (lo j) (hi j)
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  fail_summable :
    (∑' j,
      (failGood j +
        ENNReal.ofReal (4 * countSecond j / countMean j ^ 2) +
        failOverlap j)) ≠ ⊤

/-- Build the scheduled stage certificate from pointwise mesh facts.  The
only mesh-specific fields are strict growth of the scheduled points and
membership of each scheduled point in the stage block. -/
noncomputable def trackBLinearPrimeScheduledStageCertificate_of_pointwise
    {lo hi Q : ℕ → ℕ} {point : ℕ → ℕ → ℕ} {M : ℕ → ℝ}
    {r : ℕ → ℕ} {failGood failOverlap : ℕ → ℝ≥0∞}
    {countMean countSecond : ℕ → ℝ}
    (r_pos : ∀ j, 0 < r j)
    (countMean_pos : ∀ j, 0 < countMean j)
    (r_le_half_countMean : ∀ j, (r j : ℝ) ≤ countMean j / 2)
    (point_in_block :
      ∀ j r, r ∈ trackBLinearPrimeMeshIndexSet Q j →
        point j r ∈ Finset.Icc (lo j) (hi j))
    (lo_tendsto_atTop : Tendsto lo atTop atTop)
    (M_tendsto_atTop : Tendsto M atTop atTop)
    (fail_summable :
      (∑' j,
        (failGood j +
          ENNReal.ofReal (4 * countSecond j / countMean j ^ 2) +
          failOverlap j)) ≠ ⊤) :
    TrackBLinearPrimeScheduledStageCertificate
      lo hi Q point M r failGood failOverlap countMean countSecond where
  r_pos := r_pos
  countMean_pos := countMean_pos
  r_le_half_countMean := r_le_half_countMean
  testSet_in_block := fun j =>
    trackBLinearPrimeMeshTestSet_in_block_of_point_in_block lo hi Q point j
      (point_in_block j)
  lo_tendsto_atTop := lo_tendsto_atTop
  M_tendsto_atTop := M_tendsto_atTop
  fail_summable := fail_summable

/-- Good-event measurability and failure probability for the scheduled
linear-prime package. -/
structure TrackBLinearPrimeScheduledGoodEventCertificate
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) where
  good_measurable : ∀ j, MeasurableSet (good j)
  prob_good_compl : ∀ j, mu (good j)ᶜ ≤ failGood j

/-- Trivial good-event certificate for the all-space good event.  This is
useful when the analytic package has no separate exceptional small-prime event
and pays all failures through the tail/remainder fields. -/
noncomputable def trackBLinearPrimeScheduledGoodEventCertificate_univ :
    TrackBLinearPrimeScheduledGoodEventCertificate
      (fun _j => Set.univ) (fun _j => 0) where
  good_measurable := fun _j => MeasurableSet.univ
  prob_good_compl := by
    intro j
    simp

/-- Coefficient-geometry inputs for the scheduled fresh-prime core. -/
structure TrackBLinearPrimeScheduledGeometryCertificate
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (V flat rho : ℕ → ℝ) where
  variance_floor :
    ∀ omega j N, omega ∈ good j → N ∈ trackBLinearPrimeMeshTestSet Q point j →
      V j ≤ trackBLinearPrimeScheduledVariance Q point freshLo freshHi omega j N
  coeff_flat :
    ∀ omega j N p, omega ∈ good j → N ∈ trackBLinearPrimeMeshTestSet Q point j →
      p ∈ trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N →
        |trackBLinearPrimeScheduledFreshCoeff Q point freshLo freshHi omega j N p|
          ≤ flat j
  covariance_bound :
    ∀ omega j N N',
      omega ∈ good j → N ∈ trackBLinearPrimeMeshTestSet Q point j →
        N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
          |trackBLinearPrimeScheduledCovariance Q point freshLo freshHi omega j N N'|
            ≤ rho j * V j

/-- If scheduled fresh-prime layers are disjoint, then the off-diagonal
covariance part of the geometry certificate is automatic. This is the preferred
deterministic route for the fresh-prime construction. -/
noncomputable def trackBLinearPrimeScheduledGeometryCertificate_of_disjoint
    {Q : ℕ → ℕ} {point freshLo freshHi : ℕ → ℕ → ℕ}
    {good : ℕ → Set Omega} {V flat rho : ℕ → ℝ}
    (variance_floor :
      ∀ omega j N, omega ∈ good j → N ∈ trackBLinearPrimeMeshTestSet Q point j →
        V j ≤ trackBLinearPrimeScheduledVariance Q point freshLo freshHi omega j N)
    (coeff_flat :
      ∀ omega j N p, omega ∈ good j → N ∈ trackBLinearPrimeMeshTestSet Q point j →
        p ∈ trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N →
          |trackBLinearPrimeScheduledFreshCoeff Q point freshLo freshHi omega j N p|
            ≤ flat j)
    (fresh_disjoint :
      ∀ j N N', N ∈ trackBLinearPrimeMeshTestSet Q point j →
        N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
          Disjoint
            (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N)
            (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N'))
    (budget_nonneg : ∀ j, 0 ≤ rho j * V j) :
    TrackBLinearPrimeScheduledGeometryCertificate Q point freshLo freshHi good V flat rho where
  variance_floor := variance_floor
  coeff_flat := coeff_flat
  covariance_bound := by
    intro omega j N N' _hgood hN hN' hne
    exact
      trackBLinearPrimeScheduledCovariance_abs_le_of_disjoint
        Q point freshLo freshHi omega j N N' rho V
        (fresh_disjoint j N N' hN hN' hne)
        (budget_nonneg j)

/-- Interval separation of the scheduled prime layers is enough to supply the
off-diagonal covariance field of the geometry certificate. -/
noncomputable def trackBLinearPrimeScheduledGeometryCertificate_of_interval_disjoint
    {Q : ℕ → ℕ} {point freshLo freshHi : ℕ → ℕ → ℕ}
    {good : ℕ → Set Omega} {V flat rho : ℕ → ℝ}
    (variance_floor :
      ∀ omega j N, omega ∈ good j → N ∈ trackBLinearPrimeMeshTestSet Q point j →
        V j ≤ trackBLinearPrimeScheduledVariance Q point freshLo freshHi omega j N)
    (coeff_flat :
      ∀ omega j N p, omega ∈ good j → N ∈ trackBLinearPrimeMeshTestSet Q point j →
        p ∈ trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N →
          |trackBLinearPrimeScheduledFreshCoeff Q point freshLo freshHi omega j N p|
            ≤ flat j)
    (fresh_interval_disjoint :
      ∀ j r s, r ∈ trackBLinearPrimeMeshIndexSet Q j →
        s ∈ trackBLinearPrimeMeshIndexSet Q j → r ≠ s →
          freshHi j r < freshLo j s ∨ freshHi j s < freshLo j r)
    (budget_nonneg : ∀ j, 0 ≤ rho j * V j) :
    TrackBLinearPrimeScheduledGeometryCertificate Q point freshLo freshHi good V flat rho :=
  trackBLinearPrimeScheduledGeometryCertificate_of_disjoint
    variance_floor coeff_flat
    (fun j _N _N' hN hN' hne =>
      trackBLinearPrimeScheduledFreshSet_disjoint_of_interval_disjoint
        hN hN' hne (fresh_interval_disjoint j))
    budget_nonneg

/-- Scheduled geometry constructor where coefficient flatness is supplied as a
deterministic reciprocal-square-root support bound.  This is the expected shape
for the fresh-prime analytic estimates: random signs are removed by
`abs_trackBSquarefreeFreshCoeff_le_reciprocal_sum`. -/
noncomputable def trackBLinearPrimeScheduledGeometryCertificate_of_interval_disjoint_and_reciprocal
    {Q : ℕ → ℕ} {point freshLo freshHi : ℕ → ℕ → ℕ}
    {good : ℕ → Set Omega} {V flat rho : ℕ → ℝ}
    (variance_floor :
      ∀ omega j N, omega ∈ good j → N ∈ trackBLinearPrimeMeshTestSet Q point j →
        V j ≤ trackBLinearPrimeScheduledVariance Q point freshLo freshHi omega j N)
    (coeff_reciprocal_bound :
      ∀ j N p, N ∈ trackBLinearPrimeMeshTestSet Q point j →
        p ∈ trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N →
          (∑ m ∈
            trackBSquarefreeFreshCoeffSupport
              (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N) N p,
              (Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ≤ flat j)
    (fresh_interval_disjoint :
      ∀ j r s, r ∈ trackBLinearPrimeMeshIndexSet Q j →
        s ∈ trackBLinearPrimeMeshIndexSet Q j → r ≠ s →
          freshHi j r < freshLo j s ∨ freshHi j s < freshLo j r)
    (budget_nonneg : ∀ j, 0 ≤ rho j * V j) :
    TrackBLinearPrimeScheduledGeometryCertificate Q point freshLo freshHi good V flat rho :=
  trackBLinearPrimeScheduledGeometryCertificate_of_interval_disjoint
    variance_floor
    (fun omega j N p _hgood hN hp => by
      unfold trackBLinearPrimeScheduledFreshCoeff trackBSquarefreeFreshLinearCoeff
      exact le_trans
        (abs_trackBSquarefreeFreshCoeff_le_reciprocal_sum
          (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N)
          omega N p)
        (coeff_reciprocal_bound j N p hN hp))
    fresh_interval_disjoint budget_nonneg

/-- Scheduled geometry constructor reducing flatness further to a support
cardinality bound.  Since supported `p` are prime, every term in the
reciprocal sum is at most `1 / sqrt p`. -/
noncomputable def trackBLinearPrimeScheduledGeometryCertificate_of_interval_disjoint_and_card
    {Q : ℕ → ℕ} {point freshLo freshHi : ℕ → ℕ → ℕ}
    {good : ℕ → Set Omega} {V flat rho : ℕ → ℝ}
    (variance_floor :
      ∀ omega j N, omega ∈ good j → N ∈ trackBLinearPrimeMeshTestSet Q point j →
        V j ≤ trackBLinearPrimeScheduledVariance Q point freshLo freshHi omega j N)
    (coeff_support_card_bound :
      ∀ j N p, N ∈ trackBLinearPrimeMeshTestSet Q point j →
        p ∈ trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N →
          ((trackBSquarefreeFreshCoeffSupport
              (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N) N p).card :
              ℝ) *
              (Real.sqrt ((p : ℕ) : ℝ))⁻¹ ≤ flat j)
    (fresh_interval_disjoint :
      ∀ j r s, r ∈ trackBLinearPrimeMeshIndexSet Q j →
        s ∈ trackBLinearPrimeMeshIndexSet Q j → r ≠ s →
          freshHi j r < freshLo j s ∨ freshHi j s < freshLo j r)
    (budget_nonneg : ∀ j, 0 ≤ rho j * V j) :
    TrackBLinearPrimeScheduledGeometryCertificate Q point freshLo freshHi good V flat rho :=
  trackBLinearPrimeScheduledGeometryCertificate_of_interval_disjoint_and_reciprocal
    variance_floor
    (fun j N p hN hp => by
      exact le_trans
        (trackBSquarefreeFreshCoeff_reciprocal_sum_le_card_mul_inv_sqrt
          (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N) N p
          (trackBLinearPrimeScheduledFreshSet_prime hp).pos)
        (coeff_support_card_bound j N p hN hp))
    fresh_interval_disjoint budget_nonneg

/-- Scheduled geometry constructor reducing flatness to the very crude
divisor-scale estimate `(N / p) / sqrt p <= flat_j`. -/
noncomputable def trackBLinearPrimeScheduledGeometryCertificate_of_interval_disjoint_and_div
    {Q : ℕ → ℕ} {point freshLo freshHi : ℕ → ℕ → ℕ}
    {good : ℕ → Set Omega} {V flat rho : ℕ → ℝ}
    (variance_floor :
      ∀ omega j N, omega ∈ good j → N ∈ trackBLinearPrimeMeshTestSet Q point j →
        V j ≤ trackBLinearPrimeScheduledVariance Q point freshLo freshHi omega j N)
    (coeff_div_bound :
      ∀ j N p, N ∈ trackBLinearPrimeMeshTestSet Q point j →
        p ∈ trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N →
          ((N / p : ℕ) : ℝ) * (Real.sqrt ((p : ℕ) : ℝ))⁻¹ ≤ flat j)
    (fresh_interval_disjoint :
      ∀ j r s, r ∈ trackBLinearPrimeMeshIndexSet Q j →
        s ∈ trackBLinearPrimeMeshIndexSet Q j → r ≠ s →
          freshHi j r < freshLo j s ∨ freshHi j s < freshLo j r)
    (budget_nonneg : ∀ j, 0 ≤ rho j * V j) :
    TrackBLinearPrimeScheduledGeometryCertificate Q point freshLo freshHi good V flat rho :=
  trackBLinearPrimeScheduledGeometryCertificate_of_interval_disjoint_and_card
    variance_floor
    (fun j N p hN hp => by
      exact le_trans
        (trackBSquarefreeFreshCoeff_card_mul_inv_sqrt_le_div_mul_inv_sqrt
          (trackBLinearPrimeScheduledFreshSet Q point freshLo freshHi j N) N p)
        (coeff_div_bound j N p hN hp))
    fresh_interval_disjoint budget_nonneg

/-- One- and two-point Gaussian comparison and threshold-count budgets for the
scheduled fresh-prime core. -/
structure TrackBLinearPrimeScheduledGaussianTailCertificate
    (Q : ℕ → ℕ) (point freshLo freshHi : ℕ → ℕ → ℕ)
    (good : ℕ → Set Omega) (M buffer : ℕ → ℝ)
    (beta tailUpper pairCovUpper countMean countSecond : ℕ → ℝ)
    (gaussianTail : ℕ → ℕ → ℝ) (gaussianPair : ℕ → ℕ → ℕ → ℝ)
    (onePointSlack twoPointSlack productSlack gaussianPairCovUpper : ℕ → ℝ) where
  countMean_le_beta_sum :
    ∀ j,
      countMean j ≤
        ∑ _N ∈ trackBLinearPrimeMeshTestSet Q point j, beta j
  covarianceBudget_le_countSecond :
    ∀ j,
      (∑ N ∈ trackBLinearPrimeMeshTestSet Q point j,
        ∑ N' ∈ trackBLinearPrimeMeshTestSet Q point j,
          if N = N' then tailUpper j else pairCovUpper j)
        ≤ countSecond j
  gaussian_one_point_lower :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet Q point j →
      beta j + onePointSlack j ≤ gaussianTail j N
  one_point_compare_lower :
    ∀ j N, N ∈ trackBLinearPrimeMeshTestSet Q point j →
      gaussianTail j N - onePointSlack j ≤
        mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
            M buffer j N)
  tail_prob_le_tailUpper :
    ∀ (j N : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
      mu.real
          (trackBThresholdExceedanceEvent
            (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
            M buffer j N)
        ≤ tailUpper j
  pair_compare_upper :
    ∀ (j N N' : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
      N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
        mu.real
            (trackBThresholdPairExceedanceEvent
              (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
              M buffer j N N')
          ≤ gaussianPair j N N' + twoPointSlack j
  gaussian_pair_cov_upper :
    ∀ (j N N' : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
      N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
        gaussianPair j N N' - gaussianTail j N * gaussianTail j N'
          ≤ gaussianPairCovUpper j
  tail_product_compare_lower :
    ∀ (j N N' : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
      N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
        gaussianTail j N * gaussianTail j N'
          ≤
            mu.real
              (trackBThresholdExceedanceEvent
                (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
                M buffer j N) *
            mu.real
              (trackBThresholdExceedanceEvent
                (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
                M buffer j N') +
              productSlack j
  pairCovBudget_le_pairCovUpper :
    ∀ j,
      gaussianPairCovUpper j + twoPointSlack j + productSlack j
        ≤ pairCovUpper j

theorem trackBLinearPrimeScheduled_countMean_le_beta_sum_of_card
    (Q : ℕ → ℕ) (point : ℕ → ℕ → ℕ)
    (beta countMean : ℕ → ℝ)
    (j : ℕ)
    (hcard : (trackBLinearPrimeMeshTestSet Q point j).card = Q j)
    (hmean : countMean j ≤ (Q j : ℝ) * beta j) :
    countMean j ≤
      ∑ _N ∈ trackBLinearPrimeMeshTestSet Q point j, beta j := by
  rw [Finset.sum_const]
  simpa [hcard] using hmean

theorem trackBLinearPrimeScheduled_countMean_le_beta_sum_of_injOn
    (Q : ℕ → ℕ) (point : ℕ → ℕ → ℕ)
    (beta countMean : ℕ → ℝ)
    (j : ℕ)
    (hinj : Set.InjOn (point j) (trackBLinearPrimeMeshIndexSet Q j : Set ℕ))
    (hmean : countMean j ≤ (Q j : ℝ) * beta j) :
    countMean j ≤
      ∑ _N ∈ trackBLinearPrimeMeshTestSet Q point j, beta j :=
  trackBLinearPrimeScheduled_countMean_le_beta_sum_of_card
    Q point beta countMean j
    (trackBLinearPrimeMeshTestSet_card_of_injOn Q point j hinj)
    hmean

theorem trackBLinearPrimeScheduled_covarianceBudget_le_countSecond_of_card
    (Q : ℕ → ℕ) (point : ℕ → ℕ → ℕ)
    (tailUpper pairCovUpper countSecond : ℕ → ℝ)
    (j : ℕ)
    (hcard : (trackBLinearPrimeMeshTestSet Q point j).card = Q j)
    (_htail_nonneg : 0 ≤ tailUpper j)
    (hpair_nonneg : 0 ≤ pairCovUpper j)
    (hbudget :
      (Q j : ℝ) * tailUpper j + (Q j : ℝ) ^ 2 * pairCovUpper j ≤ countSecond j) :
    (∑ N ∈ trackBLinearPrimeMeshTestSet Q point j,
      ∑ N' ∈ trackBLinearPrimeMeshTestSet Q point j,
        if N = N' then tailUpper j else pairCovUpper j)
      ≤ countSecond j := by
  classical
  set s := trackBLinearPrimeMeshTestSet Q point j with hs_def
  have hcardR : (s.card : ℝ) = (Q j : ℝ) := by
    rw [hs_def]; exact_mod_cast hcard
  have hterm : ∀ N N' : ℕ,
      (if N = N' then tailUpper j else pairCovUpper j)
        ≤ (if N = N' then tailUpper j else (0 : ℝ)) + pairCovUpper j := by
    intro N N'
    by_cases h : N = N'
    · simp [h, hpair_nonneg]
    · simp [h]
  have hinner : ∀ N : ℕ, N ∈ s →
      (∑ N' ∈ s, if N = N' then tailUpper j else pairCovUpper j)
        ≤ tailUpper j + (s.card : ℝ) * pairCovUpper j := by
    intro N hN
    calc
      (∑ N' ∈ s, if N = N' then tailUpper j else pairCovUpper j)
          ≤ ∑ N' ∈ s,
              ((if N = N' then tailUpper j else (0 : ℝ)) + pairCovUpper j) :=
            Finset.sum_le_sum (fun N' _ => hterm N N')
      _ = (∑ N' ∈ s, if N = N' then tailUpper j else (0 : ℝ)) +
            ∑ _N' ∈ s, pairCovUpper j := by
            rw [Finset.sum_add_distrib]
      _ = tailUpper j + (s.card : ℝ) * pairCovUpper j := by
            have hdiag :
                (∑ N' ∈ s, if N = N' then tailUpper j else (0 : ℝ)) =
                  tailUpper j := by
              rw [show
                (∑ N' ∈ s, if N = N' then tailUpper j else (0 : ℝ)) =
                  ∑ N' ∈ s, if N' = N then tailUpper j else (0 : ℝ) by
                refine Finset.sum_congr rfl ?_
                intro N' _hN'
                by_cases h : N = N'
                · simp [h]
                · simp [h, eq_comm]]
              rw [Finset.sum_ite_eq' s N (fun _ => tailUpper j), if_pos hN]
            rw [hdiag, Finset.sum_const, nsmul_eq_mul]
  calc
    (∑ N ∈ s, ∑ N' ∈ s, if N = N' then tailUpper j else pairCovUpper j)
        ≤ ∑ _N ∈ s, (tailUpper j + (s.card : ℝ) * pairCovUpper j) :=
          Finset.sum_le_sum (fun N hN => hinner N hN)
    _ = (s.card : ℝ) * tailUpper j + (s.card : ℝ) ^ 2 * pairCovUpper j := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ = (Q j : ℝ) * tailUpper j + (Q j : ℝ) ^ 2 * pairCovUpper j := by
          rw [hcardR]
    _ ≤ countSecond j := hbudget

theorem trackBLinearPrimeScheduled_covarianceBudget_le_countSecond_of_injOn
    (Q : ℕ → ℕ) (point : ℕ → ℕ → ℕ)
    (tailUpper pairCovUpper countSecond : ℕ → ℝ)
    (j : ℕ)
    (hinj : Set.InjOn (point j) (trackBLinearPrimeMeshIndexSet Q j : Set ℕ))
    (htail_nonneg : 0 ≤ tailUpper j)
    (hpair_nonneg : 0 ≤ pairCovUpper j)
    (hbudget :
      (Q j : ℝ) * tailUpper j + (Q j : ℝ) ^ 2 * pairCovUpper j ≤ countSecond j) :
    (∑ N ∈ trackBLinearPrimeMeshTestSet Q point j,
      ∑ N' ∈ trackBLinearPrimeMeshTestSet Q point j,
        if N = N' then tailUpper j else pairCovUpper j)
      ≤ countSecond j :=
  trackBLinearPrimeScheduled_covarianceBudget_le_countSecond_of_card
    Q point tailUpper pairCovUpper countSecond j
    (trackBLinearPrimeMeshTestSet_card_of_injOn Q point j hinj)
    htail_nonneg hpair_nonneg hbudget

/-- Build the scheduled Gaussian-tail certificate from the scalar count
budgets that are normally produced by the analytic estimates.  Injectivity of
the mesh converts the finite sums over the test set into the simple factors
`Q j` and `(Q j)^2`. -/
noncomputable def trackBLinearPrimeScheduledGaussianTailCertificate_of_injOn
    {Q : ℕ → ℕ} {point freshLo freshHi : ℕ → ℕ → ℕ}
    {good : ℕ → Set Omega} {M buffer : ℕ → ℝ}
    {beta tailUpper pairCovUpper countMean countSecond : ℕ → ℝ}
    {gaussianTail : ℕ → ℕ → ℝ} {gaussianPair : ℕ → ℕ → ℕ → ℝ}
    {onePointSlack twoPointSlack productSlack gaussianPairCovUpper : ℕ → ℝ}
    (mesh_inj :
      ∀ j, Set.InjOn (point j) (trackBLinearPrimeMeshIndexSet Q j : Set ℕ))
    (countMean_le_Q_beta : ∀ j, countMean j ≤ (Q j : ℝ) * beta j)
    (tailUpper_nonneg : ∀ j, 0 ≤ tailUpper j)
    (pairCovUpper_nonneg : ∀ j, 0 ≤ pairCovUpper j)
    (countSecond_budget :
      ∀ j,
        (Q j : ℝ) * tailUpper j + (Q j : ℝ) ^ 2 * pairCovUpper j ≤ countSecond j)
    (gaussian_one_point_lower :
      ∀ j N, N ∈ trackBLinearPrimeMeshTestSet Q point j →
        beta j + onePointSlack j ≤ gaussianTail j N)
    (one_point_compare_lower :
      ∀ j N, N ∈ trackBLinearPrimeMeshTestSet Q point j →
        gaussianTail j N - onePointSlack j ≤
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
              M buffer j N))
    (tail_prob_le_tailUpper :
      ∀ (j N : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
        mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
              M buffer j N)
          ≤ tailUpper j)
    (pair_compare_upper :
      ∀ (j N N' : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
        N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
          mu.real
              (trackBThresholdPairExceedanceEvent
                (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
                M buffer j N N')
            ≤ gaussianPair j N N' + twoPointSlack j)
    (gaussian_pair_cov_upper :
      ∀ (j N N' : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
        N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
          gaussianPair j N N' - gaussianTail j N * gaussianTail j N'
            ≤ gaussianPairCovUpper j)
    (tail_product_compare_lower :
      ∀ (j N N' : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
        N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
          gaussianTail j N * gaussianTail j N'
            ≤
              mu.real
                (trackBThresholdExceedanceEvent
                  (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
                  M buffer j N) *
              mu.real
                (trackBThresholdExceedanceEvent
                  (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
                  M buffer j N') +
                productSlack j)
    (pairCovBudget_le_pairCovUpper :
      ∀ j,
        gaussianPairCovUpper j + twoPointSlack j + productSlack j
          ≤ pairCovUpper j) :
    TrackBLinearPrimeScheduledGaussianTailCertificate
      Q point freshLo freshHi good M buffer beta tailUpper pairCovUpper
      countMean countSecond gaussianTail gaussianPair onePointSlack
      twoPointSlack productSlack gaussianPairCovUpper where
  countMean_le_beta_sum := by
    intro j
    exact
      trackBLinearPrimeScheduled_countMean_le_beta_sum_of_injOn
        Q point beta countMean j (mesh_inj j) (countMean_le_Q_beta j)
  covarianceBudget_le_countSecond := by
    intro j
    exact
      trackBLinearPrimeScheduled_covarianceBudget_le_countSecond_of_injOn
        Q point tailUpper pairCovUpper countSecond j (mesh_inj j)
        (tailUpper_nonneg j) (pairCovUpper_nonneg j)
        (countSecond_budget j)
  gaussian_one_point_lower := gaussian_one_point_lower
  one_point_compare_lower := one_point_compare_lower
  tail_prob_le_tailUpper := tail_prob_le_tailUpper
  pair_compare_upper := pair_compare_upper
  gaussian_pair_cov_upper := gaussian_pair_cov_upper
  tail_product_compare_lower := tail_product_compare_lower
  pairCovBudget_le_pairCovUpper := pairCovBudget_le_pairCovUpper

/-- Variant of
`trackBLinearPrimeScheduledGaussianTailCertificate_of_injOn` where mesh
injectivity is obtained from strict growth of the scheduled points. -/
noncomputable def trackBLinearPrimeScheduledGaussianTailCertificate_of_strict
    {Q : ℕ → ℕ} {point freshLo freshHi : ℕ → ℕ → ℕ}
    {good : ℕ → Set Omega} {M buffer : ℕ → ℝ}
    {beta tailUpper pairCovUpper countMean countSecond : ℕ → ℝ}
    {gaussianTail : ℕ → ℕ → ℝ} {gaussianPair : ℕ → ℕ → ℕ → ℝ}
    {onePointSlack twoPointSlack productSlack gaussianPairCovUpper : ℕ → ℝ}
    (point_strict :
      ∀ j ⦃r s⦄, r ∈ trackBLinearPrimeMeshIndexSet Q j →
        s ∈ trackBLinearPrimeMeshIndexSet Q j → r < s → point j r < point j s)
    (countMean_le_Q_beta : ∀ j, countMean j ≤ (Q j : ℝ) * beta j)
    (tailUpper_nonneg : ∀ j, 0 ≤ tailUpper j)
    (pairCovUpper_nonneg : ∀ j, 0 ≤ pairCovUpper j)
    (countSecond_budget :
      ∀ j,
        (Q j : ℝ) * tailUpper j + (Q j : ℝ) ^ 2 * pairCovUpper j ≤ countSecond j)
    (gaussian_one_point_lower :
      ∀ j N, N ∈ trackBLinearPrimeMeshTestSet Q point j →
        beta j + onePointSlack j ≤ gaussianTail j N)
    (one_point_compare_lower :
      ∀ j N, N ∈ trackBLinearPrimeMeshTestSet Q point j →
        gaussianTail j N - onePointSlack j ≤
          mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
              M buffer j N))
    (tail_prob_le_tailUpper :
      ∀ (j N : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
        mu.real
            (trackBThresholdExceedanceEvent
              (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
              M buffer j N)
          ≤ tailUpper j)
    (pair_compare_upper :
      ∀ (j N N' : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
        N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
          mu.real
              (trackBThresholdPairExceedanceEvent
                (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
                M buffer j N N')
            ≤ gaussianPair j N N' + twoPointSlack j)
    (gaussian_pair_cov_upper :
      ∀ (j N N' : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
        N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
          gaussianPair j N N' - gaussianTail j N * gaussianTail j N'
            ≤ gaussianPairCovUpper j)
    (tail_product_compare_lower :
      ∀ (j N N' : ℕ), N ∈ trackBLinearPrimeMeshTestSet Q point j →
        N' ∈ trackBLinearPrimeMeshTestSet Q point j → N ≠ N' →
          gaussianTail j N * gaussianTail j N'
            ≤
              mu.real
                (trackBThresholdExceedanceEvent
                  (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
                  M buffer j N) *
              mu.real
                (trackBThresholdExceedanceEvent
                  (trackBLinearPrimeScheduledCore Q point freshLo freshHi good)
                  M buffer j N') +
                productSlack j)
    (pairCovBudget_le_pairCovUpper :
      ∀ j,
        gaussianPairCovUpper j + twoPointSlack j + productSlack j
          ≤ pairCovUpper j) :
    TrackBLinearPrimeScheduledGaussianTailCertificate
      Q point freshLo freshHi good M buffer beta tailUpper pairCovUpper
      countMean countSecond gaussianTail gaussianPair onePointSlack
      twoPointSlack productSlack gaussianPairCovUpper :=
  trackBLinearPrimeScheduledGaussianTailCertificate_of_injOn
    (fun j => trackBLinearPrimeMesh_injOn_of_strict Q point j (point_strict j))
    countMean_le_Q_beta tailUpper_nonneg pairCovUpper_nonneg countSecond_budget
    gaussian_one_point_lower one_point_compare_lower tail_prob_le_tailUpper
    pair_compare_upper gaussian_pair_cov_upper tail_product_compare_lower
    pairCovBudget_le_pairCovUpper

/-- Assemble the scheduled Gaussian-comparison package from smaller named
certificates.  This is the intended final wiring point for the remaining
analytic work. -/
noncomputable def trackBLinearPrimeScheduledGaussianComparisonCertificate_of_parts
    {lo hi Q : ℕ → ℕ} {point freshLo freshHi : ℕ → ℕ → ℕ}
    {M buffer : ℕ → ℝ} {good : ℕ → Set Omega} {r : ℕ → ℕ}
    {failGood failOverlap : ℕ → ℝ≥0∞}
    {beta tailUpper pairCovUpper countMean countSecond V flat rho : ℕ → ℝ}
    {gaussianTail : ℕ → ℕ → ℝ} {gaussianPair : ℕ → ℕ → ℕ → ℝ}
    {onePointSlack twoPointSlack productSlack gaussianPairCovUpper : ℕ → ℝ}
    (stage :
      TrackBLinearPrimeScheduledStageCertificate
        lo hi Q point M r failGood failOverlap countMean countSecond)
    (goodCert : TrackBLinearPrimeScheduledGoodEventCertificate good failGood)
    (geom :
      TrackBLinearPrimeScheduledGeometryCertificate
        Q point freshLo freshHi good V flat rho)
    (tails :
      TrackBLinearPrimeScheduledGaussianTailCertificate
        Q point freshLo freshHi good M buffer beta tailUpper pairCovUpper
        countMean countSecond gaussianTail gaussianPair onePointSlack
        twoPointSlack productSlack gaussianPairCovUpper)
    (rem :
      TrackBLinearPrimeScheduledRemainderBadManyCertificate
        Q point freshLo freshHi good buffer r failOverlap) :
    TrackBLinearPrimeScheduledGaussianComparisonCertificate where
  lo := lo
  hi := hi
  M := M
  buffer := buffer
  Q := Q
  point := point
  freshLo := freshLo
  freshHi := freshHi
  good := good
  r := r
  failGood := failGood
  failOverlap := failOverlap
  beta := beta
  tailUpper := tailUpper
  pairCovUpper := pairCovUpper
  countMean := countMean
  countSecond := countSecond
  V := V
  flat := flat
  rho := rho
  gaussianTail := gaussianTail
  gaussianPair := gaussianPair
  onePointSlack := onePointSlack
  twoPointSlack := twoPointSlack
  productSlack := productSlack
  gaussianPairCovUpper := gaussianPairCovUpper
  r_pos := stage.r_pos
  countMean_pos := stage.countMean_pos
  r_le_half_countMean := stage.r_le_half_countMean
  testSet_in_block := stage.testSet_in_block
  variance_floor := geom.variance_floor
  coeff_flat := geom.coeff_flat
  covariance_bound := geom.covariance_bound
  lo_tendsto_atTop := stage.lo_tendsto_atTop
  M_tendsto_atTop := stage.M_tendsto_atTop
  good_measurable := goodCert.good_measurable
  countMean_le_beta_sum := tails.countMean_le_beta_sum
  covarianceBudget_le_countSecond := tails.covarianceBudget_le_countSecond
  gaussian_one_point_lower := tails.gaussian_one_point_lower
  one_point_compare_lower := tails.one_point_compare_lower
  tail_prob_le_tailUpper := tails.tail_prob_le_tailUpper
  pair_compare_upper := tails.pair_compare_upper
  gaussian_pair_cov_upper := tails.gaussian_pair_cov_upper
  tail_product_compare_lower := tails.tail_product_compare_lower
  pairCovBudget_le_pairCovUpper := tails.pairCovBudget_le_pairCovUpper
  fail_summable := stage.fail_summable
  prob_good_compl := goodCert.prob_good_compl
  prob_overlap_many :=
    prob_scheduledOverlapMany_le_of_remainderBadManyCertificate
      Q point freshLo freshHi good M buffer r failOverlap rem

/-- Scheduled Track B linear-prime inputs specialize to the generic
Gaussian-comparison certificate. -/
noncomputable def trackBLinearPrimeGaussianComparisonCertificate_of_scheduled
    (h : TrackBLinearPrimeScheduledGaussianComparisonCertificate) :
    TrackBLinearPrimeGaussianComparisonCertificate where
  lo := h.lo
  hi := h.hi
  M := h.M
  buffer := h.buffer
  testSet := trackBLinearPrimeMeshTestSet h.Q h.point
  freshSet := trackBLinearPrimeScheduledFreshSet h.Q h.point h.freshLo h.freshHi
  coeff := trackBLinearPrimeScheduledFreshCoeff h.Q h.point h.freshLo h.freshHi
  good := h.good
  r := h.r
  failGood := h.failGood
  failOverlap := h.failOverlap
  beta := h.beta
  tailUpper := h.tailUpper
  pairCovUpper := h.pairCovUpper
  countMean := h.countMean
  countSecond := h.countSecond
  V := h.V
  flat := h.flat
  rho := h.rho
  gaussianTail := h.gaussianTail
  gaussianPair := h.gaussianPair
  onePointSlack := h.onePointSlack
  twoPointSlack := h.twoPointSlack
  productSlack := h.productSlack
  gaussianPairCovUpper := h.gaussianPairCovUpper
  r_pos := h.r_pos
  countMean_pos := h.countMean_pos
  r_le_half_countMean := h.r_le_half_countMean
  testSet_in_block := h.testSet_in_block
  variance_floor := by
    intro omega j N hgood hN
    exact h.variance_floor omega j N hgood hN
  coeff_flat := by
    intro omega j N p hgood hN hp
    exact h.coeff_flat omega j N p hgood hN hp
  covariance_bound := by
    intro omega j N N' hgood hN hN' hne
    exact h.covariance_bound omega j N N' hgood hN hN' hne
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  exceedance_measurable := by
    intro j N
    exact
      measurableSet_trackBThresholdExceedanceEvent_scheduledCore
        h.Q h.point h.freshLo h.freshHi h.good h.M h.buffer j N
        (h.good_measurable j)
  countMean_le_beta_sum := h.countMean_le_beta_sum
  covarianceBudget_le_countSecond := h.covarianceBudget_le_countSecond
  gaussian_one_point_lower := h.gaussian_one_point_lower
  one_point_compare_lower := by
    intro j N hN
    simpa [trackBLinearPrimeScheduledCore] using
      h.one_point_compare_lower j N hN
  tail_prob_le_tailUpper := by
    intro j N hN
    simpa [trackBLinearPrimeScheduledCore] using
      h.tail_prob_le_tailUpper j N hN
  pair_compare_upper := by
    intro j N N' hN hN' hne
    simpa [trackBLinearPrimeScheduledCore] using
      h.pair_compare_upper j N N' hN hN' hne
  gaussian_pair_cov_upper := h.gaussian_pair_cov_upper
  tail_product_compare_lower := by
    intro j N N' hN hN' hne
    simpa [trackBLinearPrimeScheduledCore] using
      h.tail_product_compare_lower j N N' hN hN' hne
  pairCovBudget_le_pairCovUpper := h.pairCovBudget_le_pairCovUpper
  fail_summable := h.fail_summable
  prob_good_compl := h.prob_good_compl
  prob_overlap_many := by
    intro j
    simpa [trackBLinearPrimeScheduledCore, trackBLinearPrimeScheduledRemainder] using
      h.prob_overlap_many j

/-- Direct closure from the scheduled proof-audit Gaussian-comparison package. -/
theorem erdos1144_of_trackBLinearPrimeScheduledGaussianComparisonCertificate
    (h : TrackBLinearPrimeScheduledGaussianComparisonCertificate) :
    Erdos1144 :=
  erdos1144_of_trackBLinearPrimeGaussianComparisonCertificate
    (trackBLinearPrimeGaussianComparisonCertificate_of_scheduled h)

end Problem1144
end Erdos
