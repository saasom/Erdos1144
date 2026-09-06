import Erdos.Problem1144.HarperTrackBLinearPrimeScheduleTail

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

namespace Erdos
namespace Problem1144

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 20000

/-!
## Remaining concrete coefficient-geometry fields

The schedule module already proves the concrete fresh-prime interval
separation and the nonnegative covariance budget.  This file isolates the two
analytic coefficient-geometry inputs that remain: a variance floor and the
scalar divisor-scale flatness bound.
-/

theorem trackBLinearPrimeConcreteScheduleSpec_Q_eq :
    trackBLinearPrimeConcreteScheduleSpec.Q = trackBLinearPrimeConcreteQ :=
  rfl

theorem trackBLinearPrimeConcreteScheduleSpec_point_eq :
    trackBLinearPrimeConcreteScheduleSpec.point = trackBLinearPrimeConcretePoint :=
  rfl

theorem trackBLinearPrimeConcreteScheduleSpec_freshLo_eq :
    trackBLinearPrimeConcreteScheduleSpec.freshLo = trackBLinearPrimeConcreteFreshLo :=
  rfl

theorem trackBLinearPrimeConcreteScheduleSpec_freshHi_eq :
    trackBLinearPrimeConcreteScheduleSpec.freshHi = trackBLinearPrimeConcreteFreshHi :=
  rfl

theorem trackBLinearPrimeConcreteScheduleSpec_flat_eq :
    trackBLinearPrimeConcreteScheduleSpec.flat = trackBLinearPrimeConcreteFlat :=
  rfl

theorem trackBLinearPrimeConcreteScheduleSpec_freshSet_eq (j n : ℕ) :
    trackBLinearPrimeScheduledFreshSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point
        trackBLinearPrimeConcreteScheduleSpec.freshLo
        trackBLinearPrimeConcreteScheduleSpec.freshHi j n =
      trackBLinearPrimeScheduledFreshSet
        trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
        trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi j n :=
  rfl

/-- The concrete scheduled fresh set at a mesh point is exactly the single
fresh-prime layer attached to that mesh index. -/
theorem trackBLinearPrimeConcrete_scheduledFreshSet_eq_layer
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j) :
    trackBLinearPrimeScheduledFreshSet
        trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
        trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
        j (trackBLinearPrimeConcretePoint j r) =
      trackBFreshPrimeLayer
        (trackBLinearPrimeConcreteFreshLo j r) (trackBLinearPrimeConcreteFreshHi j r) := by
  refine trackBLinearPrimeScheduledFreshSet_eq_layer_of_unique hr ?_
  intro s hs hpoint
  have hinj :
      Set.InjOn (trackBLinearPrimeConcretePoint j)
        (trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j : Set ℕ) := by
    refine trackBLinearPrimeMesh_injOn_of_strict
      trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j ?_
    intro a b ha hb hab
    exact
      trackBLinearPrimeConcrete_point_strict j
        (by simpa [trackBLinearPrimeConcreteScheduleSpec] using ha)
        (by simpa [trackBLinearPrimeConcreteScheduleSpec] using hb)
        hab
  exact hinj (by simpa using hs) (by simpa using hr) hpoint

/-- Concrete scheduled variance at a mesh point, rewritten over the explicit
fresh-prime layer attached to that mesh index. -/
theorem trackBLinearPrimeConcrete_scheduledVariance_eq_layer
    (omega : Omega) (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j) :
    trackBLinearPrimeScheduledVariance
        trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
        trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
        omega j (trackBLinearPrimeConcretePoint j r) =
      ∑ p ∈
        trackBFreshPrimeLayer
          (trackBLinearPrimeConcreteFreshLo j r) (trackBLinearPrimeConcreteFreshHi j r),
        (trackBLinearPrimeScheduledFreshCoeff
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
          trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
          omega j (trackBLinearPrimeConcretePoint j r) p) ^ 2 := by
  unfold trackBLinearPrimeScheduledVariance trackBLinearPrimeVariance
  rw [trackBLinearPrimeConcrete_scheduledFreshSet_eq_layer j r hr]

/-- Expected concrete scheduled variance at a mesh point, rewritten over the
single explicit fresh-prime layer attached to that mesh index. -/
theorem integral_trackBLinearPrimeConcrete_scheduledVariance_eq_layer
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j) :
    ∫ omega,
        trackBLinearPrimeScheduledVariance
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
          trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
          omega j (trackBLinearPrimeConcretePoint j r) ∂mu =
      ∑ p ∈
        trackBFreshPrimeLayer
          (trackBLinearPrimeConcreteFreshLo j r) (trackBLinearPrimeConcreteFreshHi j r),
        ∑ m ∈
          trackBSquarefreeFreshCoeffSupport
            (trackBFreshPrimeLayer
              (trackBLinearPrimeConcreteFreshLo j r) (trackBLinearPrimeConcreteFreshHi j r))
            (trackBLinearPrimeConcretePoint j r) p,
          ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2 := by
  rw [integral_trackBLinearPrimeScheduledVariance_eq]
  rw [trackBLinearPrimeConcrete_scheduledFreshSet_eq_layer j r hr]

/-- A pointwise divisor-scale bound for the diagonal term in the concrete
fresh-prime expected-variance estimate. -/
theorem trackBLinearPrimeConcrete_point_div_mul_inv_prime_le_scale_mul_inv_freshLo
    (j r p : ℕ)
    (hp_layer :
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeConcreteFreshLo j r) (trackBLinearPrimeConcreteFreshHi j r)) :
    ((trackBLinearPrimeConcretePoint j r / p : ℕ) : ℝ) * (p : ℝ)⁻¹ ≤
      ((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) *
        (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹ := by
  have hp_lo : trackBLinearPrimeConcreteFreshLo j r ≤ p :=
    (mem_trackBFreshPrimeLayer.mp hp_layer).1
  have hp_prime : Nat.Prime p := (mem_trackBFreshPrimeLayer.mp hp_layer).2.2
  let scale : ℕ := trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK)
  have hN_eq :
      trackBLinearPrimeConcretePoint j r =
        trackBLinearPrimeConcreteFreshLo j r * scale := by
    simpa [scale] using trackBLinearPrimeConcrete_point_eq_freshLo_mul_divisorScale j r
  have hN_le : trackBLinearPrimeConcretePoint j r ≤ p * scale := by
    calc
      trackBLinearPrimeConcretePoint j r =
          trackBLinearPrimeConcreteFreshLo j r * scale := hN_eq
      _ ≤ p * scale := Nat.mul_le_mul_right scale hp_lo
  have hdivNat : trackBLinearPrimeConcretePoint j r / p ≤ scale :=
    Nat.div_le_of_le_mul hN_le
  have hdivR : ((trackBLinearPrimeConcretePoint j r / p : ℕ) : ℝ) ≤ (scale : ℝ) := by
    exact_mod_cast hdivNat
  have hfresh_pos_nat : 0 < trackBLinearPrimeConcreteFreshLo j r := by
    exact lt_of_lt_of_le
      (pow_pos (trackBLinearPrimeConcreteBase_pos j) (28 * trackBLinearPrimeConcreteK))
      (trackBLinearPrimeConcrete_basePow28K_le_freshLo j r)
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
  have hfresh_pos : (0 : ℝ) < trackBLinearPrimeConcreteFreshLo j r := by
    exact_mod_cast hfresh_pos_nat
  have hp_lo_real : (trackBLinearPrimeConcreteFreshLo j r : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hp_lo
  have hinv : (p : ℝ)⁻¹ ≤ (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹ :=
    (inv_le_inv₀ hp_pos hfresh_pos).mpr hp_lo_real
  have hscale_nonneg : 0 ≤ (scale : ℝ) := by exact_mod_cast Nat.zero_le scale
  calc
    ((trackBLinearPrimeConcretePoint j r / p : ℕ) : ℝ) * (p : ℝ)⁻¹
        ≤ (scale : ℝ) * (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹ := by
          exact mul_le_mul hdivR hinv (inv_nonneg.mpr hp_pos.le) hscale_nonneg
    _ = ((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) *
          (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹ := by
        rfl

/-- Crude expected-variance bound before paying the fresh-layer cardinality. -/
theorem integral_trackBLinearPrimeConcrete_scheduledVariance_le_sum_scale_inv_freshLo
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j) :
    ∫ omega,
        trackBLinearPrimeScheduledVariance
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
          trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
          omega j (trackBLinearPrimeConcretePoint j r) ∂mu ≤
      ∑ _p ∈ trackBFreshPrimeLayer
          (trackBLinearPrimeConcreteFreshLo j r) (trackBLinearPrimeConcreteFreshHi j r),
        ((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) *
          (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹ := by
  classical
  rw [integral_trackBLinearPrimeConcrete_scheduledVariance_eq_layer j r hr]
  exact Finset.sum_le_sum (fun p hp => by
    have hp_prime : Nat.Prime p := (mem_trackBFreshPrimeLayer.mp hp).2.2
    calc
      (∑ m ∈ trackBSquarefreeFreshCoeffSupport
          (trackBFreshPrimeLayer
            (trackBLinearPrimeConcreteFreshLo j r) (trackBLinearPrimeConcreteFreshHi j r))
          (trackBLinearPrimeConcretePoint j r) p,
          ((Real.sqrt (((p * m : ℕ) : ℝ)))⁻¹) ^ 2)
          ≤ ((trackBLinearPrimeConcretePoint j r / p : ℕ) : ℝ) * (p : ℝ)⁻¹ := by
            exact trackBSquarefreeFreshCoeffSupport_sq_sum_le_div_mul_inv_prime _ _ p
              hp_prime
      _ ≤ ((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) *
          (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹ := by
            exact
              trackBLinearPrimeConcrete_point_div_mul_inv_prime_le_scale_mul_inv_freshLo
                j r p hp)

/-- Crude expected-variance bound using only the fresh layer's cardinality. -/
theorem integral_trackBLinearPrimeConcrete_scheduledVariance_le_crude_layer
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j) :
    ∫ omega,
        trackBLinearPrimeScheduledVariance
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
          trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
          omega j (trackBLinearPrimeConcretePoint j r) ∂mu ≤
      (trackBLinearPrimeConcreteFreshHi j r : ℝ) *
        (((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) *
          (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹) := by
  have hfresh_pos_nat : 0 < trackBLinearPrimeConcreteFreshLo j r := by
    exact lt_of_lt_of_le
      (pow_pos (trackBLinearPrimeConcreteBase_pos j) (28 * trackBLinearPrimeConcreteK))
      (trackBLinearPrimeConcrete_basePow28K_le_freshLo j r)
  have hcard_nat :
      (trackBFreshPrimeLayer
        (trackBLinearPrimeConcreteFreshLo j r)
        (trackBLinearPrimeConcreteFreshHi j r)).card ≤
        trackBLinearPrimeConcreteFreshHi j r :=
    trackBFreshPrimeLayer_card_le_hi hfresh_pos_nat
  have hcard_real :
      ((trackBFreshPrimeLayer
        (trackBLinearPrimeConcreteFreshLo j r)
        (trackBLinearPrimeConcreteFreshHi j r)).card : ℝ) ≤
        (trackBLinearPrimeConcreteFreshHi j r : ℝ) := by
    exact_mod_cast hcard_nat
  have hterm_nonneg :
      0 ≤ (((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) *
          (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹) := by
    have hfresh_nonneg : (0 : ℝ) ≤ trackBLinearPrimeConcreteFreshLo j r := by
      exact_mod_cast hfresh_pos_nat.le
    exact mul_nonneg (by exact_mod_cast Nat.zero_le _) (inv_nonneg.mpr hfresh_nonneg)
  calc
    ∫ omega,
        trackBLinearPrimeScheduledVariance
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
          trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
          omega j (trackBLinearPrimeConcretePoint j r) ∂mu
        ≤ ∑ _p ∈ trackBFreshPrimeLayer
            (trackBLinearPrimeConcreteFreshLo j r) (trackBLinearPrimeConcreteFreshHi j r),
          ((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) *
            (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹ :=
        integral_trackBLinearPrimeConcrete_scheduledVariance_le_sum_scale_inv_freshLo j r hr
    _ = ((trackBFreshPrimeLayer
            (trackBLinearPrimeConcreteFreshLo j r)
            (trackBLinearPrimeConcreteFreshHi j r)).card : ℝ) *
          (((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) *
            (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (trackBLinearPrimeConcreteFreshHi j r : ℝ) *
          (((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) *
            (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right hcard_real hterm_nonneg

/-- Natural-number cancellation behind the concrete expected-variance scale. -/
theorem trackBLinearPrimeConcrete_freshHi_mul_scale_eq_freshLo_mul_base_threeK
    (j r : ℕ) :
    trackBLinearPrimeConcreteFreshHi j r *
        trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) =
      trackBLinearPrimeConcreteFreshLo j r *
        trackBLinearPrimeConcreteBase j ^ (3 * trackBLinearPrimeConcreteK) := by
  rw [trackBLinearPrimeConcreteFreshHi, trackBLinearPrimeConcreteFreshLo]
  set b := trackBLinearPrimeConcreteBase j
  set q := trackBLinearPrimeConcretePointRatio j ^ r
  have hpow :
      b ^ (29 * trackBLinearPrimeConcreteK) * b ^ (2 * trackBLinearPrimeConcreteK) =
        b ^ (28 * trackBLinearPrimeConcreteK) * b ^ (3 * trackBLinearPrimeConcreteK) := by
    rw [← pow_add, ← pow_add]
    norm_num [trackBLinearPrimeConcreteK]
  calc
    (b ^ (29 * trackBLinearPrimeConcreteK) * q) *
        b ^ (2 * trackBLinearPrimeConcreteK)
        = (b ^ (29 * trackBLinearPrimeConcreteK) *
            b ^ (2 * trackBLinearPrimeConcreteK)) * q := by
          rw [Nat.mul_assoc, Nat.mul_comm q (b ^ (2 * trackBLinearPrimeConcreteK)),
            ← Nat.mul_assoc]
    _ = (b ^ (28 * trackBLinearPrimeConcreteK) *
            b ^ (3 * trackBLinearPrimeConcreteK)) * q := by
          rw [hpow]
    _ = (b ^ (28 * trackBLinearPrimeConcreteK) * q) *
        b ^ (3 * trackBLinearPrimeConcreteK) := by
          rw [Nat.mul_assoc, Nat.mul_comm (b ^ (3 * trackBLinearPrimeConcreteK)) q,
            ← Nat.mul_assoc]

/-- The crude expected-variance scale simplifies to `base^(3K)`. -/
theorem trackBLinearPrimeConcrete_crudeVarianceBound_eq_base_threeK (j r : ℕ) :
    (trackBLinearPrimeConcreteFreshHi j r : ℝ) *
        (((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) *
          (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹) =
      (trackBLinearPrimeConcreteBase j : ℝ) ^ (3 * trackBLinearPrimeConcreteK) := by
  have hnat :=
    trackBLinearPrimeConcrete_freshHi_mul_scale_eq_freshLo_mul_base_threeK j r
  have hreal :
      (trackBLinearPrimeConcreteFreshHi j r : ℝ) *
          ((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) =
        (trackBLinearPrimeConcreteFreshLo j r : ℝ) *
          ((trackBLinearPrimeConcreteBase j ^ (3 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hlo_ne : (trackBLinearPrimeConcreteFreshLo j r : ℝ) ≠ 0 := by
    have hpos : 0 < trackBLinearPrimeConcreteFreshLo j r := by
      exact lt_of_lt_of_le
        (pow_pos (trackBLinearPrimeConcreteBase_pos j) (28 * trackBLinearPrimeConcreteK))
        (trackBLinearPrimeConcrete_basePow28K_le_freshLo j r)
    exact_mod_cast (ne_of_gt hpos)
  calc
    (trackBLinearPrimeConcreteFreshHi j r : ℝ) *
        (((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) *
          (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹)
        = ((trackBLinearPrimeConcreteFreshHi j r : ℝ) *
            ((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ)) *
            (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹ := by
          rw [mul_assoc]
    _ = ((trackBLinearPrimeConcreteFreshLo j r : ℝ) *
          ((trackBLinearPrimeConcreteBase j ^ (3 * trackBLinearPrimeConcreteK) : ℕ) : ℝ)) *
            (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹ := by
          rw [hreal]
    _ = ((trackBLinearPrimeConcreteBase j ^ (3 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) := by
          rw [mul_assoc]
          rw [mul_comm
            ((trackBLinearPrimeConcreteBase j ^ (3 * trackBLinearPrimeConcreteK) : ℕ) : ℝ)
            (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹]
          rw [← mul_assoc, mul_inv_cancel₀ hlo_ne, one_mul]
    _ = (trackBLinearPrimeConcreteBase j : ℝ) ^ (3 * trackBLinearPrimeConcreteK) := by
          exact_mod_cast (rfl :
            trackBLinearPrimeConcreteBase j ^ (3 * trackBLinearPrimeConcreteK) =
              trackBLinearPrimeConcreteBase j ^ (3 * trackBLinearPrimeConcreteK))

/-- Concrete expected variance is at most `base^(3K)` for the current
`1 / sqrt(p*m)` coefficient layer. -/
theorem integral_trackBLinearPrimeConcrete_scheduledVariance_le_base_threeK
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j) :
    ∫ omega,
        trackBLinearPrimeScheduledVariance
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
          trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
          omega j (trackBLinearPrimeConcretePoint j r) ∂mu ≤
      (trackBLinearPrimeConcreteBase j : ℝ) ^ (3 * trackBLinearPrimeConcreteK) := by
  calc
    ∫ omega,
        trackBLinearPrimeScheduledVariance
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
          trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
          omega j (trackBLinearPrimeConcretePoint j r) ∂mu
        ≤ (trackBLinearPrimeConcreteFreshHi j r : ℝ) *
          (((trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) : ℕ) : ℝ) *
            (trackBLinearPrimeConcreteFreshLo j r : ℝ)⁻¹) :=
        integral_trackBLinearPrimeConcrete_scheduledVariance_le_crude_layer j r hr
    _ = (trackBLinearPrimeConcreteBase j : ℝ) ^ (3 * trackBLinearPrimeConcreteK) :=
        trackBLinearPrimeConcrete_crudeVarianceBound_eq_base_threeK j r

/-- The crude expected-variance scale is at most half of the concrete target
variance `V_j`. -/
theorem trackBLinearPrimeConcrete_base_threeK_le_half_V (j : ℕ) :
    (trackBLinearPrimeConcreteBase j : ℝ) ^ (3 * trackBLinearPrimeConcreteK) ≤
      trackBLinearPrimeConcreteV j / 2 := by
  let bR : ℝ := trackBLinearPrimeConcreteBase j
  have hb_pos : 0 < bR := by
    dsimp [bR]
    exact_mod_cast trackBLinearPrimeConcreteBase_pos j
  have hb_two : (2 : ℝ) ≤ bR := by
    dsimp [bR]
    exact_mod_cast trackBLinearPrimeConcreteBase_two_le j
  have hb_one : (1 : ℝ) ≤ bR := le_trans (by norm_num) hb_two
  have hpow17 : (2 : ℝ) ≤ bR ^ (17 * trackBLinearPrimeConcreteK) := by
    have hble : bR ≤ bR ^ (17 * trackBLinearPrimeConcreteK) := by
      have hexp_pos : 0 < 17 * trackBLinearPrimeConcreteK := by
        norm_num [trackBLinearPrimeConcreteK]
      exact le_self_pow₀ hb_one (ne_of_gt hexp_pos)
    exact le_trans hb_two hble
  have hnonneg3 : 0 ≤ bR ^ (3 * trackBLinearPrimeConcreteK) :=
    (pow_pos hb_pos _).le
  have hmul :
      (2 : ℝ) * bR ^ (3 * trackBLinearPrimeConcreteK) ≤
        bR ^ (17 * trackBLinearPrimeConcreteK) * bR ^ (3 * trackBLinearPrimeConcreteK) :=
    mul_le_mul_of_nonneg_right hpow17 hnonneg3
  have hpow_eq :
      bR ^ (17 * trackBLinearPrimeConcreteK) * bR ^ (3 * trackBLinearPrimeConcreteK) =
        bR ^ (20 * trackBLinearPrimeConcreteK) := by
    rw [← pow_add]
    norm_num [trackBLinearPrimeConcreteK]
  have htwo :
      (2 : ℝ) * bR ^ (3 * trackBLinearPrimeConcreteK) ≤
        bR ^ (20 * trackBLinearPrimeConcreteK) := by
    simpa [hpow_eq] using hmul
  have htwo_pos : (0 : ℝ) < 2 := by norm_num
  have hdiv := (le_div_iff₀' htwo_pos).mpr htwo
  simpa [trackBLinearPrimeConcreteV, bR] using hdiv

/-- Expected concrete scheduled variance is at most half of the target
variance for the current squarefree fresh-prime coefficient layer. -/
theorem integral_trackBLinearPrimeConcrete_scheduledVariance_le_half_V
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j) :
    ∫ omega,
        trackBLinearPrimeScheduledVariance
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
          trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
          omega j (trackBLinearPrimeConcretePoint j r) ∂mu ≤
      trackBLinearPrimeConcreteV j / 2 :=
  (integral_trackBLinearPrimeConcrete_scheduledVariance_le_base_threeK j r hr).trans
    (trackBLinearPrimeConcrete_base_threeK_le_half_V j)

/-- Exponent diagnostic for one fresh layer of width `b^K`: if the
support-size flatness route can prove `N / p^(3/2) <= b^(-K)`, then the
corresponding crude variance exponent is at most `11K`, far below the current
target exponent `20K`.  This is the Lean-checkable arithmetic behind
`notes/1144/open_tasks/14_fresh_layer_scale_repair.md`. -/
theorem trackBLinearPrimeConcrete_supportFlatness_forces_varianceExponent_le_elevenK
    {a : ℕ}
    (hflatExp :
      2 * (30 * trackBLinearPrimeConcreteK + trackBLinearPrimeConcreteK) ≤
        3 * a) :
    30 * trackBLinearPrimeConcreteK + trackBLinearPrimeConcreteK - a ≤
      11 * trackBLinearPrimeConcreteK := by
  norm_num [trackBLinearPrimeConcreteK] at hflatExp ⊢
  omega

/-- Exponent diagnostic in the other direction: making the crude expectation
scale reach `b^(20K)` with one fresh layer of width `b^K` forces the fresh
lower exponent to be at most `11K`. -/
theorem trackBLinearPrimeConcrete_varianceScale_forces_freshExponent_le_elevenK
    {a : ℕ}
    (hvarExp :
      20 * trackBLinearPrimeConcreteK + a ≤
        30 * trackBLinearPrimeConcreteK + trackBLinearPrimeConcreteK) :
    a ≤ 11 * trackBLinearPrimeConcreteK := by
  norm_num [trackBLinearPrimeConcreteK] at hvarExp ⊢
  omega

/-- The one-layer exponent repair cannot keep both the current deterministic
support-size flatness proof and the current `V_j = b^(20K)` variance scale.
One of the analytic ingredients has to change. -/
theorem trackBLinearPrimeConcrete_oneLayer_flatness_varianceScale_incompatible
    {a : ℕ}
    (hflatExp :
      2 * (30 * trackBLinearPrimeConcreteK + trackBLinearPrimeConcreteK) ≤
        3 * a)
    (hvarExp :
      20 * trackBLinearPrimeConcreteK + a ≤
        30 * trackBLinearPrimeConcreteK + trackBLinearPrimeConcreteK) :
    False := by
  have ha_low : 2067 ≤ a := by
    norm_num [trackBLinearPrimeConcreteK] at hflatExp
    omega
  have ha_high :
      a ≤ 11 * trackBLinearPrimeConcreteK :=
    trackBLinearPrimeConcrete_varianceScale_forces_freshExponent_le_elevenK hvarExp
  norm_num [trackBLinearPrimeConcreteK] at ha_high
  omega

/-- Real-valued Markov consequence of the expected-variance scale audit: for
the current coefficient layer, a fixed concrete mesh point reaches the
requested variance target with probability at most `1/2`. -/
theorem measureReal_trackBLinearPrimeConcrete_scheduledVariance_ge_V_le_half
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j) :
    mu.real {omega : Omega |
        trackBLinearPrimeConcreteV j ≤
          trackBLinearPrimeScheduledVariance
            trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
            trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
            omega j (trackBLinearPrimeConcretePoint j r)}
      ≤ (1 : ℝ) / 2 := by
  let W : Omega → ℝ := fun omega =>
    trackBLinearPrimeScheduledVariance
      trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
      trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
      omega j (trackBLinearPrimeConcretePoint j r)
  let A : ℝ := trackBLinearPrimeConcreteV j
  let T : Set Omega := {omega | A ≤ W omega}
  have hW_int : Integrable W mu := by
    dsimp [W]
    exact
      integrable_trackBLinearPrimeScheduledVariance
        trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
        trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi j
        (trackBLinearPrimeConcretePoint j r)
  have hW_nonneg : 0 ≤ᵐ[mu] W :=
    ae_of_all _ fun omega => by
      dsimp [W]
      exact
        trackBLinearPrimeScheduledVariance_nonneg
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
          trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi omega j
          (trackBLinearPrimeConcretePoint j r)
  have hA_pos : 0 < A := by
    dsimp [A, trackBLinearPrimeConcreteV]
    exact pow_pos (by exact_mod_cast trackBLinearPrimeConcreteBase_pos j) _
  have hmean : (∫ omega, W omega ∂mu) ≤ A / 2 := by
    dsimp [W, A]
    exact integral_trackBLinearPrimeConcrete_scheduledVariance_le_half_V j r hr
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg (μ := mu) (f := W) hW_nonneg hW_int A
  have hTreal : mu.real T ≤ (1 : ℝ) / 2 := by
    have hmul : A * mu.real T ≤ A / 2 := le_trans hmarkov hmean
    have hdiv : mu.real T ≤ (A / 2) / A := by
      rw [le_div_iff₀ hA_pos]
      simpa [mul_comm] using hmul
    have hratio : (A / 2) / A = (1 : ℝ) / 2 := by
      field_simp [ne_of_gt hA_pos]
    simpa [hratio] using hdiv
  simpa [T, W, A] using hTreal

/-- Markov consequence of the expected-variance scale audit: for the current
coefficient layer, a fixed concrete mesh point reaches the requested variance
target with probability at most `1/2`. -/
theorem measure_trackBLinearPrimeConcrete_scheduledVariance_ge_V_le_half
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j) :
    mu {omega : Omega |
        trackBLinearPrimeConcreteV j ≤
          trackBLinearPrimeScheduledVariance
            trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
            trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
            omega j (trackBLinearPrimeConcretePoint j r)}
      ≤ ENNReal.ofReal ((1 : ℝ) / 2) := by
  let T : Set Omega := {omega |
    trackBLinearPrimeConcreteV j ≤
      trackBLinearPrimeScheduledVariance
        trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
        trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
        omega j (trackBLinearPrimeConcretePoint j r)}
  change mu T ≤ ENNReal.ofReal ((1 : ℝ) / 2)
  rw [← ofReal_measureReal (μ := mu) (s := T)]
  exact ENNReal.ofReal_le_ofReal
    (measureReal_trackBLinearPrimeConcrete_scheduledVariance_ge_V_le_half j r hr)

/-- Complementary obstruction form of the scale audit: for the current
coefficient layer, the variance falls below the requested target with
probability at least `1/2` at each fixed concrete mesh point. -/
theorem measure_trackBLinearPrimeConcrete_scheduledVariance_lt_V_ge_half
    (j r : ℕ)
    (hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j) :
    ENNReal.ofReal ((1 : ℝ) / 2) ≤
      mu {omega : Omega |
          trackBLinearPrimeScheduledVariance
            trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
            trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
            omega j (trackBLinearPrimeConcretePoint j r) <
          trackBLinearPrimeConcreteV j} := by
  let W : Omega → ℝ := fun omega =>
    trackBLinearPrimeScheduledVariance
      trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
      trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
      omega j (trackBLinearPrimeConcretePoint j r)
  let A : ℝ := trackBLinearPrimeConcreteV j
  let T : Set Omega := {omega | A ≤ W omega}
  let B : Set Omega := {omega | W omega < A}
  have hT_meas : MeasurableSet T := by
    dsimp [T, W, A]
    exact
      measurableSet_le measurable_const
        (measurable_trackBLinearPrimeScheduledVariance
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
          trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi j
          (trackBLinearPrimeConcretePoint j r))
  have hB_eq : B = Tᶜ := by
    ext omega
    simp [B, T]
  have hTreal :
      mu.real T ≤ (1 : ℝ) / 2 := by
    dsimp [T, W, A]
    exact measureReal_trackBLinearPrimeConcrete_scheduledVariance_ge_V_le_half j r hr
  have hBreal : (1 : ℝ) / 2 ≤ mu.real B := by
    have hcomp : mu.real Tᶜ = 1 - mu.real T :=
      probReal_compl_eq_one_sub (μ := mu) hT_meas
    calc
      (1 : ℝ) / 2 ≤ 1 - mu.real T := by linarith
      _ = mu.real Tᶜ := hcomp.symm
      _ = mu.real B := by rw [← hB_eq]
  change ENNReal.ofReal ((1 : ℝ) / 2) ≤ mu B
  rw [← ofReal_measureReal (μ := mu) (s := B)]
  exact ENNReal.ofReal_le_ofReal hBreal

/-- Concrete divisor-scale flatness for one explicit fresh-prime layer. -/
theorem trackBLinearPrimeConcrete_coeff_div_bound_layer
    (j n p r : ℕ)
    (hpoint : trackBLinearPrimeConcretePoint j r = n)
    (hp_layer :
      p ∈ trackBFreshPrimeLayer
        (trackBLinearPrimeConcreteFreshLo j r) (trackBLinearPrimeConcreteFreshHi j r)) :
    ((n / p : ℕ) : ℝ) * (Real.sqrt ((p : ℕ) : ℝ))⁻¹ ≤
        trackBLinearPrimeConcreteFlat j := by
  have hp_lo : trackBLinearPrimeConcreteFreshLo j r ≤ p :=
    (mem_trackBFreshPrimeLayer.mp hp_layer).1
  have hp_prime : Nat.Prime p :=
    (mem_trackBFreshPrimeLayer.mp hp_layer).2.2
  let scale : ℕ := trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK)
  have hN_eq : n = trackBLinearPrimeConcreteFreshLo j r * scale := by
    rw [← hpoint]
    simpa [scale] using trackBLinearPrimeConcrete_point_eq_freshLo_mul_divisorScale j r
  have hN_le : n ≤ p * scale := by
    calc
      n = trackBLinearPrimeConcreteFreshLo j r * scale := hN_eq
      _ ≤ p * scale := Nat.mul_le_mul_right scale hp_lo
  have hdivNat : n / p ≤ scale := Nat.div_le_of_le_mul hN_le
  have hdivR : ((n / p : ℕ) : ℝ) ≤ (scale : ℝ) := by
    exact_mod_cast hdivNat
  have hscale_cast :
      (scale : ℝ) =
        (trackBLinearPrimeConcreteBase j : ℝ) ^ (2 * trackBLinearPrimeConcreteK) := by
    dsimp [scale]
    exact_mod_cast (rfl :
      trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK) =
        trackBLinearPrimeConcreteBase j ^ (2 * trackBLinearPrimeConcreteK))
  have hp_lower_nat :
      trackBLinearPrimeConcreteBase j ^ (28 * trackBLinearPrimeConcreteK) ≤ p :=
    le_trans (trackBLinearPrimeConcrete_basePow28K_le_freshLo j r) hp_lo
  have hp_lower_real :
      (trackBLinearPrimeConcreteBase j : ℝ) ^ (28 * trackBLinearPrimeConcreteK) ≤
        (p : ℝ) := by
    exact_mod_cast hp_lower_nat
  have hsquare_eq :
      ((trackBLinearPrimeConcreteBase j : ℝ) ^ (14 * trackBLinearPrimeConcreteK)) ^ 2 =
        (trackBLinearPrimeConcreteBase j : ℝ) ^ (28 * trackBLinearPrimeConcreteK) := by
    rw [← pow_mul]
    congr 1
  have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.zero_le p)
  have hpow14_nonneg :
      0 ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ (14 * trackBLinearPrimeConcreteK) := by
    exact pow_nonneg (by exact_mod_cast (Nat.zero_le (trackBLinearPrimeConcreteBase j))) _
  have hsqrt_lower :
      (trackBLinearPrimeConcreteBase j : ℝ) ^ (14 * trackBLinearPrimeConcreteK) ≤
        Real.sqrt ((p : ℕ) : ℝ) := by
    rw [Real.le_sqrt hpow14_nonneg hp_nonneg]
    exact le_trans (le_of_eq hsquare_eq) hp_lower_real
  have hbase_pos_real : (0 : ℝ) < trackBLinearPrimeConcreteBase j := by
    exact_mod_cast trackBLinearPrimeConcreteBase_pos j
  have hpow14_pos :
      0 < (trackBLinearPrimeConcreteBase j : ℝ) ^ (14 * trackBLinearPrimeConcreteK) := by
    exact pow_pos hbase_pos_real _
  have hsqrt_pos : 0 < Real.sqrt ((p : ℕ) : ℝ) := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast hp_prime.pos)
  have hinv_sqrt :
      (Real.sqrt ((p : ℕ) : ℝ))⁻¹ ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^
          (14 * trackBLinearPrimeConcreteK)))⁻¹ := by
    exact (inv_le_inv₀ hsqrt_pos hpow14_pos).mpr hsqrt_lower
  have hscale_nonneg : 0 ≤ (scale : ℝ) := by
    exact_mod_cast (Nat.zero_le scale)
  have hmul_bound :
      ((n / p : ℕ) : ℝ) * (Real.sqrt ((p : ℕ) : ℝ))⁻¹ ≤
        (scale : ℝ) *
          (((trackBLinearPrimeConcreteBase j : ℝ) ^
            (14 * trackBLinearPrimeConcreteK)))⁻¹ := by
    exact mul_le_mul hdivR hinv_sqrt (inv_nonneg.mpr (Real.sqrt_nonneg _))
      hscale_nonneg
  have hscale_bound :
      (scale : ℝ) *
          (((trackBLinearPrimeConcreteBase j : ℝ) ^
            (14 * trackBLinearPrimeConcreteK)))⁻¹ ≤
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ trackBLinearPrimeConcreteK))⁻¹ := by
    rw [hscale_cast]
    have hb1 : (1 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
      exact_mod_cast (trackBLinearPrimeConcreteBase_one_lt j).le
    have hbpos : (0 : ℝ) < trackBLinearPrimeConcreteBase j := by
      exact_mod_cast trackBLinearPrimeConcreteBase_pos j
    unfold trackBLinearPrimeConcreteK
    norm_num
    have hpow :
        (trackBLinearPrimeConcreteBase j : ℝ) ^ 300 ≤
          (trackBLinearPrimeConcreteBase j : ℝ) ^ 1400 := by
      have hpow1100 : (1 : ℝ) ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 1100 :=
        one_le_pow₀ hb1
      have hnonneg300 : 0 ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 300 :=
        (pow_pos hbpos 300).le
      calc
        (trackBLinearPrimeConcreteBase j : ℝ) ^ 300
            ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 300 *
                (trackBLinearPrimeConcreteBase j : ℝ) ^ 1100 :=
              le_mul_of_one_le_right hnonneg300 hpow1100
        _ = (trackBLinearPrimeConcreteBase j : ℝ) ^ (300 + 1100) := by rw [pow_add]
        _ = (trackBLinearPrimeConcreteBase j : ℝ) ^ 1400 := by norm_num
    have hpos300 : (0 : ℝ) < (trackBLinearPrimeConcreteBase j : ℝ) ^ 300 :=
      pow_pos hbpos 300
    have hpos1400 : (0 : ℝ) < (trackBLinearPrimeConcreteBase j : ℝ) ^ 1400 :=
      pow_pos hbpos 1400
    have hinv :
        (((trackBLinearPrimeConcreteBase j : ℝ) ^ 1400))⁻¹ ≤
          (((trackBLinearPrimeConcreteBase j : ℝ) ^ 300))⁻¹ :=
      (inv_le_inv₀ hpos1400 hpos300).mpr hpow
    calc
      (trackBLinearPrimeConcreteBase j : ℝ) ^ 200 *
          (((trackBLinearPrimeConcreteBase j : ℝ) ^ 1400))⁻¹
          ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 200 *
              (((trackBLinearPrimeConcreteBase j : ℝ) ^ 300))⁻¹ :=
            mul_le_mul_of_nonneg_left hinv (pow_pos hbpos 200).le
      _ = (((trackBLinearPrimeConcreteBase j : ℝ) ^ 100))⁻¹ := by
        have hpos100 : (0 : ℝ) < (trackBLinearPrimeConcreteBase j : ℝ) ^ 100 :=
          pow_pos hbpos 100
        field_simp [hpos100.ne', hpos300.ne']
  exact le_trans hmul_bound hscale_bound

/-- Concrete divisor-scale flatness for the explicit scheduled fresh-prime set.

The proof is deliberately local to the concrete schedule, avoiding a broad
scheduled-fresh-set theorem that forces Lean to unfold the whole schedule
record. -/
theorem trackBLinearPrimeConcrete_coeff_div_bound_explicit
    (j n p : ℕ)
    (hp : p ∈ trackBLinearPrimeScheduledFreshSet
        trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
        trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi j n) :
    ((n / p : ℕ) : ℝ) * (Real.sqrt ((p : ℕ) : ℝ))⁻¹ ≤
        trackBLinearPrimeConcreteFlat j := by
  classical
  simp only [trackBLinearPrimeScheduledFreshSet, Finset.mem_biUnion, Finset.mem_filter] at hp
  rcases hp with ⟨r, ⟨_hr, hpoint⟩, hp_layer⟩
  exact trackBLinearPrimeConcrete_coeff_div_bound_layer j n p r hpoint hp_layer

/-- Concrete divisor-scale flatness in the schedule-spec field shape. -/
theorem trackBLinearPrimeConcrete_coeff_div_bound
    (j n p : ℕ)
    (_hN : n ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point j)
    (hp : p ∈ trackBLinearPrimeScheduledFreshSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point
        trackBLinearPrimeConcreteScheduleSpec.freshLo
        trackBLinearPrimeConcreteScheduleSpec.freshHi j n) :
    ((n / p : ℕ) : ℝ) * (Real.sqrt ((p : ℕ) : ℝ))⁻¹ ≤
        trackBLinearPrimeConcreteScheduleSpec.flat j := by
  rw [trackBLinearPrimeConcreteScheduleSpec_flat_eq]
  rw [trackBLinearPrimeConcreteScheduleSpec_freshSet_eq] at hp
  simp only [trackBLinearPrimeScheduledFreshSet, Finset.mem_biUnion, Finset.mem_filter] at hp
  rcases hp with ⟨r, ⟨_hr, hpoint⟩, hp_layer⟩
  exact trackBLinearPrimeConcrete_coeff_div_bound_layer j n p r hpoint hp_layer

/-- Concrete fresh-prime intervals are pairwise disjoint in fully explicit
schedule form. -/
theorem trackBLinearPrimeConcrete_fresh_interval_disjoint_explicit
    (j r s : ℕ)
    (_hr : r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j)
    (_hs : s ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j)
    (hne : r ≠ s) :
    trackBLinearPrimeConcreteFreshHi j r < trackBLinearPrimeConcreteFreshLo j s ∨
      trackBLinearPrimeConcreteFreshHi j s < trackBLinearPrimeConcreteFreshLo j r := by
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · refine Or.inl ?_
    exact
      (trackBLinearPrimeConcrete_freshHi_lt_freshLo_succ j r).trans_le
        (trackBLinearPrimeConcrete_freshLo_mono j (Nat.succ_le_of_lt hrs))
  · refine Or.inr ?_
    exact
      (trackBLinearPrimeConcrete_freshHi_lt_freshLo_succ j s).trans_le
        (trackBLinearPrimeConcrete_freshLo_mono j (Nat.succ_le_of_lt hsr))

/-- The concrete covariance budget is nonnegative in fully explicit schedule
form. -/
theorem trackBLinearPrimeConcrete_rho_mul_V_nonneg_explicit (j : ℕ) :
    0 ≤ trackBLinearPrimeConcreteRho j * trackBLinearPrimeConcreteV j := by
  exact mul_nonneg (trackBLinearPrimeConcreteRho_nonneg j)
    (trackBLinearPrimeConcreteV_nonneg j)

/-- The only non-scalar geometry fact still needed for the concrete schedule. -/
structure TrackBLinearPrimeConcreteGeometryAnalyticFacts where
  variance_floor :
    ∀ omega j N,
      omega ∈ trackBLinearPrimeConcreteScheduleSpec.good j →
      N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteScheduleSpec.Q
        trackBLinearPrimeConcreteScheduleSpec.point j →
      trackBLinearPrimeConcreteScheduleSpec.V j ≤
        trackBLinearPrimeScheduledVariance
          trackBLinearPrimeConcreteScheduleSpec.Q
          trackBLinearPrimeConcreteScheduleSpec.point
          trackBLinearPrimeConcreteScheduleSpec.freshLo
          trackBLinearPrimeConcreteScheduleSpec.freshHi omega j N

/-- Layer-indexed version of the concrete all-space variance-floor input. -/
structure TrackBLinearPrimeConcreteLayerVarianceAnalyticFacts where
  variance_layer_floor :
    ∀ omega j r,
      r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j →
        trackBLinearPrimeConcreteV j ≤
          ∑ p ∈
            trackBFreshPrimeLayer
              (trackBLinearPrimeConcreteFreshLo j r) (trackBLinearPrimeConcreteFreshHi j r),
            (trackBLinearPrimeScheduledFreshCoeff
              trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
              trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
              omega j (trackBLinearPrimeConcretePoint j r) p) ^ 2

/-- Convert a layer-indexed concrete variance floor into the all-space
scheduled geometry analytic field. -/
def trackBLinearPrimeConcreteGeometryAnalyticFacts_of_layerVariance
    (h : TrackBLinearPrimeConcreteLayerVarianceAnalyticFacts) :
    TrackBLinearPrimeConcreteGeometryAnalyticFacts where
  variance_floor := by
    intro omega j N _hgood hN
    rcases mem_trackBLinearPrimeMeshTestSet.mp hN with ⟨r, hr, hpoint⟩
    subst N
    change trackBLinearPrimeConcreteV j ≤
      trackBLinearPrimeScheduledVariance
        trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
        trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
        omega j (trackBLinearPrimeConcretePoint j r)
    rw [trackBLinearPrimeConcrete_scheduledVariance_eq_layer omega j r hr]
    exact h.variance_layer_floor omega j r hr

/-- Assemble the concrete geometry facts from the remaining analytic
geometry inputs plus the schedule arithmetic already proved. -/
def trackBLinearPrimeConcreteGeometryFacts_of_analytic
    (h : TrackBLinearPrimeConcreteGeometryAnalyticFacts) :
    TrackBLinearPrimeScheduleGeometryFacts trackBLinearPrimeConcreteScheduleSpec where
  variance_floor := h.variance_floor
  coeff_div_bound := trackBLinearPrimeConcrete_coeff_div_bound
  fresh_interval_disjoint := trackBLinearPrimeConcrete_fresh_interval_disjoint
  budget_nonneg := trackBLinearPrimeConcrete_rho_mul_V_nonneg

/-- The concrete variance-floor good event: every scheduled test point at
stage `j` has coefficient square-sum at least the target `V_j`. -/
noncomputable def trackBLinearPrimeConcreteVarianceGood (j : ℕ) : Set Omega :=
  ⋂ N : ℕ,
    {omega |
      N ∈ trackBLinearPrimeMeshTestSet
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j →
        trackBLinearPrimeConcreteV j ≤
          trackBLinearPrimeScheduledVariance
            trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
            trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi omega j N}

/-- The concrete variance-floor good event is measurable. -/
theorem measurableSet_trackBLinearPrimeConcreteVarianceGood (j : ℕ) :
    MeasurableSet (trackBLinearPrimeConcreteVarianceGood j) := by
  unfold trackBLinearPrimeConcreteVarianceGood
  refine MeasurableSet.iInter (fun N : ℕ => ?_)
  by_cases hN :
      N ∈ trackBLinearPrimeMeshTestSet
        trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j
  · simp only [hN, true_implies]
    exact measurableSet_le measurable_const
      (measurable_trackBLinearPrimeScheduledVariance
        trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
        trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi j N)
  · have hset :
        {omega : Omega |
          N ∈ trackBLinearPrimeMeshTestSet
            trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j →
          trackBLinearPrimeConcreteV j ≤
            trackBLinearPrimeScheduledVariance
              trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
              trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi omega j N} =
          Set.univ := by
        ext omega
        simp [hN]
    rw [hset]
    exact MeasurableSet.univ

/-- If the concrete variance-good event fails at stage `j`, then one scheduled
test point has variance below the target `V_j`. -/
theorem trackBLinearPrimeConcreteVarianceGood_compl_subset_exists_bad (j : ℕ) :
    (trackBLinearPrimeConcreteVarianceGood j)ᶜ ⊆
      ⋃ N ∈ trackBLinearPrimeMeshTestSet
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j,
        {omega : Omega |
          trackBLinearPrimeScheduledVariance
              trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
              trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi omega j N <
            trackBLinearPrimeConcreteV j} := by
  intro omega homega
  rw [trackBLinearPrimeConcreteVarianceGood] at homega
  by_contra hnot
  apply homega
  refine Set.mem_iInter.mpr ?_
  intro N hN
  by_contra hfloor
  have hbad :
      trackBLinearPrimeScheduledVariance
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
          trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi omega j N <
        trackBLinearPrimeConcreteV j := lt_of_not_ge hfloor
  exact hnot (Set.mem_iUnion₂.mpr ⟨N, hN, hbad⟩)

/-- Union-bound control of the concrete variance-good complement from
one-point variance lower-tail probabilities. -/
theorem measure_trackBLinearPrimeConcreteVarianceGood_compl_le_sum_single (j : ℕ) :
    mu (trackBLinearPrimeConcreteVarianceGood j)ᶜ ≤
      ∑ N ∈ trackBLinearPrimeMeshTestSet
          trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j,
        mu {omega : Omega |
          trackBLinearPrimeScheduledVariance
              trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
              trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi omega j N <
            trackBLinearPrimeConcreteV j} := by
  exact le_trans
    (measure_mono (trackBLinearPrimeConcreteVarianceGood_compl_subset_exists_bad j))
    (measure_biUnion_finset_le (μ := mu)
      (trackBLinearPrimeMeshTestSet trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j)
      fun N =>
        {omega : Omega |
          trackBLinearPrimeScheduledVariance
              trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
              trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi omega j N <
            trackBLinearPrimeConcreteV j})

/-- Layer-indexed characterization of the concrete variance-good event. -/
theorem mem_trackBLinearPrimeConcreteVarianceGood_iff_layer
    (omega : Omega) (j : ℕ) :
    omega ∈ trackBLinearPrimeConcreteVarianceGood j ↔
      ∀ r, r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j →
        trackBLinearPrimeConcreteV j ≤
          ∑ p ∈
            trackBFreshPrimeLayer
              (trackBLinearPrimeConcreteFreshLo j r) (trackBLinearPrimeConcreteFreshHi j r),
            (trackBLinearPrimeScheduledFreshCoeff
              trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
              trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
              omega j (trackBLinearPrimeConcretePoint j r) p) ^ 2 := by
  constructor
  · intro hgood r hr
    have hN :
        trackBLinearPrimeConcretePoint j r ∈
          trackBLinearPrimeMeshTestSet
            trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint j := by
      rw [mem_trackBLinearPrimeMeshTestSet]
      exact ⟨r, hr, rfl⟩
    have hv := (Set.mem_iInter.mp hgood (trackBLinearPrimeConcretePoint j r)) hN
    simpa [trackBLinearPrimeConcrete_scheduledVariance_eq_layer omega j r hr] using hv
  · intro hgood
    rw [trackBLinearPrimeConcreteVarianceGood]
    refine Set.mem_iInter.mpr ?_
    intro N hN
    rcases mem_trackBLinearPrimeMeshTestSet.mp hN with ⟨r, hr, hpoint⟩
    subst N
    rw [trackBLinearPrimeConcrete_scheduledVariance_eq_layer omega j r hr]
    exact hgood r hr

/-- The only non-scalar geometry fact still needed for the concrete schedule
with a configurable good event. -/
structure TrackBLinearPrimeConcreteWithGoodGeometryAnalyticFacts
    (good : ℕ → Set Omega) (failGood : ℕ → ℝ≥0∞) where
  variance_floor :
    ∀ omega j N,
      omega ∈ (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).good j →
      N ∈ trackBLinearPrimeMeshTestSet
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
        (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point j →
      (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).V j ≤
        trackBLinearPrimeScheduledVariance
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).Q
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).point
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshLo
          (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood).freshHi omega j N

/-- Layer-indexed version of the concrete with-good variance-floor input.

This is usually the easiest analytic statement to prove: for each scheduled
mesh index `r`, lower-bound the coefficient square sum over the single fresh
prime layer attached to `r`.  The theorem
`trackBLinearPrimeConcreteWithGoodGeometryAnalyticFacts_of_layerVariance`
turns it into the scheduled image-test-point formulation. -/
structure TrackBLinearPrimeConcreteWithGoodLayerVarianceAnalyticFacts
    (good : ℕ → Set Omega) (_failGood : ℕ → ℝ≥0∞) where
  variance_layer_floor :
    ∀ omega j r, omega ∈ good j →
      r ∈ trackBLinearPrimeMeshIndexSet trackBLinearPrimeConcreteQ j →
        trackBLinearPrimeConcreteV j ≤
          ∑ p ∈
            trackBFreshPrimeLayer
              (trackBLinearPrimeConcreteFreshLo j r) (trackBLinearPrimeConcreteFreshHi j r),
            (trackBLinearPrimeScheduledFreshCoeff
              trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
              trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
              omega j (trackBLinearPrimeConcretePoint j r) p) ^ 2

/-- Convert a layer-indexed concrete variance floor into the scheduled
with-good geometry analytic field. -/
def trackBLinearPrimeConcreteWithGoodGeometryAnalyticFacts_of_layerVariance
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeConcreteWithGoodLayerVarianceAnalyticFacts good failGood) :
    TrackBLinearPrimeConcreteWithGoodGeometryAnalyticFacts good failGood where
  variance_floor := by
    intro omega j N hgood hN
    rcases mem_trackBLinearPrimeMeshTestSet.mp hN with ⟨r, hr, hpoint⟩
    subst N
    change trackBLinearPrimeConcreteV j ≤
      trackBLinearPrimeScheduledVariance
        trackBLinearPrimeConcreteQ trackBLinearPrimeConcretePoint
        trackBLinearPrimeConcreteFreshLo trackBLinearPrimeConcreteFreshHi
        omega j (trackBLinearPrimeConcretePoint j r)
    rw [trackBLinearPrimeConcrete_scheduledVariance_eq_layer omega j r hr]
    exact h.variance_layer_floor omega j r hgood hr

/-- The concrete variance-good event makes the with-good geometry field
definitionally immediate.  The remaining geometry-side analytic task is then
only to bound the probability of this event's complement. -/
def trackBLinearPrimeConcreteWithGoodGeometryAnalyticFacts_of_varianceGood
    (failGood : ℕ → ℝ≥0∞) :
    TrackBLinearPrimeConcreteWithGoodGeometryAnalyticFacts
      trackBLinearPrimeConcreteVarianceGood failGood where
  variance_floor := by
    intro omega j N hgood hN
    exact (Set.mem_iInter.mp hgood N) hN

/-- Assemble concrete with-good geometry facts from the remaining variance
floor plus schedule arithmetic already proved. -/
def trackBLinearPrimeConcreteWithGoodGeometryFacts_of_analytic
    {good : ℕ → Set Omega} {failGood : ℕ → ℝ≥0∞}
    (h : TrackBLinearPrimeConcreteWithGoodGeometryAnalyticFacts good failGood) :
    TrackBLinearPrimeScheduleGeometryFacts
      (trackBLinearPrimeConcreteScheduleSpecWithGood good failGood) where
  variance_floor := h.variance_floor
  coeff_div_bound := trackBLinearPrimeConcrete_coeff_div_bound
  fresh_interval_disjoint := trackBLinearPrimeConcrete_fresh_interval_disjoint
  budget_nonneg := trackBLinearPrimeConcrete_rho_mul_V_nonneg

end Problem1144
end Erdos
