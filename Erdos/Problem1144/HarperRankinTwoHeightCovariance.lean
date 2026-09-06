import Erdos.Problem1144.HarperRankinTwoHeightBlockIndependence
import Erdos.Problem1144.HarperRankinVarianceWindow
import Erdos.Problem1144.HarperTwoHeightCovariance

open Finset MeasureTheory ProbabilityTheory Set Matrix Filter Topology
open scoped BigOperators

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Covariance arithmetic for the Rankin two-height law
-/

noncomputable def harperRankinTwoHeightCenteredSignVariance
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s : ℝ) : ℝ :=
  ∫ b, (Problem520.cubeSign b -
      harperRankinTwoHeightTiltBias p a t s) ^ 2
    ∂harperRankinTwoHeightCoin p hp a ha t s

theorem harperRankinTwoHeightCenteredSignVariance_eq_one_sub_sq
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ) :
    harperRankinTwoHeightCenteredSignVariance p hp a ha t s =
      1 - harperRankinTwoHeightTiltBias p a t s ^ 2 := by
  unfold harperRankinTwoHeightCenteredSignVariance
  rw [integral_harperRankinTwoHeightCoin]
  have hsum := harperRankinTwoHeightCoinWeight_false_add_true hp ha t s
  unfold harperRankinTwoHeightTiltBias
  simp only [Problem520.cubeSign, Bool.false_eq_true, if_false, if_true]
  nlinarith

theorem abs_harperRankinTwoHeightTiltBias_le_sixteen_inv_sqrt
    {p : ℕ} (hp : p.Prime) (hp16 : 16 ≤ p)
    {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    |harperRankinTwoHeightTiltBias p a t s| ≤
      16 * (Real.sqrt (p : ℝ))⁻¹ := by
  let r : ℝ := harperRankinEulerRadius p a
  let A : ℝ := harperRankinEulerNormalizer p a
  let M : ℝ := harperRankinTwoHeightPrimeNormalizer p a t s
  let ct : ℝ := Real.cos (t * Real.log (p : ℝ))
  let cs : ℝ := Real.cos (s * Real.log (p : ℝ))
  have hr0 : 0 ≤ r := harperRankinEulerRadius_nonneg p a
  have hrle : r ≤ (Real.sqrt (p : ℝ))⁻¹ :=
    harperRankinEulerRadius_le_inv_sqrt hp.one_le ha
  have hsqrtFour : (4 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    have h16 : (16 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp16
    have h := Real.sqrt_le_sqrt h16
    norm_num at h ⊢
    exact h
  have hinvQuarter : (Real.sqrt (p : ℝ))⁻¹ ≤ (1 / 4 : ℝ) := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hsqrtFour)
  have hrQuarter : r ≤ (1 / 4 : ℝ) := hrle.trans hinvQuarter
  have hAformula : A = 1 + r ^ 2 := by rfl
  have hA0 : 0 < A := harperRankinEulerNormalizer_pos p a
  have hAtwo : A ≤ 2 := by
    rw [hAformula]
    nlinarith [sq_nonneg r]
  have hctcs : -1 ≤ ct * cs := by
    have habs : |ct * cs| ≤ 1 := by
      calc
        |ct * cs| = |ct| * |cs| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul (Real.abs_cos_le_one _)
          (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    exact (abs_le.mp habs).1
  have hMformula : M = A ^ 2 + 4 * r ^ 2 * ct * cs := by
    dsimp only [M, A, r, ct, cs]
    rw [harperRankinTwoHeightPrimeNormalizer_eq_correlation]
  have hcross : -(4 * r ^ 2) ≤ 4 * r ^ 2 * ct * cs := by
    have := mul_le_mul_of_nonneg_left hctcs
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg r))
    nlinarith
  have hMlower : (3 / 4 : ℝ) ≤ M := by
    rw [hMformula, hAformula]
    nlinarith [sq_nonneg r, sq_nonneg (r ^ 2)]
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) hMlower
  have hsum : |2 * r * ct + 2 * r * cs| ≤ 4 * r := by
    calc
      |2 * r * ct + 2 * r * cs| ≤
          |2 * r * ct| + |2 * r * cs| := abs_add_le _ _
      _ = 2 * r * |ct| + 2 * r * |cs| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hr0]
      _ ≤ 2 * r * 1 + 2 * r * 1 := by
        gcongr <;> exact Real.abs_cos_le_one _
      _ = 4 * r := by ring
  have hnum : |A * (2 * r * ct + 2 * r * cs)| ≤ 8 * r := by
    rw [abs_mul, abs_of_pos hA0]
    calc
      A * |2 * r * ct + 2 * r * cs| ≤ A * (4 * r) := by gcongr
      _ ≤ 2 * (4 * r) := by gcongr
      _ = 8 * r := by ring
  rw [harperRankinTwoHeightTiltBias_eq hp ha]
  change |A * (2 * r * ct + 2 * r * cs) / M| ≤ _
  rw [abs_div, abs_of_pos hM]
  apply (div_le_iff₀ hM).2
  have hinv0 : 0 ≤ (Real.sqrt (p : ℝ))⁻¹ := by positivity
  calc
    |A * (2 * r * ct + 2 * r * cs)| ≤ 8 * r := hnum
    _ ≤ 8 * (Real.sqrt (p : ℝ))⁻¹ := by gcongr
    _ ≤ (16 * (Real.sqrt (p : ℝ))⁻¹) * M := by nlinarith

theorem harperRankinTwoHeightTiltBias_sq_le_twoFiftySix_inv
    {p : ℕ} (hp : p.Prime) (hp16 : 16 ≤ p)
    {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    harperRankinTwoHeightTiltBias p a t s ^ 2 ≤
      256 * (p : ℝ)⁻¹ := by
  have habs := abs_harperRankinTwoHeightTiltBias_le_sixteen_inv_sqrt
    hp hp16 ha t s
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt (by exact_mod_cast hp.pos.le)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) (by simpa using habs) 2
  rw [sq_abs] at hsq
  calc
    harperRankinTwoHeightTiltBias p a t s ^ 2 ≤
        (16 * (Real.sqrt (p : ℝ))⁻¹) ^ 2 := hsq
    _ = 256 * (p : ℝ)⁻¹ := by
      rw [mul_pow, inv_pow, hsqrtSq]
      norm_num

noncomputable def harperRankinTwoHeightPrimeCoefficient
    (p : ℕ) (a u : ℝ) : ℝ :=
  harperRankinEulerRadius p a * Real.cos (u * Real.log (p : ℝ))

theorem harperRankinTwoHeightPrimeCoefficient_mul
    {p : ℕ} (hp : 0 < p) (a u v : ℝ) :
    harperRankinTwoHeightPrimeCoefficient p a u *
        harperRankinTwoHeightPrimeCoefficient p a v =
      Real.cos (u * Real.log (p : ℝ)) *
        Real.cos (v * Real.log (p : ℝ)) * (p : ℝ)⁻¹ *
          (p : ℝ) ^ (-a) := by
  unfold harperRankinTwoHeightPrimeCoefficient
  rw [show
      (harperRankinEulerRadius p a * Real.cos (u * Real.log (p : ℝ))) *
          (harperRankinEulerRadius p a * Real.cos (v * Real.log (p : ℝ))) =
        harperRankinEulerRadius p a ^ 2 *
          (Real.cos (u * Real.log (p : ℝ)) *
            Real.cos (v * Real.log (p : ℝ))) by ring,
    harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg hp a]
  ring

noncomputable def harperRankinTwoHeightBlockCoordinateCovariance
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s u v : ℝ) : ℝ :=
  ∑ p ∈ S,
    harperRankinTwoHeightCenteredSignVariance p.1
        (Nat.prime_of_mem_primesBelow p.property) a ha t s *
      harperRankinTwoHeightPrimeCoefficient p.1 a u *
      harperRankinTwoHeightPrimeCoefficient p.1 a v

theorem harperRankinTwoHeightProjectedPrimeVariance_eq
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s v w : ℝ) :
    harperRankinTwoHeightProjectedPrimeVariance p hp a ha t s v w =
      v ^ 2 * harperRankinTwoHeightCenteredSignVariance p hp a ha t s *
          harperRankinTwoHeightPrimeCoefficient p a t ^ 2 +
        2 * v * w * harperRankinTwoHeightCenteredSignVariance p hp a ha t s *
          harperRankinTwoHeightPrimeCoefficient p a t *
          harperRankinTwoHeightPrimeCoefficient p a s +
        w ^ 2 * harperRankinTwoHeightCenteredSignVariance p hp a ha t s *
          harperRankinTwoHeightPrimeCoefficient p a s ^ 2 := by
  let q : Bool → ℝ := fun b ↦
    Problem520.cubeSign b - harperRankinTwoHeightTiltBias p a t s
  let ct : ℝ := harperRankinTwoHeightPrimeCoefficient p a t
  let cs : ℝ := harperRankinTwoHeightPrimeCoefficient p a s
  have hpoint (b : Bool) :
      harperRankinTwoHeightProjectedPrimeIncrement p a t s v w b =
        q b * (v * ct + w * cs) := by
    unfold harperRankinTwoHeightProjectedPrimeIncrement
      harperRankinTwoHeightPrimeFluctuation
    dsimp only [q, ct, cs, harperRankinTwoHeightPrimeCoefficient]
    ring_nf
  unfold harperRankinTwoHeightProjectedPrimeVariance
  simp_rw [hpoint, mul_pow]
  rw [integral_mul_const]
  change
    harperRankinTwoHeightCenteredSignVariance p hp a ha t s *
        (v * ct + w * cs) ^ 2 = _
  dsimp only [ct, cs]
  ring

theorem harperRankinTwoHeightProjectedBlockVariance_eq_coordinateCovariance
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ) :
    harperRankinTwoHeightProjectedBlockVariance y S a ha t s v w =
      v ^ 2 * harperRankinTwoHeightBlockCoordinateCovariance
          y S a ha t s t t +
        2 * v * w * harperRankinTwoHeightBlockCoordinateCovariance
          y S a ha t s t s +
        w ^ 2 * harperRankinTwoHeightBlockCoordinateCovariance
          y S a ha t s s s := by
  unfold harperRankinTwoHeightProjectedBlockVariance
    harperRankinTwoHeightBlockCoordinateCovariance
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hpS
  rw [harperRankinTwoHeightProjectedPrimeVariance_eq]
  ring

/-- The shifted centered covariance at one prime differs from its radially
weighted bare cosine kernel only by a summable inverse-square term. -/
theorem abs_harperRankinTwoHeightPrimeCoordinateCovariance_sub_weightedCosine_le
    {p : ℕ} (hp : p.Prime) (hp16 : 16 ≤ p)
    {a : ℝ} (ha : 0 ≤ a) (t s u v : ℝ) :
    |harperRankinTwoHeightCenteredSignVariance p hp a ha t s *
          harperRankinTwoHeightPrimeCoefficient p a u *
          harperRankinTwoHeightPrimeCoefficient p a v -
        Real.cos (u * Real.log (p : ℝ)) *
          Real.cos (v * Real.log (p : ℝ)) * (p : ℝ)⁻¹ *
            (p : ℝ) ^ (-a)| ≤
      256 * (p : ℝ)⁻¹ ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hz0 : 0 ≤ (p : ℝ) ^ (-a) := Real.rpow_nonneg hpR.le _
  have hz1 : (p : ℝ) ^ (-a) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hpOne (neg_nonpos.mpr ha)
  rw [harperRankinTwoHeightCenteredSignVariance_eq_one_sub_sq,
    mul_assoc, harperRankinTwoHeightPrimeCoefficient_mul hp.pos]
  let q := harperRankinTwoHeightTiltBias p a t s
  let c := Real.cos (u * Real.log (p : ℝ)) *
    Real.cos (v * Real.log (p : ℝ))
  have hc : |c| ≤ 1 := by
    dsimp [c]
    rw [abs_mul]
    calc
      |Real.cos (u * Real.log (p : ℝ))| *
          |Real.cos (v * Real.log (p : ℝ))| ≤ 1 * 1 :=
        mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
          (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hq := harperRankinTwoHeightTiltBias_sq_le_twoFiftySix_inv
    hp hp16 ha t s
  have hq0 : 0 ≤ q ^ 2 := sq_nonneg _
  have hinv0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  change |(1 - q ^ 2) * (c * (p : ℝ)⁻¹ * (p : ℝ) ^ (-a)) -
      c * (p : ℝ)⁻¹ * (p : ℝ) ^ (-a)| ≤ _
  rw [show (1 - q ^ 2) * (c * (p : ℝ)⁻¹ * (p : ℝ) ^ (-a)) -
      c * (p : ℝ)⁻¹ * (p : ℝ) ^ (-a) =
        -(q ^ 2 * c * (p : ℝ)⁻¹ * (p : ℝ) ^ (-a)) by ring,
    abs_neg, abs_mul, abs_mul, abs_mul, abs_of_nonneg hq0,
    abs_of_pos (inv_pos.mpr hpR), abs_of_nonneg hz0]
  calc
    q ^ 2 * |c| * (p : ℝ)⁻¹ * (p : ℝ) ^ (-a) ≤
        (256 * (p : ℝ)⁻¹) * 1 * (p : ℝ)⁻¹ * 1 := by gcongr
    _ = 256 * (p : ℝ)⁻¹ ^ 2 := by ring

/-- With radial weight at least `19/20`, the shifted one-prime covariance
is uniformly close to the already analysed critical covariance. -/
theorem abs_harperRankinTwoHeightPrimeCoordinateCovariance_sub_critical_le
    {p : ℕ} (hp : p.Prime) (hp16 : 16 ≤ p)
    {a : ℝ} (ha : 0 ≤ a)
    (hweight : (19 / 20 : ℝ) ≤ (p : ℝ) ^ (-a))
    (t s u v : ℝ) :
    |harperRankinTwoHeightCenteredSignVariance p hp a ha t s *
          harperRankinTwoHeightPrimeCoefficient p a u *
          harperRankinTwoHeightPrimeCoefficient p a v -
        harperTwoHeightCenteredSignVariance p hp t s *
          harperTwoHeightPrimeCoefficient p u *
          harperTwoHeightPrimeCoefficient p v| ≤
      (1 / 20 : ℝ) * (p : ℝ)⁻¹ +
        512 * (p : ℝ)⁻¹ ^ 2 := by
  let c := Real.cos (u * Real.log (p : ℝ)) *
    Real.cos (v * Real.log (p : ℝ))
  let z := (p : ℝ) ^ (-a)
  let weighted := c * (p : ℝ)⁻¹ * z
  let bare := c * (p : ℝ)⁻¹
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hz0 : 0 ≤ z := by dsimp [z]; exact Real.rpow_nonneg hpR.le _
  have hz1 : z ≤ 1 := by
    dsimp [z]
    exact Real.rpow_le_one_of_one_le_of_nonpos hpOne (neg_nonpos.mpr ha)
  have hc : |c| ≤ 1 := by
    dsimp [c]
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
      (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hzw : |z - 1| ≤ (1 / 20 : ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hz1)]
    have hzLower : (19 / 20 : ℝ) ≤ z := by simpa only [z] using hweight
    linarith
  have hweighted : |weighted - bare| ≤
      (1 / 20 : ℝ) * (p : ℝ)⁻¹ := by
    have hinv0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
    dsimp [weighted, bare]
    rw [show c * (p : ℝ)⁻¹ * z - c * (p : ℝ)⁻¹ =
        c * (p : ℝ)⁻¹ * (z - 1) by ring,
      abs_mul, abs_mul, abs_of_nonneg hinv0]
    calc
      |c| * (p : ℝ)⁻¹ * |z - 1| ≤
          1 * (p : ℝ)⁻¹ * (1 / 20 : ℝ) := by gcongr
      _ = (1 / 20 : ℝ) * (p : ℝ)⁻¹ := by ring
  have hshift :=
    abs_harperRankinTwoHeightPrimeCoordinateCovariance_sub_weightedCosine_le
      hp hp16 ha t s u v
  have hcritical :=
    abs_harperTwoHeightPrimeCoordinateCovariance_sub_cosine_le
      hp hp16 t s u v
  let shifted :=
    harperRankinTwoHeightCenteredSignVariance p hp a ha t s *
      harperRankinTwoHeightPrimeCoefficient p a u *
      harperRankinTwoHeightPrimeCoefficient p a v
  let critical :=
    harperTwoHeightCenteredSignVariance p hp t s *
      harperTwoHeightPrimeCoefficient p u *
      harperTwoHeightPrimeCoefficient p v
  change |shifted - critical| ≤ _
  change |shifted - weighted| ≤ _ at hshift
  change |critical - bare| ≤ _ at hcritical
  calc
    |shifted - critical| ≤
        |shifted - weighted| + |weighted - bare| + |bare - critical| := by
      rw [show shifted - critical =
          (shifted - weighted) + (weighted - bare) + (bare - critical) by ring]
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 256 * (p : ℝ)⁻¹ ^ 2 +
          (1 / 20 : ℝ) * (p : ℝ)⁻¹ +
          256 * (p : ℝ)⁻¹ ^ 2 := by
      exact add_le_add (add_le_add hshift hweighted)
        (by simpa only [abs_sub_comm] using hcritical)
    _ = (1 / 20 : ℝ) * (p : ℝ)⁻¹ +
          512 * (p : ℝ)⁻¹ ^ 2 := by ring

/-- Blockwise covariance stability under a `19/20` Rankin radial lower
bound.  Only a small reciprocal-mass loss and a summable square-mass loss
remain. -/
theorem abs_harperRankinTwoHeightBlockCoordinateCovariance_sub_critical_le
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    {a : ℝ} (ha : 0 ≤ a)
    (h16 : ∀ p ∈ S, 16 ≤ p.1)
    (hweight : ∀ p ∈ S, (19 / 20 : ℝ) ≤ (p.1 : ℝ) ^ (-a))
    (t s u v : ℝ) :
    |harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s u v -
        harperTwoHeightBlockCoordinateCovariance y S t s u v| ≤
      (1 / 20 : ℝ) * (∑ p ∈ S, (p.1 : ℝ)⁻¹) +
        512 * ∑ p ∈ S, (p.1 : ℝ)⁻¹ ^ 2 := by
  unfold harperRankinTwoHeightBlockCoordinateCovariance
    harperTwoHeightBlockCoordinateCovariance
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ S,
        (harperRankinTwoHeightCenteredSignVariance p.1
              (Nat.prime_of_mem_primesBelow p.property) a ha t s *
            harperRankinTwoHeightPrimeCoefficient p.1 a u *
            harperRankinTwoHeightPrimeCoefficient p.1 a v -
          harperTwoHeightCenteredSignVariance p.1
              (Nat.prime_of_mem_primesBelow p.property) t s *
            harperTwoHeightPrimeCoefficient p.1 u *
            harperTwoHeightPrimeCoefficient p.1 v)| ≤
        ∑ p ∈ S,
          |harperRankinTwoHeightCenteredSignVariance p.1
                (Nat.prime_of_mem_primesBelow p.property) a ha t s *
              harperRankinTwoHeightPrimeCoefficient p.1 a u *
              harperRankinTwoHeightPrimeCoefficient p.1 a v -
            harperTwoHeightCenteredSignVariance p.1
                (Nat.prime_of_mem_primesBelow p.property) t s *
              harperTwoHeightPrimeCoefficient p.1 u *
              harperTwoHeightPrimeCoefficient p.1 v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S,
        ((1 / 20 : ℝ) * (p.1 : ℝ)⁻¹ +
          512 * (p.1 : ℝ)⁻¹ ^ 2) := by
      apply Finset.sum_le_sum
      intro p hpS
      exact abs_harperRankinTwoHeightPrimeCoordinateCovariance_sub_critical_le
        (Nat.prime_of_mem_primesBelow p.property)
        (h16 p hpS)
        ha (hweight p hpS) t s u v
    _ = (1 / 20 : ℝ) * (∑ p ∈ S, (p.1 : ℝ)⁻¹) +
          512 * ∑ p ∈ S, (p.1 : ℝ)⁻¹ ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- After a fixed radial gap, every sufficiently late scheduled shifted
covariance block is within `1/16` of the critical covariance block. -/
theorem exists_gap_eventually_harperRankinTwoHeightScheduledCovariance_close :
    ∀ V : ℝ, 0 ≤ V →
      ∃ gap J : ℕ, ∀ j y : ℕ, J ≤ j →
        Problem520.harperBlockEndpoint (j + gap + 1) ≤ y →
          ∀ ha : 0 ≤ 4 * V / Real.log (y : ℝ), ∀ t s u v : ℝ,
            |harperRankinTwoHeightBlockCoordinateCovariance y
                  (Problem520.harperScheduledPrimeBlock y j)
                  (4 * V / Real.log (y : ℝ))
                  ha
                  t s u v -
                harperTwoHeightBlockCoordinateCovariance y
                  (Problem520.harperScheduledPrimeBlock y j) t s u v| <
              (1 / 16 : ℝ) := by
  intro V hV
  obtain ⟨gap, hgap⟩ := exists_harperRankinStrongRadialGap V
  obtain ⟨Jmass, hmass⟩ :=
    Problem520.exists_eventually_harperScheduledPrimeBlock_inv_close_log_two
      (by norm_num : (0 : ℝ) < 1 / 1000)
  obtain ⟨c, hc, C, hC, Jerr, herr⟩ :=
    Problem520.exists_harperScheduledSummableBlockErrorBounds 1
  have hsquareTendsto : Tendsto Problem520.harperScheduledSquareEnvelope
      atTop (nhds 0) :=
    Problem520.summable_harperScheduledSquareEnvelope.tendsto_atTop_zero
  have hsquareEventually : ∀ᶠ j : ℕ in atTop,
      Problem520.harperScheduledSquareEnvelope j <
        (1 / 32768 : ℝ) :=
    (tendsto_order.mp hsquareTendsto).2 _ (by norm_num)
  obtain ⟨Jsquare, hsquare⟩ := eventually_atTop.1 hsquareEventually
  refine ⟨gap, max Jmass (max Jerr Jsquare), ?_⟩
  intro j y hj hy ha t s u v
  have hjmass : Jmass ≤ j := by omega
  have hjerr : Jerr ≤ j := by omega
  have hjsquare : Jsquare ≤ j := by omega
  have hyNear : Problem520.harperBlockEndpoint (j + 1) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans hy
  have hyOne : (1 : ℕ) < y := by
    have hbase :=
      Problem520.harperBlockEndpoint_ge_sixteen (j + gap + 1)
    omega
  have hclose :=
    abs_harperRankinTwoHeightBlockCoordinateCovariance_sub_critical_le
      y (Problem520.harperScheduledPrimeBlock y j) ha
      (fun p hpS ↦ by
        have :=
          Problem520.sixtyFour_le_prime_of_mem_harperScheduledPrimeBlock hpS
        omega)
      (fun p hpS ↦
        harperRankinScheduledPrime_radialWeight_of_strongGap
          hgap hy p hpS)
      t s u v
  have hmassj := hmass j hjmass y hyNear
  change |Problem520.harperScheduledReciprocalMass y j - Real.log 2| <
    (1 / 1000 : ℝ) at hmassj
  have hmassUpper :
      Problem520.harperScheduledReciprocalMass y j <
        (901 / 1000 : ℝ) := by
    have := lt_of_abs_lt hmassj
    nlinarith [Real.log_two_lt_d9]
  have hsquareBound :
      Problem520.harperScheduledSquareMass y j ≤
        Problem520.harperScheduledSquareEnvelope j :=
    (herr j hjerr y hyNear).2.2
  have hsquareSmall := hsquare j hjsquare
  change |harperRankinTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j)
        (4 * V / Real.log (y : ℝ)) ha t s u v -
      harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) t s u v| ≤
    (1 / 20 : ℝ) * Problem520.harperScheduledReciprocalMass y j +
      512 * Problem520.harperScheduledSquareMass y j at hclose
  nlinarith

theorem harperRankinTwoHeightProjectedBlockVariance_ge_eighth_of_marginals_covariance
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ)
    (ht : (1 / 4 : ℝ) ≤
      harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s t t)
    (hs : (1 / 4 : ℝ) ≤
      harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s s s)
    (hcov : |harperRankinTwoHeightBlockCoordinateCovariance
      y S a ha t s t s| ≤ (1 / 8 : ℝ)) :
    (1 / 8 : ℝ) * (v ^ 2 + w ^ 2) ≤
      harperRankinTwoHeightProjectedBlockVariance y S a ha t s v w := by
  let q := harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s t s
  have hamgm : 2 * |v| * |w| ≤ v ^ 2 + w ^ 2 := by
    nlinarith [sq_nonneg (|v| - |w|), sq_abs v, sq_abs w]
  have hcrossAbs : |2 * v * w * q| ≤
      (1 / 8 : ℝ) * (v ^ 2 + w ^ 2) := by
    calc
      |2 * v * w * q| = (2 * |v| * |w|) * |q| := by
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 * |v| * |w|) * (1 / 8 : ℝ) := by gcongr
      _ ≤ (v ^ 2 + w ^ 2) * (1 / 8 : ℝ) := by gcongr
      _ = (1 / 8 : ℝ) * (v ^ 2 + w ^ 2) := by ring
  have hcross := neg_le_of_abs_le hcrossAbs
  have ht' : (1 / 4 : ℝ) * v ^ 2 ≤
      v ^ 2 * harperRankinTwoHeightBlockCoordinateCovariance
        y S a ha t s t t := by
    nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg v)]
  have hs' : (1 / 4 : ℝ) * w ^ 2 ≤
      w ^ 2 * harperRankinTwoHeightBlockCoordinateCovariance
        y S a ha t s s s := by
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg w)]
  rw [harperRankinTwoHeightProjectedBlockVariance_eq_coordinateCovariance]
  dsimp only [q] at hcross
  nlinarith

#print axioms Erdos.Problem1144.harperRankinTwoHeightCenteredSignVariance_eq_one_sub_sq
#print axioms Erdos.Problem1144.abs_harperRankinTwoHeightTiltBias_le_sixteen_inv_sqrt
#print axioms Erdos.Problem1144.harperRankinTwoHeightProjectedBlockVariance_eq_coordinateCovariance
#print axioms Erdos.Problem1144.harperRankinTwoHeightProjectedBlockVariance_ge_eighth_of_marginals_covariance

end
end Problem1144
end Erdos
