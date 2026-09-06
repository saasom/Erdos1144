import Erdos.Problem1144.HarperTwoHeightGaussianLaw
import Erdos.Problem520.HarperPrimeBlockArithmetic
import Erdos.Problem520.HarperCentralBandMoments

open Finset MeasureTheory ProbabilityTheory Set Matrix Filter Topology
open scoped BigOperators

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Exact covariance arithmetic for the two-height Gaussian

This file connects the covariance matrix used by the bivariate Gaussian
comparison to the scheduled reciprocal-prime cosine sums.  The centered-sign
variance is exactly `1 - bias^2`; the bias-squared correction is summable on
scheduled prime blocks.  Thus the only nonsummable off-diagonal term is the
difference-frequency cosine kernel, whose strong-PNT estimate detects the
coherence scale `|t-s| * log(BlockEndpoint j) ≍ 1`.
-/

/-- A two-point sign with mean `m` has centered variance `1-m^2`. -/
theorem harperTwoHeightCenteredSignVariance_eq_one_sub_sq
    (p : Nat) (hp : p.Prime) (t s : Real) :
    harperTwoHeightCenteredSignVariance p hp t s =
      1 - harperTwoHeightTiltBias p t s ^ (2 : Nat) := by
  unfold harperTwoHeightCenteredSignVariance
  rw [integral_harperTwoHeightCoin]
  have hsum := harperTwoHeightCoinWeight_false_add_true hp t s
  unfold harperTwoHeightTiltBias
  simp only [Problem520.cubeSign, Bool.false_eq_true, if_false, if_true]
  nlinarith

theorem harperTwoHeightCenteredSignVariance_le_one
    (p : Nat) (hp : p.Prime) (t s : Real) :
    harperTwoHeightCenteredSignVariance p hp t s ≤ 1 := by
  rw [harperTwoHeightCenteredSignVariance_eq_one_sub_sq]
  exact sub_le_self _ (sq_nonneg _)

/-- On the scheduled prime range the product tilt still has bias
`O(p^{-1/2})`.  The deliberately loose constant makes the later summable
correction completely elementary. -/
theorem abs_harperTwoHeightTiltBias_le_sixteen_inv_sqrt
    {p : Nat} (hp : p.Prime) (hp16 : 16 ≤ p) (t s : Real) :
    |harperTwoHeightTiltBias p t s| ≤
      16 * (Real.sqrt (p : Real))⁻¹ := by
  let x : Real := p
  let A : Real := 1 + x⁻¹
  let M : Real := harperTwoHeightPrimeNormalizer p t s
  let ct : Real := Real.cos (t * Real.log x)
  let cs : Real := Real.cos (s * Real.log x)
  have hx : 0 < x := by dsimp [x]; exact_mod_cast hp.pos
  have hx16 : (16 : Real) ≤ x := by dsimp [x]; exact_mod_cast hp16
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hinv0 : 0 ≤ x⁻¹ := by positivity
  have hinv16 : x⁻¹ ≤ (1 / 16 : Real) := by
    have h := one_div_le_one_div_of_le
      (a := (16 : Real)) (b := x) (by norm_num) hx16
    simpa only [one_div] using h
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hAone : 1 ≤ A := by dsimp [A]; linarith
  have hAtwo : A ≤ 2 := by dsimp [A]; linarith
  have hctcs : -1 ≤ ct * cs := by
    have habs : |ct * cs| ≤ 1 := by
      calc
        |ct * cs| = |ct| * |cs| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul (Real.abs_cos_le_one _)
          (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    exact (abs_le.mp habs).1
  have hMformula : M = A ^ (2 : Nat) + 4 * ct * cs * x⁻¹ := by
    dsimp only [M]
    rw [harperTwoHeightPrimeNormalizer_eq_correlation hp]
  have hcross : -(4 * x⁻¹) ≤ 4 * ct * cs * x⁻¹ := by
    have := mul_le_mul_of_nonneg_right hctcs hinv0
    nlinarith
  have hMlower : (3 / 4 : Real) ≤ M := by
    rw [hMformula]
    have hAsq : 1 ≤ A ^ (2 : Nat) := by nlinarith
    nlinarith
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) hMlower
  have hsum :
      |2 * ct / Real.sqrt x + 2 * cs / Real.sqrt x| ≤
        4 * (Real.sqrt x)⁻¹ := by
    have hct : |2 * ct / Real.sqrt x| ≤
        2 * (Real.sqrt x)⁻¹ := by
      calc
        |2 * ct / Real.sqrt x| = |2 * ct| / Real.sqrt x := by
          rw [abs_div, abs_of_pos hsqrt]
        _ ≤ 2 / Real.sqrt x := by
          apply div_le_div_of_nonneg_right _ hsqrt.le
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
          nlinarith [Real.abs_cos_le_one (t * Real.log x)]
        _ = 2 * (Real.sqrt x)⁻¹ := by rw [div_eq_mul_inv]
    have hcs : |2 * cs / Real.sqrt x| ≤
        2 * (Real.sqrt x)⁻¹ := by
      calc
        |2 * cs / Real.sqrt x| = |2 * cs| / Real.sqrt x := by
          rw [abs_div, abs_of_pos hsqrt]
        _ ≤ 2 / Real.sqrt x := by
          apply div_le_div_of_nonneg_right _ hsqrt.le
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
          nlinarith [Real.abs_cos_le_one (s * Real.log x)]
        _ = 2 * (Real.sqrt x)⁻¹ := by rw [div_eq_mul_inv]
    calc
      |2 * ct / Real.sqrt x + 2 * cs / Real.sqrt x| ≤
          |2 * ct / Real.sqrt x| + |2 * cs / Real.sqrt x| :=
        abs_add_le _ _
      _ ≤ 2 * (Real.sqrt x)⁻¹ + 2 * (Real.sqrt x)⁻¹ :=
        add_le_add hct hcs
      _ = 4 * (Real.sqrt x)⁻¹ := by ring
  have hnum :
      |A * (2 * ct / Real.sqrt x + 2 * cs / Real.sqrt x)| ≤
        8 * (Real.sqrt x)⁻¹ := by
    rw [abs_mul, abs_of_pos hA0]
    calc
      A * |2 * ct / Real.sqrt x + 2 * cs / Real.sqrt x| ≤
          A * (4 * (Real.sqrt x)⁻¹) :=
        mul_le_mul_of_nonneg_left hsum hA0.le
      _ ≤ 2 * (4 * (Real.sqrt x)⁻¹) :=
        mul_le_mul_of_nonneg_right hAtwo (by positivity)
      _ = 8 * (Real.sqrt x)⁻¹ := by ring
  rw [harperTwoHeightTiltBias_eq hp]
  change |A * (2 * ct / Real.sqrt x + 2 * cs / Real.sqrt x) / M| ≤ _
  rw [abs_div, abs_of_pos hM]
  apply (div_le_iff₀ hM).2
  have hinvsqrt : 0 ≤ (Real.sqrt x)⁻¹ := by positivity
  calc
    |A * (2 * ct / Real.sqrt x + 2 * cs / Real.sqrt x)| ≤
        8 * (Real.sqrt x)⁻¹ := hnum
    _ ≤ (16 * (Real.sqrt x)⁻¹) * M := by nlinarith

theorem harperTwoHeightTiltBias_sq_le_twoFiftySix_inv
    {p : Nat} (hp : p.Prime) (hp16 : 16 ≤ p) (t s : Real) :
    harperTwoHeightTiltBias p t s ^ (2 : Nat) ≤
      256 * (p : Real)⁻¹ := by
  have habs := abs_harperTwoHeightTiltBias_le_sixteen_inv_sqrt
    hp hp16 t s
  have hsqrt0 : 0 ≤ Real.sqrt (p : Real) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (p : Real) ^ (2 : Nat) = (p : Real) :=
    Real.sq_sqrt (by exact_mod_cast hp.pos.le)
  have hsq := pow_le_pow_left₀ (abs_nonneg _)
    (by simpa using habs) 2
  rw [sq_abs] at hsq
  calc
    harperTwoHeightTiltBias p t s ^ (2 : Nat) ≤
        (16 * (Real.sqrt (p : Real))⁻¹) ^ (2 : Nat) := hsq
    _ = 256 * (p : Real)⁻¹ := by
      rw [mul_pow, inv_pow, hsqrtSq]
      norm_num

/-- Scalar covariance of the exact centered linear block at two observation
heights. -/
noncomputable def harperTwoHeightBlockCoordinateCovariance
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s u v : Real) : Real :=
  ∑ p ∈ S,
    harperTwoHeightCenteredSignVariance p.1
        (Nat.prime_of_mem_primesBelow p.property) t s *
      harperTwoHeightPrimeCoefficient p.1 u *
      harperTwoHeightPrimeCoefficient p.1 v

theorem harperTwoHeightBlockCovarianceMatrix_apply
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) (i k : Bool) :
    harperTwoHeightBlockCovarianceMatrix y S t s i k =
      harperTwoHeightBlockCoordinateCovariance y S t s
        (if i then s else t) (if k then s else t) := by
  classical
  unfold harperTwoHeightBlockCovarianceMatrix
    harperTwoHeightBlockCoordinateCovariance
    harperTwoHeightPrimeCoefficientVector
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro p hpS
  cases i <;> cases k <;> simp [Matrix.vecMulVec, mul_assoc]

/-- Scalar expansion of the projected variance in terms of the two diagonal
variances and the off-diagonal covariance. -/
theorem harperTwoHeightProjectedBlockVariance_eq_coordinateCovariance
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) :
    harperTwoHeightProjectedBlockVariance y S t s v w =
      v ^ (2 : Nat) *
          harperTwoHeightBlockCoordinateCovariance y S t s t t +
        2 * v * w *
          harperTwoHeightBlockCoordinateCovariance y S t s t s +
        w ^ (2 : Nat) *
          harperTwoHeightBlockCoordinateCovariance y S t s s s := by
  classical
  unfold harperTwoHeightProjectedBlockVariance
    harperTwoHeightBlockCoordinateCovariance
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hpS
  rw [harperTwoHeightProjectedPrimeVariance_eq]
  ring

/-- A lower bound on both marginal variances together with a small
off-diagonal covariance gives a uniform lower eigenvalue for the exact
two-height covariance matrix. -/
theorem harperTwoHeightProjectedBlockVariance_ge_eighth_of_marginals_covariance
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real)
    (ht : (1 / 4 : Real) ≤
      harperTwoHeightBlockCoordinateCovariance y S t s t t)
    (hs : (1 / 4 : Real) ≤
      harperTwoHeightBlockCoordinateCovariance y S t s s s)
    (hcov : |harperTwoHeightBlockCoordinateCovariance y S t s t s| ≤
      (1 / 8 : Real)) :
    (1 / 8 : Real) * (v ^ (2 : Nat) + w ^ (2 : Nat)) ≤
      harperTwoHeightProjectedBlockVariance y S t s v w := by
  let q := harperTwoHeightBlockCoordinateCovariance y S t s t s
  have hamgm : 2 * |v| * |w| ≤ v ^ (2 : Nat) + w ^ (2 : Nat) := by
    nlinarith [sq_nonneg (|v| - |w|), sq_abs v, sq_abs w]
  have hcrossAbs : |2 * v * w * q| ≤
      (1 / 8 : Real) * (v ^ (2 : Nat) + w ^ (2 : Nat)) := by
    calc
      |2 * v * w * q| = (2 * |v| * |w|) * |q| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
      _ ≤ (2 * |v| * |w|) * (1 / 8 : Real) := by
        gcongr
      _ ≤ (v ^ (2 : Nat) + w ^ (2 : Nat)) * (1 / 8 : Real) := by
        gcongr
      _ = (1 / 8 : Real) * (v ^ (2 : Nat) + w ^ (2 : Nat)) := by ring
  have hcross := neg_le_of_abs_le hcrossAbs
  have ht' : (1 / 4 : Real) * v ^ (2 : Nat) ≤
      v ^ (2 : Nat) *
        harperTwoHeightBlockCoordinateCovariance y S t s t t := by
    nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg v)]
  have hs' : (1 / 4 : Real) * w ^ (2 : Nat) ≤
      w ^ (2 : Nat) *
        harperTwoHeightBlockCoordinateCovariance y S t s s s := by
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg w)]
  rw [harperTwoHeightProjectedBlockVariance_eq_coordinateCovariance]
  dsimp only [q] at hcross
  nlinarith

theorem harperTwoHeightPrimeCoefficient_mul
    {p : Nat} (hp : 0 < p) (u v : Real) :
    harperTwoHeightPrimeCoefficient p u *
        harperTwoHeightPrimeCoefficient p v =
      Real.cos (u * Real.log (p : Real)) *
        Real.cos (v * Real.log (p : Real)) * (p : Real)⁻¹ := by
  have hpR : (0 : Real) < p := by exact_mod_cast hp
  have hsqrtSq : Real.sqrt (p : Real) ^ (2 : Nat) = (p : Real) :=
    Real.sq_sqrt hpR.le
  unfold harperTwoHeightPrimeCoefficient
  field_simp [(Real.sqrt_pos.2 hpR).ne']
  rw [hsqrtSq]
  ring

/-- Removing the two-height bias changes one prime covariance by only
`O(p^{-2})`. -/
theorem abs_harperTwoHeightPrimeCoordinateCovariance_sub_cosine_le
    {p : Nat} (hp : p.Prime) (hp16 : 16 ≤ p)
    (t s u v : Real) :
    |harperTwoHeightCenteredSignVariance p hp t s *
          harperTwoHeightPrimeCoefficient p u *
          harperTwoHeightPrimeCoefficient p v -
        Real.cos (u * Real.log (p : Real)) *
          Real.cos (v * Real.log (p : Real)) * (p : Real)⁻¹| ≤
      256 * (p : Real)⁻¹ ^ (2 : Nat) := by
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  rw [harperTwoHeightCenteredSignVariance_eq_one_sub_sq, mul_assoc,
    harperTwoHeightPrimeCoefficient_mul hp.pos]
  let q := harperTwoHeightTiltBias p t s
  let c := Real.cos (u * Real.log (p : Real)) *
    Real.cos (v * Real.log (p : Real))
  have hc : |c| ≤ 1 := by
    dsimp [c]
    rw [abs_mul]
    calc
      |Real.cos (u * Real.log (p : Real))| *
          |Real.cos (v * Real.log (p : Real))| ≤ 1 * 1 :=
        mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
          (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hq := harperTwoHeightTiltBias_sq_le_twoFiftySix_inv
    hp hp16 t s
  have hq0 : 0 ≤ q ^ (2 : Nat) := sq_nonneg _
  have hinv0 : 0 ≤ (p : Real)⁻¹ := by positivity
  change |(1 - q ^ (2 : Nat)) * (c * (p : Real)⁻¹) -
      c * (p : Real)⁻¹| ≤ _
  rw [show (1 - q ^ (2 : Nat)) * (c * (p : Real)⁻¹) -
      c * (p : Real)⁻¹ = -(q ^ (2 : Nat) * c * (p : Real)⁻¹) by ring,
    abs_neg, abs_mul, abs_mul, abs_of_nonneg hq0,
    abs_of_pos (inv_pos.mpr hpR)]
  calc
    q ^ (2 : Nat) * |c| * (p : Real)⁻¹ ≤
        (256 * (p : Real)⁻¹) * 1 * (p : Real)⁻¹ := by gcongr
    _ = 256 * (p : Real)⁻¹ ^ (2 : Nat) := by ring

/-- The exact block covariance differs from the bare cosine-product sum by
the scheduled inverse-square mass only. -/
theorem abs_harperTwoHeightBlockCoordinateCovariance_sub_cosineSum_le
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (h16 : ∀ p ∈ S, 16 ≤ p.1) (t s u v : Real) :
    |harperTwoHeightBlockCoordinateCovariance y S t s u v -
        ∑ p ∈ S,
          Real.cos (u * Real.log (p.1 : Real)) *
            Real.cos (v * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹| ≤
      256 * ∑ p ∈ S, (p.1 : Real)⁻¹ ^ (2 : Nat) := by
  unfold harperTwoHeightBlockCoordinateCovariance
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ S,
        (harperTwoHeightCenteredSignVariance p.1
              (Nat.prime_of_mem_primesBelow p.property) t s *
            harperTwoHeightPrimeCoefficient p.1 u *
            harperTwoHeightPrimeCoefficient p.1 v -
          Real.cos (u * Real.log (p.1 : Real)) *
            Real.cos (v * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹)| ≤
        ∑ p ∈ S,
          |harperTwoHeightCenteredSignVariance p.1
                (Nat.prime_of_mem_primesBelow p.property) t s *
              harperTwoHeightPrimeCoefficient p.1 u *
              harperTwoHeightPrimeCoefficient p.1 v -
            Real.cos (u * Real.log (p.1 : Real)) *
              Real.cos (v * Real.log (p.1 : Real)) *
                (p.1 : Real)⁻¹| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, 256 * (p.1 : Real)⁻¹ ^ (2 : Nat) := by
      exact Finset.sum_le_sum fun p hpS ↦
        abs_harperTwoHeightPrimeCoordinateCovariance_sub_cosine_le
          (Nat.prime_of_mem_primesBelow p.property) (h16 p hpS) t s u v
    _ = 256 * ∑ p ∈ S, (p.1 : Real)⁻¹ ^ (2 : Nat) := by
      rw [Finset.mul_sum]

theorem cosine_mul_cosine_eq_half_difference_add_sum
    (u v L : Real) :
    Real.cos (u * L) * Real.cos (v * L) =
      (1 / 2 : Real) *
        (Real.cos ((u - v) * L) + Real.cos ((u + v) * L)) := by
  rw [show (u - v) * L = u * L - v * L by ring,
    show (u + v) * L = u * L + v * L by ring]
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- Exact product-to-sum decomposition on a scheduled block. -/
theorem sum_scheduled_cosine_mul_cosine_eq
    (y j : Nat) (u v : Real) :
    (∑ p ∈ Problem520.harperScheduledPrimeBlock y j,
        Real.cos (u * Real.log (p.1 : Real)) *
          Real.cos (v * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹) =
      (1 / 2 : Real) *
        (Problem520.harperScheduledOscillationMass y j (u - v) +
          Problem520.harperScheduledOscillationMass y j (u + v)) := by
  unfold Problem520.harperScheduledOscillationMass
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hpS
  rw [cosine_mul_cosine_eq_half_difference_add_sum]
  ring

/-- Scheduled covariance is the half-sum of the difference and sum frequency
kernels, up to a summable inverse-square correction. -/
theorem abs_harperTwoHeightScheduledCoordinateCovariance_sub_kernels_le
    (y j : Nat) (t s u v : Real) :
    |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) t s u v -
        (1 / 2 : Real) *
          (Problem520.harperScheduledOscillationMass y j (u - v) +
            Problem520.harperScheduledOscillationMass y j (u + v))| ≤
      256 * Problem520.harperScheduledSquareMass y j := by
  rw [← sum_scheduled_cosine_mul_cosine_eq]
  simpa only [Problem520.harperScheduledSquareMass] using
    abs_harperTwoHeightBlockCoordinateCovariance_sub_cosineSum_le
      y (Problem520.harperScheduledPrimeBlock y j)
      (fun p hpS ↦ Problem520.sixteen_le_prime_of_mem_harperScheduledPrimeBlock
        hpS) t s u v

/-- The explicit output of the strong-PNT oscillatory estimate on scheduled
block `j`. -/
noncomputable def harperScheduledRawOscillationEnvelope
    (c C : Real) (j : Nat) (tau : Real) : Real :=
  (2 / |tau| +
      2 * Problem520.mediumThetaBlockDelta c C
        (Problem520.harperBlockEndpoint j)
        (Problem520.harperBlockEndpoint (j + 1)) +
      Problem520.mediumThetaBlockDelta c C
        (Problem520.harperBlockEndpoint j)
        (Problem520.harperBlockEndpoint (j + 1)) *
        (1 + |tau|) *
        Real.log ((Problem520.harperBlockEndpoint (j + 1) : Real) /
          Problem520.harperBlockEndpoint j)) *
    Problem520.invLog (Problem520.harperBlockEndpoint j)

/-- An abstract pair of oscillatory bounds immediately controls the exact
off-diagonal entry of the covariance-matched Gaussian. -/
theorem abs_harperTwoHeightScheduledCoordinateCovariance_le_of_oscillation
    (y j : Nat) (t s u v Bdiff Bsum : Real)
    (hdiff :
      |Problem520.harperScheduledOscillationMass y j (u - v)| ≤ Bdiff)
    (hsum :
      |Problem520.harperScheduledOscillationMass y j (u + v)| ≤ Bsum) :
    |harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) t s u v| ≤
      (1 / 2 : Real) * (Bdiff + Bsum) +
        256 * Problem520.harperScheduledSquareMass y j := by
  let K : Real := (1 / 2 : Real) *
    (Problem520.harperScheduledOscillationMass y j (u - v) +
      Problem520.harperScheduledOscillationMass y j (u + v))
  let R : Real := 256 * Problem520.harperScheduledSquareMass y j
  have happrox :
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) t s u v - K| ≤ R := by
    simpa only [K, R] using
      abs_harperTwoHeightScheduledCoordinateCovariance_sub_kernels_le
        y j t s u v
  have hK : |K| ≤ (1 / 2 : Real) * (Bdiff + Bsum) := by
    dsimp only [K]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2)]
    calc
      (1 / 2 : Real) *
          |Problem520.harperScheduledOscillationMass y j (u - v) +
            Problem520.harperScheduledOscillationMass y j (u + v)| ≤
        (1 / 2 : Real) *
          (|Problem520.harperScheduledOscillationMass y j (u - v)| +
            |Problem520.harperScheduledOscillationMass y j (u + v)|) := by
              gcongr
              exact abs_add_le _ _
      _ ≤ (1 / 2 : Real) * (Bdiff + Bsum) := by gcongr
  calc
    |harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) t s u v| =
      |(harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) t s u v - K) + K| := by
            congr 1
            ring
    _ ≤ |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) t s u v - K| +
        |K| := abs_add_le _ _
    _ ≤ R + (1 / 2 : Real) * (Bdiff + Bsum) := add_le_add happrox hK
    _ = (1 / 2 : Real) * (Bdiff + Bsum) +
        256 * Problem520.harperScheduledSquareMass y j := by
          dsimp only [R]
          ring

/-- Strong PNT bound for the exact off-diagonal covariance entry.  The first
envelope sees `t-s` and hence the coherence scale; the second sees `t+s`,
which stays uniformly away from zero on the lower vertical band. -/
theorem exists_harperTwoHeightScheduledCovariance_rawPNT_bound :
    ∃ c > 0, ∃ C > 0, ∃ J : Nat,
      ∀ j : Nat, J ≤ j → ∀ y : Nat,
        Problem520.harperBlockEndpoint (j + 1) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand, t ≠ s →
              |harperTwoHeightBlockCoordinateCovariance y
                  (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
                (1 / 2 : Real) *
                  (harperScheduledRawOscillationEnvelope c C j (t - s) +
                    harperScheduledRawOscillationEnvelope c C j (t + s)) +
                  256 * Problem520.harperScheduledSquareMass y j := by
  obtain ⟨c, hc, C, hC, J, hPNT⟩ :=
    Problem520.exists_mediumPNT_harperScheduledPrimeOscillation_bound
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro j hj y hy t ht s hs hts
  have hdiff : t - s ≠ 0 := sub_ne_zero.mpr hts
  have hsum : t + s ≠ 0 := by
    change (1 / 3 : Real) ≤ t ∧ t ≤ 1 / 2 at ht
    change (1 / 3 : Real) ≤ s ∧ s ≤ 1 / 2 at hs
    linarith
  have hdiffBound := hPNT j hj y hy (t - s) hdiff
  have hsumBound := hPNT j hj y hy (t + s) hsum
  apply abs_harperTwoHeightScheduledCoordinateCovariance_le_of_oscillation
    y j t s t s
  · simpa only [harperScheduledRawOscillationEnvelope] using hdiffBound
  · simpa only [harperScheduledRawOscillationEnvelope] using hsumBound

@[simp] theorem harperScheduledOscillationMass_zero
    (y j : Nat) :
    Problem520.harperScheduledOscillationMass y j 0 =
      Problem520.harperScheduledReciprocalMass y j := by
  unfold Problem520.harperScheduledOscillationMass
    Problem520.harperScheduledReciprocalMass
  apply Finset.sum_congr rfl
  intro p hpS
  simp

/-- Diagonal specialization of the exact covariance arithmetic. -/
theorem abs_harperTwoHeightScheduledCoordinateVariance_sub_main_le
    (y j : Nat) (t s u : Real) :
    |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) t s u u -
        (1 / 2 : Real) *
          (Problem520.harperScheduledReciprocalMass y j +
            Problem520.harperScheduledOscillationMass y j (2 * u))| ≤
      256 * Problem520.harperScheduledSquareMass y j := by
  have h :=
    abs_harperTwoHeightScheduledCoordinateCovariance_sub_kernels_le
      y j t s u u
  rw [sub_self, harperScheduledOscillationMass_zero,
    show u + u = 2 * u by ring] at h
  exact h

/-- A transparent lower bound for either diagonal variance.  Its three terms
are respectively the reciprocal-prime main mass, the fixed noncentral
oscillation, and the summable two-height-bias correction. -/
theorem harperTwoHeightScheduledCoordinateVariance_lower
    (y j : Nat) (t s u : Real) :
    (1 / 2 : Real) *
        (Problem520.harperScheduledReciprocalMass y j -
          |Problem520.harperScheduledOscillationMass y j (2 * u)|) -
        256 * Problem520.harperScheduledSquareMass y j ≤
      harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) t s u u := by
  have h := neg_le_of_abs_le
    (abs_harperTwoHeightScheduledCoordinateVariance_sub_main_le
      y j t s u)
  have hosc := neg_abs_le
    (Problem520.harperScheduledOscillationMass y j (2 * u))
  linarith

theorem harperTwoHeightBlockCoordinateVariance_nonneg
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s u : Real) :
    0 ≤ harperTwoHeightBlockCoordinateCovariance y S t s u u := by
  unfold harperTwoHeightBlockCoordinateCovariance
  apply Finset.sum_nonneg
  intro p hpS
  have hvar := harperTwoHeightCenteredSignVariance_nonneg p.1
    (Nat.prime_of_mem_primesBelow p.property) t s
  nlinarith [sq_nonneg (harperTwoHeightPrimeCoefficient p.1 u)]

theorem harperTwoHeightBlockCoordinateVariance_le_reciprocalMass
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s u : Real) :
    harperTwoHeightBlockCoordinateCovariance y S t s u u ≤
      ∑ p ∈ S, (p.1 : Real)⁻¹ := by
  unfold harperTwoHeightBlockCoordinateCovariance
  apply Finset.sum_le_sum
  intro p hpS
  have hpPrime := Nat.prime_of_mem_primesBelow p.property
  have hpR : (0 : Real) < p.1 := by exact_mod_cast hpPrime.pos
  have hvar0 := harperTwoHeightCenteredSignVariance_nonneg p.1
    hpPrime t s
  have hvar1 := harperTwoHeightCenteredSignVariance_le_one p.1
    hpPrime t s
  have hcoeff := harperTwoHeightPrimeCoefficient_mul hpPrime.pos u u
  have hcosSq : Real.cos (u * Real.log (p.1 : Real)) ^ (2 : Nat) ≤ 1 := by
    nlinarith [Real.neg_one_le_cos (u * Real.log (p.1 : Real)),
      Real.cos_le_one (u * Real.log (p.1 : Real))]
  have hinv0 : 0 ≤ (p.1 : Real)⁻¹ := by positivity
  rw [mul_assoc, show harperTwoHeightPrimeCoefficient p.1 u *
      harperTwoHeightPrimeCoefficient p.1 u =
        Real.cos (u * Real.log (p.1 : Real)) ^ (2 : Nat) *
          (p.1 : Real)⁻¹ by simpa only [pow_two] using hcoeff]
  have hcoeff0 : 0 ≤ Real.cos (u * Real.log (p.1 : Real)) ^ (2 : Nat) *
      (p.1 : Real)⁻¹ := mul_nonneg (sq_nonneg _) hinv0
  calc
    harperTwoHeightCenteredSignVariance p.1 hpPrime t s *
          (Real.cos (u * Real.log (p.1 : Real)) ^ (2 : Nat) *
            (p.1 : Real)⁻¹) ≤
        1 * (Real.cos (u * Real.log (p.1 : Real)) ^ (2 : Nat) *
          (p.1 : Real)⁻¹) :=
      mul_le_mul_of_nonneg_right hvar1 hcoeff0
    _ ≤ 1 * (1 * (p.1 : Real)⁻¹) := by gcongr
    _ = (p.1 : Real)⁻¹ := by ring

theorem harperTwoHeightScheduledCoordinateVariance_upper
    (y j : Nat) (t s u : Real) :
    harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) t s u u ≤
      Problem520.harperScheduledReciprocalMass y j := by
  simpa only [Problem520.harperScheduledReciprocalMass] using
    harperTwoHeightBlockCoordinateVariance_le_reciprocalMass y
      (Problem520.harperScheduledPrimeBlock y j) t s u

/-- Uniform nondegeneracy of both coordinates of the exact covariance
Gaussian on the lower vertical band.  This is uniform in both tilt heights
and in either observation height. -/
theorem exists_eventually_harperTwoHeightScheduledCoordinateVariance_quarter_one :
    ∃ J : Nat, ∀ j : Nat, J ≤ j → ∀ y : Nat,
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            ∀ u ∈ harperLowerVerticalBand,
              (1 / 4 : Real) <
                  harperTwoHeightBlockCoordinateCovariance y
                    (Problem520.harperScheduledPrimeBlock y j) t s u u ∧
                harperTwoHeightBlockCoordinateCovariance y
                    (Problem520.harperScheduledPrimeBlock y j) t s u u < 1 := by
  obtain ⟨Jmass, hmass⟩ :=
    Problem520.exists_eventually_harperScheduledPrimeBlock_inv_close_log_two
      (by norm_num : (0 : Real) < 1 / 1000)
  obtain ⟨Josc, hosc⟩ :=
    Problem520.exists_harperScheduledCentralBandOscillation_le_milli
  obtain ⟨c, hc, C, hC, Jerr, herr⟩ :=
    Problem520.exists_harperScheduledSummableBlockErrorBounds 1
  have hsquareTendsto : Tendsto Problem520.harperScheduledSquareEnvelope
      Filter.atTop (nhds 0) :=
    Problem520.summable_harperScheduledSquareEnvelope.tendsto_atTop_zero
  have hsquareEventually : ∀ᶠ j : Nat in Filter.atTop,
      Problem520.harperScheduledSquareEnvelope j <
        (1 / 256000 : Real) :=
    (tendsto_order.mp hsquareTendsto).2 _ (by norm_num)
  obtain ⟨Jsquare, hsquare⟩ := Filter.eventually_atTop.1 hsquareEventually
  refine ⟨max Jmass (max (Josc + 1) (max Jerr Jsquare)), ?_⟩
  intro j hj y hy t ht s hs u hu
  have hjmass : Jmass ≤ j := by omega
  have hjosc : Josc + 1 ≤ j := by omega
  have hjerr : Jerr ≤ j := by omega
  have hjsquare : Jsquare ≤ j := by omega
  have huBand : (1 / 3 : Real) ≤ u ∧ u ≤ 1 / 2 := hu
  have hu0 : 0 ≤ u := by linarith [huBand.1]
  have huabs : |u| = u := abs_of_nonneg hu0
  have huLower : (1 / 2 : Real) ^ (1 + 1) < |u| := by
    rw [huabs]
    norm_num
    linarith [huBand.1]
  have huUpper : |u| ≤ (1 / 2 : Real) ^ (1 : Nat) := by
    rw [huabs]
    norm_num
    exact huBand.2
  have hmassj := hmass j hjmass y hy
  change |Problem520.harperScheduledReciprocalMass y j - Real.log 2| <
    (1 / 1000 : Real) at hmassj
  have hoscj := hosc 1 j y hjosc hy u huLower huUpper
  have hsquarej : Problem520.harperScheduledSquareMass y j ≤
      Problem520.harperScheduledSquareEnvelope j :=
    (herr j hjerr y hy).2.2
  have hsquareSmall :
      256 * Problem520.harperScheduledSquareMass y j <
        (1 / 1000 : Real) := by
    have hsquare0 : 0 ≤ Problem520.harperScheduledSquareMass y j := by
      unfold Problem520.harperScheduledSquareMass
      positivity
    have hsmall := hsquare j hjsquare
    nlinarith
  have hlower := harperTwoHeightScheduledCoordinateVariance_lower
    y j t s u
  have hupper := harperTwoHeightScheduledCoordinateVariance_upper
    y j t s u
  have hmassLower := neg_lt_of_abs_lt hmassj
  have hmassUpper := lt_of_abs_lt hmassj
  have hoscNonneg : 0 ≤
      |Problem520.harperScheduledOscillationMass y j (2 * u)| :=
    abs_nonneg _
  constructor <;>
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The sharper variance window needed by the universal finite Gaussian
ballot estimate.  Both exact joint-tilt marginal variances converge uniformly
to `(log 2)/2`, hence eventually lie between `1/3` and `3/8`. -/
theorem exists_eventually_harperTwoHeightScheduledCoordinateVariance_third_threeEighths :
    ∃ J : Nat, ∀ j : Nat, J ≤ j → ∀ y : Nat,
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            ∀ u ∈ harperLowerVerticalBand,
              (1 / 3 : Real) <
                  harperTwoHeightBlockCoordinateCovariance y
                    (Problem520.harperScheduledPrimeBlock y j) t s u u ∧
                harperTwoHeightBlockCoordinateCovariance y
                    (Problem520.harperScheduledPrimeBlock y j) t s u u <
                  (3 / 8 : Real) := by
  obtain ⟨Jmass, hmass⟩ :=
    Problem520.exists_eventually_harperScheduledPrimeBlock_inv_close_log_two
      (by norm_num : (0 : Real) < 1 / 1000)
  obtain ⟨Josc, hosc⟩ :=
    Problem520.exists_harperScheduledCentralBandOscillation_le_milli
  obtain ⟨c, hc, C, hC, Jerr, herr⟩ :=
    Problem520.exists_harperScheduledSummableBlockErrorBounds 1
  have hsquareTendsto : Tendsto Problem520.harperScheduledSquareEnvelope
      Filter.atTop (nhds 0) :=
    Problem520.summable_harperScheduledSquareEnvelope.tendsto_atTop_zero
  have hsquareEventually : ∀ᶠ j : Nat in Filter.atTop,
      Problem520.harperScheduledSquareEnvelope j <
        (1 / 256000 : Real) :=
    (tendsto_order.mp hsquareTendsto).2 _ (by norm_num)
  obtain ⟨Jsquare, hsquare⟩ := Filter.eventually_atTop.1 hsquareEventually
  refine ⟨max Jmass (max (Josc + 1) (max Jerr Jsquare)), ?_⟩
  intro j hj y hy t ht s hs u hu
  have hjmass : Jmass ≤ j := by omega
  have hjosc : Josc + 1 ≤ j := by omega
  have hjerr : Jerr ≤ j := by omega
  have hjsquare : Jsquare ≤ j := by omega
  have huBand : (1 / 3 : Real) ≤ u ∧ u ≤ 1 / 2 := hu
  have hu0 : 0 ≤ u := by linarith [huBand.1]
  have huabs : |u| = u := abs_of_nonneg hu0
  have huLower : (1 / 2 : Real) ^ (1 + 1) < |u| := by
    rw [huabs]
    norm_num
    linarith [huBand.1]
  have huUpper : |u| ≤ (1 / 2 : Real) ^ (1 : Nat) := by
    rw [huabs]
    norm_num
    exact huBand.2
  have hmassj := hmass j hjmass y hy
  change |Problem520.harperScheduledReciprocalMass y j - Real.log 2| <
    (1 / 1000 : Real) at hmassj
  have hoscj := hosc 1 j y hjosc hy u huLower huUpper
  have hsquarej : Problem520.harperScheduledSquareMass y j ≤
      Problem520.harperScheduledSquareEnvelope j :=
    (herr j hjerr y hy).2.2
  have hsquareSmall :
      256 * Problem520.harperScheduledSquareMass y j <
        (1 / 1000 : Real) := by
    have hsquare0 : 0 ≤ Problem520.harperScheduledSquareMass y j := by
      unfold Problem520.harperScheduledSquareMass
      positivity
    have hsmall := hsquare j hjsquare
    nlinarith
  have happrox :=
    abs_harperTwoHeightScheduledCoordinateVariance_sub_main_le
      y j t s u
  have hmassLower := neg_lt_of_abs_lt hmassj
  have hmassUpper := lt_of_abs_lt hmassj
  have hoscBounds := abs_le.mp hoscj
  have happroxBounds := abs_le.mp happrox
  constructor <;>
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Dyadic-shell form of post-coherence covariance decay.  On shell `r`,
block `j` is decorrelated once `j` is at least a fixed constant plus `r+1`.
The difference frequency pays the shell-dependent envelope; the sum
frequency always pays the fixed `d=1` envelope. -/
theorem exists_harperTwoHeightScheduledCovariance_dyadicShell_bound :
    ∃ c > 0, ∃ C > 0, ∃ J : Nat,
      ∀ r j y : Nat, J + (r + 1) ≤ j →
        Problem520.harperBlockEndpoint (j + 1) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (r + 1) < |t - s| →
                |harperTwoHeightBlockCoordinateCovariance y
                    (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
                  (1 / 2 : Real) *
                    (Problem520.harperScheduledDyadicOscillationEnvelope
                        (r + 1) c C j +
                      Problem520.harperScheduledDyadicOscillationEnvelope
                        1 c C j) +
                    256 * Problem520.harperScheduledSquareMass y j := by
  obtain ⟨c, hc, C, hC, J, hosc⟩ :=
    Problem520.exists_harperScheduledDyadicOscillationBounds
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro r j y hj hy t ht s hs hsep
  have htBand : (1 / 3 : Real) ≤ t ∧ t ≤ 1 / 2 := ht
  have hsBand : (1 / 3 : Real) ≤ s ∧ s ≤ 1 / 2 := hs
  let udiff : Real := (t - s) / 2
  let usum : Real := (t + s) / 2
  have hudiffLower :
      (1 / 2 : Real) ^ ((r + 1) + 1) < |udiff| := by
    calc
      (1 / 2 : Real) ^ ((r + 1) + 1) =
          (1 / 2 : Real) ^ (r + 1) / 2 := by
        rw [pow_succ]
        ring
      _ < |t - s| / 2 := div_lt_div_of_pos_right hsep (by norm_num)
      _ = |udiff| := by
        dsimp only [udiff]
        rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
  have hdiffAbs : |t - s| ≤ (1 / 6 : Real) := by
    rw [abs_le]
    constructor <;> linarith
  have hudiffUpper : |udiff| ≤ 1 := by
    dsimp only [udiff]
    rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    linarith
  have husumPos : 0 < usum := by
    dsimp only [usum]
    linarith
  have husumLower : (1 / 2 : Real) ^ (1 + 1) < |usum| := by
    rw [abs_of_pos husumPos]
    dsimp only [usum]
    norm_num
    linarith
  have husumUpper : |usum| ≤ 1 := by
    rw [abs_of_pos husumPos]
    dsimp only [usum]
    linarith
  have hjSum : J + 1 ≤ j := by omega
  have hdiffBound := hosc (r + 1) j y hj hy udiff udiff
    hudiffLower hudiffUpper (by simp)
  have hsumBound := hosc 1 j y hjSum hy usum usum
    husumLower husumUpper (by simp)
  apply abs_harperTwoHeightScheduledCoordinateCovariance_le_of_oscillation
    y j t s t s
  · simpa only [udiff, show 2 * ((t - s) / 2) = t - s by ring] using
      hdiffBound
  · simpa only [usum, show 2 * ((t + s) / 2) = t + s by ring] using
      hsumBound

theorem harperScheduledDyadicOscillationEnvelope_le_geometric
    {c C : Real} {d j : Nat} (hdj : d ≤ j) :
    Problem520.harperScheduledDyadicOscillationEnvelope d c C j ≤
      4 * (1 / 2 : Real) ^ (j - d) +
        7 * Problem520.harperScheduledThetaEnvelope c C j := by
  unfold Problem520.harperScheduledDyadicOscillationEnvelope
  exact add_le_add
    (Problem520.harperScheduledDyadicBoundary_le_geometric hdj) le_rfl

/-- Fully explicit geometric form of the shell covariance estimate. -/
theorem exists_harperTwoHeightScheduledCovariance_postCoherence_geometric :
    ∃ c > 0, ∃ C > 0, ∃ J : Nat,
      ∀ r j y : Nat, J + (r + 1) ≤ j →
        Problem520.harperBlockEndpoint (j + 1) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (r + 1) < |t - s| →
                |harperTwoHeightBlockCoordinateCovariance y
                    (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
                  2 * (1 / 2 : Real) ^ (j - (r + 1)) +
                    2 * (1 / 2 : Real) ^ (j - 1) +
                    7 * Problem520.harperScheduledThetaEnvelope c C j +
                    256 * Problem520.harperScheduledSquareMass y j := by
  obtain ⟨c, hc, C, hC, J, hcov⟩ :=
    exists_harperTwoHeightScheduledCovariance_dyadicShell_bound
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro r j y hj hy t ht s hs hsep
  have hrj : r + 1 ≤ j := by omega
  have h1j : 1 ≤ j := by omega
  have hraw := hcov r j y hj hy t ht s hs hsep
  have hdiff := harperScheduledDyadicOscillationEnvelope_le_geometric
    (c := c) (C := C) hrj
  have hsum := harperScheduledDyadicOscillationEnvelope_le_geometric
    (c := c) (C := C) h1j
  calc
    |harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
      (1 / 2 : Real) *
          (Problem520.harperScheduledDyadicOscillationEnvelope
              (r + 1) c C j +
            Problem520.harperScheduledDyadicOscillationEnvelope 1 c C j) +
        256 * Problem520.harperScheduledSquareMass y j := hraw
    _ ≤ (1 / 2 : Real) *
          ((4 * (1 / 2 : Real) ^ (j - (r + 1)) +
              7 * Problem520.harperScheduledThetaEnvelope c C j) +
            (4 * (1 / 2 : Real) ^ (j - 1) +
              7 * Problem520.harperScheduledThetaEnvelope c C j)) +
        256 * Problem520.harperScheduledSquareMass y j := by gcongr
    _ = 2 * (1 / 2 : Real) ^ (j - (r + 1)) +
          2 * (1 / 2 : Real) ^ (j - 1) +
          7 * Problem520.harperScheduledThetaEnvelope c C j +
          256 * Problem520.harperScheduledSquareMass y j := by ring

/-- Uniform small-correlation consequence.  After a fixed additional shift,
every block beyond the shell's coherence index has covariance smaller than
an arbitrary prescribed positive constant. -/
theorem exists_eventually_harperTwoHeightScheduledCovariance_postCoherence_small
    {ε : Real} (hε : 0 < ε) :
    ∃ J : Nat, ∀ r j y : Nat, J + (r + 1) ≤ j →
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (r + 1) < |t - s| →
              |harperTwoHeightBlockCoordinateCovariance y
                  (Problem520.harperScheduledPrimeBlock y j) t s t s| < ε := by
  obtain ⟨c, hc, C, hC, Jcov, hcov⟩ :=
    exists_harperTwoHeightScheduledCovariance_postCoherence_geometric
  obtain ⟨c', hc', C', hC', Jerr, herr⟩ :=
    Problem520.exists_harperScheduledSummableBlockErrorBounds 1
  have hgeomTendsto : Tendsto
      (fun k : Nat ↦ 2 * (1 / 2 : Real) ^ k) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : Real) ≤ 1 / 2)
        (by norm_num : (1 / 2 : Real) < 1))
  have hthetaTendsto : Tendsto
      (Problem520.harperScheduledThetaEnvelope c C) atTop (nhds 0) :=
    (Problem520.summable_harperScheduledThetaEnvelope hc hC.le).tendsto_atTop_zero
  have hsquareTendsto : Tendsto Problem520.harperScheduledSquareEnvelope
      atTop (nhds 0) :=
    Problem520.summable_harperScheduledSquareEnvelope.tendsto_atTop_zero
  have hgeomEventually : ∀ᶠ k : Nat in atTop,
      2 * (1 / 2 : Real) ^ k < ε / 4 :=
    (tendsto_order.mp hgeomTendsto).2 _ (by linarith)
  have hthetaEventually : ∀ᶠ k : Nat in atTop,
      Problem520.harperScheduledThetaEnvelope c C k < ε / 28 :=
    (tendsto_order.mp hthetaTendsto).2 _ (by linarith)
  have hsquareEventually : ∀ᶠ k : Nat in atTop,
      Problem520.harperScheduledSquareEnvelope k < ε / 1024 :=
    (tendsto_order.mp hsquareTendsto).2 _ (by linarith)
  obtain ⟨Jgeom, hgeom⟩ := Filter.eventually_atTop.1 hgeomEventually
  obtain ⟨Jtheta, htheta⟩ := Filter.eventually_atTop.1 hthetaEventually
  obtain ⟨Jsquare, hsquare⟩ := Filter.eventually_atTop.1 hsquareEventually
  let J := max Jcov (max Jerr (max Jgeom (max Jtheta Jsquare)))
  refine ⟨J, ?_⟩
  intro r j y hj hy t ht s hs hsep
  have hJcov : Jcov + (r + 1) ≤ j := by
    have : Jcov ≤ J := le_max_left _ _
    omega
  have hJerr : Jerr ≤ j := by
    have : Jerr ≤ J := (le_max_left Jerr _).trans (le_max_right Jcov _)
    omega
  have hJgeomDiff : Jgeom ≤ j - (r + 1) := by
    have : Jgeom ≤ J :=
      (le_max_left Jgeom _).trans
        ((le_max_right Jerr _).trans (le_max_right Jcov _))
    omega
  have hJgeomSum : Jgeom ≤ j - 1 := by
    have : Jgeom ≤ J :=
      (le_max_left Jgeom _).trans
        ((le_max_right Jerr _).trans (le_max_right Jcov _))
    omega
  have hJtheta : Jtheta ≤ j := by
    have : Jtheta ≤ J :=
      ((le_max_left Jtheta Jsquare).trans (le_max_right Jgeom _)).trans
        ((le_max_right Jerr _).trans (le_max_right Jcov _))
    omega
  have hJsquare : Jsquare ≤ j := by
    have : Jsquare ≤ J :=
      ((le_max_right Jtheta Jsquare).trans (le_max_right Jgeom _)).trans
        ((le_max_right Jerr _).trans (le_max_right Jcov _))
    omega
  have hraw := hcov r j y hJcov hy t ht s hs hsep
  have hgeomDiff := hgeom (j - (r + 1)) hJgeomDiff
  have hgeomSum := hgeom (j - 1) hJgeomSum
  have hthetaSmall := htheta j hJtheta
  have hsquareBound : Problem520.harperScheduledSquareMass y j ≤
      Problem520.harperScheduledSquareEnvelope j :=
    (herr j hJerr y hy).2.2
  have hsquareSmall := hsquare j hJsquare
  nlinarith

/-- Beyond a fixed shift past the dyadic coherence scale, every scheduled
two-height block covariance matrix has its least eigenvalue at least `1 / 8`.
This is the uniform nondegeneracy input needed by the two-dimensional
rectangle comparison. -/
theorem exists_eventually_harperTwoHeightScheduledProjectedVariance_eighth :
    ∃ J : Nat, ∀ r j y : Nat, J + (r + 1) ≤ j →
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (r + 1) < |t - s| →
              ∀ v w : Real,
                (1 / 8 : Real) * (v ^ (2 : Nat) + w ^ (2 : Nat)) ≤
                  harperTwoHeightProjectedBlockVariance y
                    (Problem520.harperScheduledPrimeBlock y j) t s v w := by
  obtain ⟨Jvar, hvar⟩ :=
    exists_eventually_harperTwoHeightScheduledCoordinateVariance_quarter_one
  obtain ⟨Jcov, hcov⟩ :=
    exists_eventually_harperTwoHeightScheduledCovariance_postCoherence_small
      (by norm_num : (0 : Real) < 1 / 8)
  refine ⟨max Jvar Jcov, ?_⟩
  intro r j y hj hy t ht s hs hsep v w
  have hjvar : Jvar ≤ j := by
    have : Jvar ≤ max Jvar Jcov := le_max_left _ _
    omega
  have hjcov : Jcov + (r + 1) ≤ j := by
    have : Jcov ≤ max Jvar Jcov := le_max_right _ _
    omega
  have htt := (hvar j hjvar y hy t ht s hs t ht).1
  have hss := (hvar j hjvar y hy t ht s hs s hs).1
  have hts := (hcov r j y hjcov hy t ht s hs hsep).le
  exact harperTwoHeightProjectedBlockVariance_ge_eighth_of_marginals_covariance
    y (Problem520.harperScheduledPrimeBlock y j) t s v w htt.le hss.le hts

#print axioms Erdos.Problem1144.harperTwoHeightCenteredSignVariance_eq_one_sub_sq
#print axioms Erdos.Problem1144.abs_harperTwoHeightTiltBias_le_sixteen_inv_sqrt
#print axioms Erdos.Problem1144.harperTwoHeightBlockCovarianceMatrix_apply
#print axioms Erdos.Problem1144.harperTwoHeightProjectedBlockVariance_eq_coordinateCovariance
#print axioms Erdos.Problem1144.abs_harperTwoHeightScheduledCoordinateCovariance_sub_kernels_le
#print axioms Erdos.Problem1144.exists_harperTwoHeightScheduledCovariance_rawPNT_bound
#print axioms Erdos.Problem1144.harperTwoHeightScheduledCoordinateVariance_lower
#print axioms Erdos.Problem1144.harperTwoHeightScheduledCoordinateVariance_upper
#print axioms Erdos.Problem1144.exists_eventually_harperTwoHeightScheduledCoordinateVariance_quarter_one
#print axioms Erdos.Problem1144.exists_eventually_harperTwoHeightScheduledCoordinateVariance_third_threeEighths
#print axioms Erdos.Problem1144.exists_harperTwoHeightScheduledCovariance_dyadicShell_bound
#print axioms Erdos.Problem1144.exists_harperTwoHeightScheduledCovariance_postCoherence_geometric
#print axioms Erdos.Problem1144.exists_eventually_harperTwoHeightScheduledCovariance_postCoherence_small
#print axioms Erdos.Problem1144.harperTwoHeightProjectedBlockVariance_ge_eighth_of_marginals_covariance
#print axioms Erdos.Problem1144.exists_eventually_harperTwoHeightScheduledProjectedVariance_eighth

end

end Problem1144
end Erdos
