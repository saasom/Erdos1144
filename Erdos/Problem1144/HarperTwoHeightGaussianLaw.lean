import Erdos.Problem1144.HarperBivariateFejer
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open Finset MeasureTheory ProbabilityTheory Set Matrix WithLp
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# The covariance-matched two-height Gaussian law

This module constructs the Gaussian comparison measure that was left
abstract in the two-dimensional Fejer estimate.  Its covariance matrix is a
finite sum of the rank-one covariance matrices contributed by the scheduled
prime block.  Positive semidefiniteness is therefore immediate, including in
the degenerate near-diagonal case.
-/

/-- The variance of the centered sign under one two-height tilted coin. -/
noncomputable def harperTwoHeightCenteredSignVariance
    (p : Nat) (hp : p.Prime) (t s : Real) : Real :=
  ∫ b, (Problem520.cubeSign b - harperTwoHeightTiltBias p t s) ^ (2 : Nat)
    ∂harperTwoHeightCoin p hp t s

theorem harperTwoHeightCenteredSignVariance_nonneg
    (p : Nat) (hp : p.Prime) (t s : Real) :
    0 ≤ harperTwoHeightCenteredSignVariance p hp t s := by
  unfold harperTwoHeightCenteredSignVariance
  exact integral_nonneg fun b ↦ sq_nonneg _

/-- The deterministic coefficient of a prime at an observation height. -/
noncomputable def harperTwoHeightPrimeCoefficient (p : Nat) (u : Real) : Real :=
  Real.cos (u * Real.log (p : Real)) / Real.sqrt (p : Real)

/-- Coordinates are indexed by `Bool`: `false` is height `t`, `true` is
height `s`. -/
noncomputable def harperTwoHeightPrimeCoefficientVector
    (p : Nat) (t s : Real) (i : Bool) : Real :=
  if i then harperTwoHeightPrimeCoefficient p s
  else harperTwoHeightPrimeCoefficient p t

/-- The exact covariance matrix of the centered linear two-height prime
block. -/
noncomputable def harperTwoHeightBlockCovarianceMatrix
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) : Matrix Bool Bool Real :=
  ∑ p ∈ S,
    harperTwoHeightCenteredSignVariance p.1
        (Nat.prime_of_mem_primesBelow p.property) t s •
      Matrix.vecMulVec
        (harperTwoHeightPrimeCoefficientVector p.1 t s)
        (harperTwoHeightPrimeCoefficientVector p.1 t s)

theorem harperTwoHeightBlockCovarianceMatrix_posSemidef
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    (harperTwoHeightBlockCovarianceMatrix y S t s).PosSemidef := by
  classical
  unfold harperTwoHeightBlockCovarianceMatrix
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact Matrix.PosSemidef.zero
  | @insert p S hp ih =>
      rw [Finset.sum_insert hp]
      exact ((Matrix.posSemidef_vecMulVec_self_star
        (harperTwoHeightPrimeCoefficientVector p.1 t s)).smul
          (harperTwoHeightCenteredSignVariance_nonneg p.1
            (Nat.prime_of_mem_primesBelow p.property) t s)).add ih

/-- The projected one-prime variance is the centered-sign variance times
the square of the corresponding deterministic linear form. -/
theorem harperTwoHeightProjectedPrimeVariance_eq
    (p : Nat) (hp : p.Prime) (t s v w : Real) :
    harperTwoHeightProjectedPrimeVariance p hp t s v w =
      harperTwoHeightCenteredSignVariance p hp t s *
        (v * harperTwoHeightPrimeCoefficient p t +
          w * harperTwoHeightPrimeCoefficient p s) ^ (2 : Nat) := by
  unfold harperTwoHeightProjectedPrimeVariance
    harperTwoHeightProjectedPrimeIncrement
    harperTwoHeightPrimeFluctuation
    harperTwoHeightPrimeCoefficient
    harperTwoHeightCenteredSignVariance
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ fun b ↦ by ring

/-- The covariance quadratic form is definitionally the projected block
variance already used in the characteristic estimate. -/
theorem harperTwoHeightBlockCovarianceMatrix_quadratic
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) :
    let z : EuclideanSpace Real Bool :=
      toLp 2 (fun i : Bool ↦ if i then w else v)
    z ⬝ᵥ harperTwoHeightBlockCovarianceMatrix y S t s *ᵥ z =
      harperTwoHeightProjectedBlockVariance y S t s v w := by
  classical
  dsimp only
  unfold harperTwoHeightBlockCovarianceMatrix
    harperTwoHeightProjectedBlockVariance
  rw [Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro p hpS
  rw [harperTwoHeightProjectedPrimeVariance_eq]
  simp [dotProduct, mulVec, Matrix.vecMulVec,
    harperTwoHeightPrimeCoefficientVector]
  ring

/-- The covariance-matched Gaussian on the two-dimensional Euclidean space
indexed by `Bool`. -/
noncomputable def harperTwoHeightGaussianEuclideanLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) : Measure (EuclideanSpace Real Bool) :=
  multivariateGaussian 0 (harperTwoHeightBlockCovarianceMatrix y S t s)

instance harperTwoHeightGaussianEuclideanLaw_isProbabilityMeasure
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    IsProbabilityMeasure (harperTwoHeightGaussianEuclideanLaw y S t s) := by
  unfold harperTwoHeightGaussianEuclideanLaw
  infer_instance

/-- The same Gaussian law in the product coordinates used by the bivariate
Fejer interface. -/
noncomputable def harperTwoHeightGaussianLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) : Measure (Real × Real) :=
  Measure.map (fun x : EuclideanSpace Real Bool ↦ (x false, x true))
    (harperTwoHeightGaussianEuclideanLaw y S t s)

instance harperTwoHeightGaussianLaw_isProbabilityMeasure
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    IsProbabilityMeasure (harperTwoHeightGaussianLaw y S t s) := by
  unfold harperTwoHeightGaussianLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem charFun_harperTwoHeightGaussianEuclideanLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) :
    let z : EuclideanSpace Real Bool :=
      toLp 2 (fun i : Bool ↦ if i then w else v)
    charFun (harperTwoHeightGaussianEuclideanLaw y S t s) z =
      Complex.exp
        (-((harperTwoHeightProjectedBlockVariance y S t s v w / 2 :
          Real) : Complex)) := by
  dsimp only
  unfold harperTwoHeightGaussianEuclideanLaw
  rw [charFun_multivariateGaussian
    (harperTwoHeightBlockCovarianceMatrix_posSemidef y S t s)]
  rw [harperTwoHeightBlockCovarianceMatrix_quadratic]
  simp

/-- The product-coordinate Gaussian has exactly the covariance
characteristic used by the Rademacher comparison. -/
theorem harperBivariateCharacteristic_harperTwoHeightGaussianLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) :
    harperBivariateCharacteristic
        (harperTwoHeightGaussianLaw y S t s) (v, w) =
      Complex.exp
        (-((harperTwoHeightProjectedBlockVariance y S t s v w / 2 :
          Real) : Complex)) := by
  let z : EuclideanSpace Real Bool :=
    toLp 2 (fun i : Bool ↦ if i then w else v)
  calc
    harperBivariateCharacteristic
        (harperTwoHeightGaussianLaw y S t s) (v, w) =
        charFun (harperTwoHeightGaussianEuclideanLaw y S t s) z := by
      rw [harperBivariateCharacteristic, charFunDual_apply]
      unfold harperTwoHeightGaussianLaw
      rw [integral_map (by fun_prop) (by fun_prop), charFun_apply]
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by
        simp [z, harperTwoHeightProjection_apply, PiLp.inner_apply]
        rw [real_inner_eq_re_inner Real, real_inner_eq_re_inner Real]
        simp [RCLike.inner_apply]
        ring_nf
    _ = _ := charFun_harperTwoHeightGaussianEuclideanLaw y S t s v w

/-- Scheduled form of the exact Gaussian characteristic identity. -/
theorem harperBivariateCharacteristic_scheduledTwoHeightGaussianLaw
    (y j : Nat) (t s : Real) (z : Real × Real) :
    harperBivariateCharacteristic
        (harperTwoHeightGaussianLaw y
          (Problem520.harperScheduledPrimeBlock y j) t s) z =
      harperScheduledTwoHeightGaussianCharacteristic y j t s z := by
  rw [← Prod.eta z]
  exact harperBivariateCharacteristic_harperTwoHeightGaussianLaw
    y (Problem520.harperScheduledPrimeBlock y j) t s z.1 z.2

/-- The scheduled smoothed-cell comparison with the Gaussian measure now
fully instantiated.  Only the general product-Fejer inversion identity is
left as an input to this theorem. -/
theorem abs_harperScheduledTwoHeightSmoothRectangle_sub_gaussianLaw_le
    (y j : Nat) (t s T a b c d : Real)
    (hT : 0 ≤ T)
    (hfrequency :
      4 * T ≤ Real.sqrt (Problem520.harperBlockEndpoint j : Real))
    (hidentity : HarperBivariateFejerRectangleIdentity
      (harperTwoHeightPrimeBlockVectorLaw y
        (Problem520.harperScheduledPrimeBlock y j) t s)
      (harperTwoHeightGaussianLaw y
        (Problem520.harperScheduledPrimeBlock y j) t s) T) :
    |harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T)
          (harperTwoHeightPrimeBlockVectorLaw y
            (Problem520.harperScheduledPrimeBlock y j) t s) a b c d -
        harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T)
          (harperTwoHeightGaussianLaw y
            (Problem520.harperScheduledPrimeBlock y j) t s) a b c d| ≤
      (2 * Real.pi)⁻¹ ^ (2 : Nat) * |b - a| * |d - c| *
        (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
          (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat)) := by
  exact abs_harperScheduledTwoHeightSmoothRectangle_sub_gaussian_le
    y j t s
    (harperTwoHeightGaussianLaw y
      (Problem520.harperScheduledPrimeBlock y j) t s)
    T a b c d hT hfrequency
    (harperBivariateCharacteristic_scheduledTwoHeightGaussianLaw y j t s)
    hidentity

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.harperTwoHeightBlockCovarianceMatrix_posSemidef
#print axioms Erdos.Problem1144.harperTwoHeightBlockCovarianceMatrix_quadratic
#print axioms Erdos.Problem1144.harperBivariateCharacteristic_harperTwoHeightGaussianLaw
#print axioms Erdos.Problem1144.harperBivariateCharacteristic_scheduledTwoHeightGaussianLaw
#print axioms Erdos.Problem1144.abs_harperScheduledTwoHeightSmoothRectangle_sub_gaussianLaw_le
