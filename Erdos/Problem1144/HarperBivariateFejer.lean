import Erdos.Problem1144.HarperTwoHeightVectorLaw
import Erdos.Problem520.HarperFejerInversion

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators Interval ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Two-dimensional Fejer smoothing for bounded rectangles

Harper's local-limit argument only needs probabilities of bounded cells.
This is important: the Fourier multiplier of a bounded interval has a
removable singularity at zero, so the product multiplier in two dimensions is
uniformly bounded by the area of the spatial rectangle.

As in the successful one-dimensional development, the exact inversion
identity is isolated first.  Everything after it--the multiplier estimate,
integrability, and the explicit consequence of a cubic/quartic characteristic
bound--is proved here.
-/

/-- Characteristic function of a law on `Real × Real`, parametrized by the
ordinary frequency pair. -/
noncomputable def harperBivariateCharacteristic
    (mu : Measure (Real × Real)) (z : Real × Real) : Complex :=
  charFunDual mu (harperTwoHeightProjection z.1 z.2)

/-- Fejer-smoothed mass of the rectangle `(a,b] × (c,d]`. -/
noncomputable def harperBivariateSmoothRectangle
    (kappa : Measure Real) (mu : Measure (Real × Real))
    (a b c d : Real) : Real :=
  ∫ x,
    (cdf kappa (b - x.1) - cdf kappa (a - x.1)) *
      (cdf kappa (d - x.2) - cdf kappa (c - x.2)) ∂mu

/-- Compactly supported Fourier multiplier of a bounded interval.  The value
at zero is immaterial for integration and is filled with zero. -/
noncomputable def harperFejerIntervalMultiplier
    (T a b v : Real) : Complex :=
  if v = 0 then 0 else
    (Complex.exp (((-v * b : Real) : Complex) * Complex.I) -
        Complex.exp (((-v * a : Real) : Complex) * Complex.I)) *
      (Problem520.harperFejerTriangle (T⁻¹ * v) : Complex) /
        (-((v : Complex) * Complex.I))

/-- The two-frequency inversion integrand for a difference of bivariate
laws. -/
noncomputable def harperBivariateFejerRectangleIntegrand
    (phi psi : (Real × Real) → Complex)
    (T a b c d : Real) (z : Real × Real) : Complex :=
  (phi z - psi z) *
    harperFejerIntervalMultiplier T a b z.1 *
      harperFejerIntervalMultiplier T c d z.2

/-- The exact product-Fejer inversion statement.  A later inversion module
must prove this for the actual and Gaussian laws; all quantitative analysis
after the identity is already supplied below. -/
def HarperBivariateFejerRectangleIdentity
    (mu nu : Measure (Real × Real)) (T : Real) : Prop :=
  ∀ a b c d : Real,
    (((harperBivariateSmoothRectangle
        (Problem520.harperFejerMeasureScaled T) mu a b c d -
      harperBivariateSmoothRectangle
        (Problem520.harperFejerMeasureScaled T) nu a b c d : Real) :
          Complex)) =
      ((((2 * Real.pi : Real)⁻¹ : Real) : Complex) ^ (2 : Nat)) *
        ∫ z in Icc (-T) T ×ˢ Icc (-T) T,
          harperBivariateFejerRectangleIntegrand
            (harperBivariateCharacteristic mu)
            (harperBivariateCharacteristic nu) T a b c d z

/-- The bounded-interval Fourier multiplier is controlled by the interval
length, uniformly in frequency. -/
theorem norm_harperFejerIntervalMultiplier_le
    (T a b v : Real) :
    ‖harperFejerIntervalMultiplier T a b v‖ ≤ |b - a| := by
  by_cases hv : v = 0
  · simp [harperFejerIntervalMultiplier, hv]
  have hIntBound :
      ‖∫ x in a..b,
          Complex.exp (((-v * x : Real) : Complex) * Complex.I)‖ ≤
        1 * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [Problem520.intervalIntegral_exp_neg_mul_I hv] at hIntBound
  have hquot :
      ‖(Complex.exp (((-v * b : Real) : Complex) * Complex.I) -
          Complex.exp (((-v * a : Real) : Complex) * Complex.I)) /
            (-((v : Complex) * Complex.I))‖ ≤ |b - a| := by
    simpa only [one_mul] using hIntBound
  have htri0 : 0 ≤ Problem520.harperFejerTriangle (T⁻¹ * v) :=
    Problem520.harperFejerTriangle_nonneg _
  have htri1 : Problem520.harperFejerTriangle (T⁻¹ * v) ≤ 1 :=
    Problem520.harperFejerTriangle_le_one _
  rw [harperFejerIntervalMultiplier, if_neg hv]
  rw [show
      (Complex.exp (((-v * b : Real) : Complex) * Complex.I) -
          Complex.exp (((-v * a : Real) : Complex) * Complex.I)) *
            (Problem520.harperFejerTriangle (T⁻¹ * v) : Complex) /
              (-((v : Complex) * Complex.I)) =
        ((Complex.exp (((-v * b : Real) : Complex) * Complex.I) -
          Complex.exp (((-v * a : Real) : Complex) * Complex.I)) /
            (-((v : Complex) * Complex.I))) *
          (Problem520.harperFejerTriangle (T⁻¹ * v) : Complex) by ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htri0]
  exact (mul_le_mul hquot htri1 htri0 (abs_nonneg _)).trans_eq (mul_one _)

theorem norm_harperBivariateFejerRectangleIntegrand_le
    (phi psi : (Real × Real) → Complex)
    (T a b c d : Real) (z : Real × Real) :
    ‖harperBivariateFejerRectangleIntegrand phi psi T a b c d z‖ ≤
      ‖phi z - psi z‖ * |b - a| * |d - c| := by
  unfold harperBivariateFejerRectangleIntegrand
  rw [norm_mul, norm_mul]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left
      (norm_harperFejerIntervalMultiplier_le T a b z.1)
      (norm_nonneg (phi z - psi z)))
    (norm_harperFejerIntervalMultiplier_le T c d z.2)
    (norm_nonneg _) (mul_nonneg (norm_nonneg _) (abs_nonneg _))

/-- A cubic/quartic bivariate characteristic estimate gives an explicit
smoothed-rectangle comparison.  The crude constants are intentional: the
scheduled block endpoints are doubly exponential, so only the powers of `T`
matter downstream. -/
theorem abs_harperBivariateSmoothRectangle_sub_le_of_identity
    (mu nu : Measure (Real × Real))
    (T A B a b c d : Real)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hidentity : HarperBivariateFejerRectangleIdentity mu nu T)
    (hchar : ∀ z ∈ Icc (-T) T ×ˢ Icc (-T) T,
      ‖harperBivariateCharacteristic mu z -
          harperBivariateCharacteristic nu z‖ ≤
        A * (|z.1| + |z.2|) ^ (3 : Nat) +
          B * (|z.1| + |z.2|) ^ (4 : Nat)) :
    |harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T) mu a b c d -
        harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T) nu a b c d| ≤
      (2 * Real.pi)⁻¹ ^ (2 : Nat) * |b - a| * |d - c| *
        (32 * A * T ^ (5 : Nat) + 64 * B * T ^ (6 : Nat)) := by
  let box : Set (Real × Real) := Icc (-T) T ×ˢ Icc (-T) T
  let phi := harperBivariateCharacteristic mu
  let psi := harperBivariateCharacteristic nu
  let f := harperBivariateFejerRectangleIntegrand phi psi T a b c d
  let lambda : Measure (Real × Real) := volume
  let M : Real := |b - a| * |d - c| *
    (A * (2 * T) ^ (3 : Nat) + B * (2 * T) ^ (4 : Nat))
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hfBound : ∀ z ∈ box, ‖f z‖ ≤ M := by
    intro z hz
    have hz1 : |z.1| ≤ T := by
      rw [abs_le]
      exact ⟨by linarith [hz.1.1], hz.1.2⟩
    have hz2 : |z.2| ≤ T := by
      rw [abs_le]
      exact ⟨by linarith [hz.2.1], hz.2.2⟩
    have hradius : |z.1| + |z.2| ≤ 2 * T := by linarith
    calc
      ‖f z‖ ≤ ‖phi z - psi z‖ * |b - a| * |d - c| :=
        norm_harperBivariateFejerRectangleIntegrand_le
          phi psi T a b c d z
      _ ≤ (A * (|z.1| + |z.2|) ^ (3 : Nat) +
            B * (|z.1| + |z.2|) ^ (4 : Nat)) *
          |b - a| * |d - c| := by
        gcongr
        exact hchar z hz
      _ ≤ (A * (2 * T) ^ (3 : Nat) + B * (2 * T) ^ (4 : Nat)) *
          |b - a| * |d - c| := by
        gcongr
      _ = M := by dsimp only [M]; ring
  have hboxFinite : lambda box < ∞ := by
    exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hnorm : ‖∫ z in box, f z ∂lambda‖ ≤ M * lambda.real box := by
    apply norm_setIntegral_le_of_norm_le_const_ae' hboxFinite
    filter_upwards with z
    intro hz
    exact hfBound z hz
  have hboxVolume : lambda.real box = (2 * T) ^ (2 : Nat) := by
    dsimp only [lambda, box]
    rw [Measure.volume_eq_prod, Measure.real, Measure.prod_prod,
      Real.volume_Icc, ENNReal.toReal_mul]
    simp only [sub_neg_eq_add,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ T + T)]
    ring
  have hid := hidentity a b c d
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hid,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
  change
    (2 * Real.pi)⁻¹ ^ (2 : Nat) * ‖∫ z in box, f z ∂lambda‖ ≤ _
  calc
    _ ≤ (2 * Real.pi)⁻¹ ^ (2 : Nat) * (M * lambda.real box) := by
      gcongr
    _ = (2 * Real.pi)⁻¹ ^ (2 : Nat) * |b - a| * |d - c| *
        (32 * A * T ^ (5 : Nat) + 64 * B * T ^ (6 : Nat)) := by
      rw [hboxVolume]
      dsimp only [M]
      ring

/-! ## Scheduled Rademacher block specialization -/

/-- The exact Gaussian characteristic factor associated with a scheduled
two-height block.  This is kept as a named function so that the construction
of the comparison Gaussian law and the Fourier estimate meet at a small,
explicit interface. -/
noncomputable def harperScheduledTwoHeightGaussianCharacteristic
    (y j : Nat) (t s : Real) (z : Real × Real) : Complex :=
  Complex.exp
    (-((harperTwoHeightProjectedBlockVariance y
      (Problem520.harperScheduledPrimeBlock y j) t s z.1 z.2 / 2 :
        Real) : Complex))

/-- The scheduled bivariate Rademacher law has the explicit
cubic/quartic characteristic estimate required by Fejer smoothing. -/
theorem norm_harperBivariateCharacteristic_scheduledVectorLaw_sub_gaussian_le
    (y j : Nat) (t s v w : Real)
    (hfrequency :
      2 * (|v| + |w|) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real)) :
    ‖harperBivariateCharacteristic
          (harperTwoHeightPrimeBlockVectorLaw y
            (Problem520.harperScheduledPrimeBlock y j) t s) (v, w) -
        harperScheduledTwoHeightGaussianCharacteristic y j t s (v, w)‖ ≤
      (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
        (16 * (|v| + |w|) ^ (3 : Nat) +
          2 * (|v| + |w|) ^ (4 : Nat)) := by
  unfold harperBivariateCharacteristic
    harperScheduledTwoHeightGaussianCharacteristic
  exact
    norm_charFunDual_harperTwoHeightScheduledVectorLaw_sub_gaussian_le
      y j t s v w hfrequency

/-- Once the comparison measure has the exact covariance characteristic and
the product-Fejer inversion identity is available, the actual scheduled
Rademacher block has an explicit two-dimensional smoothed-cell error. -/
theorem abs_harperScheduledTwoHeightSmoothRectangle_sub_gaussian_le
    (y j : Nat) (t s : Real) (nu : Measure (Real × Real))
    (T a b c d : Real)
    (hT : 0 ≤ T)
    (hfrequency :
      4 * T ≤ Real.sqrt (Problem520.harperBlockEndpoint j : Real))
    (hnu : ∀ z : Real × Real,
      harperBivariateCharacteristic nu z =
        harperScheduledTwoHeightGaussianCharacteristic y j t s z)
    (hidentity : HarperBivariateFejerRectangleIdentity
      (harperTwoHeightPrimeBlockVectorLaw y
        (Problem520.harperScheduledPrimeBlock y j) t s) nu T) :
    |harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T)
          (harperTwoHeightPrimeBlockVectorLaw y
            (Problem520.harperScheduledPrimeBlock y j) t s) a b c d -
        harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T) nu a b c d| ≤
      (2 * Real.pi)⁻¹ ^ (2 : Nat) * |b - a| * |d - c| *
        (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
          (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat)) := by
  let q : Real :=
    (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hchar : ∀ z ∈ Icc (-T) T ×ˢ Icc (-T) T,
      ‖harperBivariateCharacteristic
          (harperTwoHeightPrimeBlockVectorLaw y
            (Problem520.harperScheduledPrimeBlock y j) t s) z -
        harperBivariateCharacteristic nu z‖ ≤
      (16 * q) * (|z.1| + |z.2|) ^ (3 : Nat) +
        (2 * q) * (|z.1| + |z.2|) ^ (4 : Nat) := by
    intro z hz
    have hz1 : |z.1| ≤ T := by
      rw [abs_le]
      exact ⟨by linarith [hz.1.1], hz.1.2⟩
    have hz2 : |z.2| ≤ T := by
      rw [abs_le]
      exact ⟨by linarith [hz.2.1], hz.2.2⟩
    have hwindow :
        2 * (|z.1| + |z.2|) ≤
          Real.sqrt (Problem520.harperBlockEndpoint j : Real) := by
      calc
        2 * (|z.1| + |z.2|) ≤ 4 * T := by linarith
        _ ≤ _ := hfrequency
    rw [hnu]
    have hbase :=
      norm_harperBivariateCharacteristic_scheduledVectorLaw_sub_gaussian_le
        y j t s z.1 z.2 hwindow
    calc
      _ ≤ q * (16 * (|z.1| + |z.2|) ^ (3 : Nat) +
          2 * (|z.1| + |z.2|) ^ (4 : Nat)) := by
        simpa only [q] using hbase
      _ = (16 * q) * (|z.1| + |z.2|) ^ (3 : Nat) +
          (2 * q) * (|z.1| + |z.2|) ^ (4 : Nat) := by ring
  have hbase := abs_harperBivariateSmoothRectangle_sub_le_of_identity
    (harperTwoHeightPrimeBlockVectorLaw y
      (Problem520.harperScheduledPrimeBlock y j) t s) nu
    T (16 * q) (2 * q) a b c d hT (by positivity) (by positivity)
    hidentity hchar
  calc
    _ ≤ (2 * Real.pi)⁻¹ ^ (2 : Nat) * |b - a| * |d - c| *
        (32 * (16 * q) * T ^ (5 : Nat) +
          64 * (2 * q) * T ^ (6 : Nat)) := hbase
    _ = (2 * Real.pi)⁻¹ ^ (2 : Nat) * |b - a| * |d - c| *
        q * (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat)) := by ring
    _ = _ := by rfl

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.norm_harperFejerIntervalMultiplier_le
#print axioms Erdos.Problem1144.abs_harperBivariateSmoothRectangle_sub_le_of_identity
#print axioms Erdos.Problem1144.norm_harperBivariateCharacteristic_scheduledVectorLaw_sub_gaussian_le
#print axioms Erdos.Problem1144.abs_harperScheduledTwoHeightSmoothRectangle_sub_gaussian_le
