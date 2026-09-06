import Erdos.Problem1144.HarperTwoHeightCovariance
import Erdos.Problem1144.HarperBivariateFejerUnsmoothing

open Finset MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Decorrelation of the covariance-matched Gaussian block

The exact comparison Gaussian has small off-diagonal covariance after the
height-coherence block.  This module introduces the product of its exact
marginals and compares their characteristic functions.  This keeps the
Gaussian ballot endpoint variance-matched while isolating correlation in a
single scalar term.
-/

noncomputable def harperTwoHeightCoordinateVarianceNNReal
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s u : Real) : NNReal :=
  ⟨harperTwoHeightBlockCoordinateCovariance y S t s u u,
    harperTwoHeightBlockCoordinateVariance_nonneg y S t s u⟩

@[simp] theorem coe_harperTwoHeightCoordinateVarianceNNReal
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s u : Real) :
    (harperTwoHeightCoordinateVarianceNNReal y S t s u : Real) =
      harperTwoHeightBlockCoordinateCovariance y S t s u u := rfl

/-- Product of the two exact marginal Gaussian laws of one block. -/
noncomputable def harperTwoHeightIndependentGaussianBlockLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) : Measure (Real × Real) :=
  (gaussianReal 0
      (harperTwoHeightCoordinateVarianceNNReal y S t s t)).prod
    (gaussianReal 0
      (harperTwoHeightCoordinateVarianceNNReal y S t s s))

instance harperTwoHeightIndependentGaussianBlockLaw_isProbabilityMeasure
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    IsProbabilityMeasure
      (harperTwoHeightIndependentGaussianBlockLaw y S t s) := by
  unfold harperTwoHeightIndependentGaussianBlockLaw
  infer_instance

theorem harperBivariateCharacteristic_independentGaussianBlockLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) :
    harperBivariateCharacteristic
        (harperTwoHeightIndependentGaussianBlockLaw y S t s) (v, w) =
      Complex.exp
        (-(((v ^ (2 : Nat) *
              harperTwoHeightBlockCoordinateCovariance y S t s t t +
            w ^ (2 : Nat) *
              harperTwoHeightBlockCoordinateCovariance y S t s s s) / 2 :
                Real) : Complex)) := by
  rw [harperBivariateCharacteristic]
  unfold harperTwoHeightIndependentGaussianBlockLaw
  rw [charFunDual_prod]
  have hvcomp :
      (harperTwoHeightProjection v w).comp
          (ContinuousLinearMap.inl Real Real Real) =
        InnerProductSpace.toDualMap Real Real v := by
    ext
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      harperTwoHeightProjection_apply, mul_zero, add_zero,
      InnerProductSpace.toDualMap_apply_apply]
    rw [real_inner_eq_re_inner Real]
    simp [RCLike.inner_apply]
  have hwcomp :
      (harperTwoHeightProjection v w).comp
          (ContinuousLinearMap.inr Real Real Real) =
        InnerProductSpace.toDualMap Real Real w := by
    ext
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      harperTwoHeightProjection_apply, InnerProductSpace.toDualMap_apply_apply]
    rw [real_inner_eq_re_inner Real]
    simp [RCLike.inner_apply]
  rw [hvcomp, hwcomp, ← charFun_eq_charFunDual_toDualMap,
    ← charFun_eq_charFunDual_toDualMap]
  change
    charFun (gaussianReal 0
        (harperTwoHeightCoordinateVarianceNNReal y S t s t)) v *
      charFun (gaussianReal 0
        (harperTwoHeightCoordinateVarianceNNReal y S t s s)) w = _
  rw [charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add]
  simp only [coe_harperTwoHeightCoordinateVarianceNNReal]
  congr 1
  push_cast
  ring

/-- `exp(-x)` is one-Lipschitz on the nonnegative half-line. -/
theorem abs_exp_neg_sub_exp_neg_le_abs_sub
    {A B : Real} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |Real.exp (-A) - Real.exp (-B)| ≤ |A - B| := by
  wlog hAB : A ≤ B generalizing A B with hsymm
  · have hBA : B ≤ A := le_of_not_ge hAB
    have h := hsymm hB hA hBA
    simpa only [abs_sub_comm] using h
  have hExpOrder : Real.exp (-B) ≤ Real.exp (-A) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hAexp : Real.exp (-A) ≤ 1 := by
    simpa only [← Real.exp_zero] using Real.exp_le_exp.mpr (by linarith)
  have hgap0 : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hgapExp0 : 0 ≤ 1 - Real.exp (-(B - A)) := by
    have : Real.exp (-(B - A)) ≤ 1 := by
      simpa only [← Real.exp_zero] using Real.exp_le_exp.mpr (by linarith)
    linarith
  have hgap : 1 - Real.exp (-(B - A)) ≤ B - A := by
    have h := Real.add_one_le_exp (-(B - A))
    linarith
  rw [abs_of_nonneg (sub_nonneg.mpr hExpOrder),
    abs_of_nonpos (sub_nonpos.mpr hAB)]
  have hfactor :
      Real.exp (-A) - Real.exp (-B) =
        Real.exp (-A) * (1 - Real.exp (-(B - A))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2
    ring
  rw [hfactor]
  calc
    Real.exp (-A) * (1 - Real.exp (-(B - A))) ≤
        1 * (1 - Real.exp (-(B - A))) :=
      mul_le_mul_of_nonneg_right hAexp hgapExp0
    _ ≤ B - A := by simpa using hgap
    _ = -(A - B) := by ring

/-- The exact correlated Gaussian and the product of its exact marginals
differ in characteristic function by at most the covariance times the two
Fourier coordinates. -/
theorem norm_harperBivariateCharacteristic_gaussianLaw_sub_independent_le
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) :
    ‖harperBivariateCharacteristic (harperTwoHeightGaussianLaw y S t s) (v, w) -
        harperBivariateCharacteristic
          (harperTwoHeightIndependentGaussianBlockLaw y S t s) (v, w)‖ ≤
      |harperTwoHeightBlockCoordinateCovariance y S t s t s| * |v| * |w| := by
  let a := harperTwoHeightBlockCoordinateCovariance y S t s t t
  let b := harperTwoHeightBlockCoordinateCovariance y S t s s s
  let q := harperTwoHeightBlockCoordinateCovariance y S t s t s
  let A : Real := (v ^ (2 : Nat) * a + 2 * v * w * q + w ^ (2 : Nat) * b) / 2
  let B : Real := (v ^ (2 : Nat) * a + w ^ (2 : Nat) * b) / 2
  have hA : 0 ≤ A := by
    dsimp only [A, a, b, q]
    rw [← harperTwoHeightProjectedBlockVariance_eq_coordinateCovariance]
    exact div_nonneg (harperTwoHeightProjectedBlockVariance_nonneg
      y S t s v w) (by norm_num)
  have hB : 0 ≤ B := by
    dsimp only [B, a, b]
    exact div_nonneg (add_nonneg
      (mul_nonneg (sq_nonneg _)
        (harperTwoHeightBlockCoordinateVariance_nonneg y S t s t))
      (mul_nonneg (sq_nonneg _)
        (harperTwoHeightBlockCoordinateVariance_nonneg y S t s s)))
      (by norm_num)
  rw [harperBivariateCharacteristic_harperTwoHeightGaussianLaw,
    harperBivariateCharacteristic_independentGaussianBlockLaw,
    harperTwoHeightProjectedBlockVariance_eq_coordinateCovariance]
  change ‖Complex.exp (-(A : Complex)) - Complex.exp (-(B : Complex))‖ ≤ _
  rw [← Complex.ofReal_neg, ← Complex.ofReal_neg,
    ← Complex.ofReal_exp, ← Complex.ofReal_exp,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hbase := abs_exp_neg_sub_exp_neg_le_abs_sub hA hB
  calc
    |Real.exp (-A) - Real.exp (-B)| ≤ |A - B| := hbase
    _ = |q| * |v| * |w| := by
      dsimp only [A, B]
      rw [show
        (v ^ (2 : Nat) * a + 2 * v * w * q + w ^ (2 : Nat) * b) / 2 -
            (v ^ (2 : Nat) * a + w ^ (2 : Nat) * b) / 2 =
          v * w * q by ring,
        abs_mul, abs_mul]
      ring
    _ = _ := by rfl

/-- Quadratic characteristic error gives a `T^4` product-Fejer rectangle
error. -/
theorem abs_harperBivariateSmoothRectangle_sub_le_of_identity_quadratic
    (mu nu : Measure (Real × Real))
    (T A a b c d : Real)
    (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hidentity : HarperBivariateFejerRectangleIdentity mu nu T)
    (hchar : ∀ z ∈ Icc (-T) T ×ˢ Icc (-T) T,
      ‖harperBivariateCharacteristic mu z -
          harperBivariateCharacteristic nu z‖ ≤
        A * (|z.1| + |z.2|) ^ (2 : Nat)) :
    |harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T) mu a b c d -
        harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T) nu a b c d| ≤
      (2 * Real.pi)⁻¹ ^ (2 : Nat) * |b - a| * |d - c| *
        (16 * A * T ^ (4 : Nat)) := by
  let box : Set (Real × Real) := Icc (-T) T ×ˢ Icc (-T) T
  let phi := harperBivariateCharacteristic mu
  let psi := harperBivariateCharacteristic nu
  let f := harperBivariateFejerRectangleIntegrand phi psi T a b c d
  let lambda : Measure (Real × Real) := volume
  let M : Real := |b - a| * |d - c| * (A * (2 * T) ^ (2 : Nat))
  have hM : 0 ≤ M := by dsimp only [M]; positivity
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
      _ ≤ (A * (|z.1| + |z.2|) ^ (2 : Nat)) *
          |b - a| * |d - c| := by
        gcongr
        exact hchar z hz
      _ ≤ (A * (2 * T) ^ (2 : Nat)) *
          |b - a| * |d - c| := by gcongr
      _ = M := by dsimp only [M]; ring
  have hboxFinite : lambda box < ∞ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
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
        (16 * A * T ^ (4 : Nat)) := by
      rw [hboxVolume]
      dsimp only [M]
      ring

/-- Smoothed rectangle decorrelation for the exact Gaussian block. -/
theorem abs_harperTwoHeightGaussianSmoothRectangle_sub_independent_le
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s T a b c d : Real) (hT : 0 < T) :
    |harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T)
          (harperTwoHeightGaussianLaw y S t s) a b c d -
        harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T)
          (harperTwoHeightIndependentGaussianBlockLaw y S t s) a b c d| ≤
      (2 * Real.pi)⁻¹ ^ (2 : Nat) * |b - a| * |d - c| *
        (16 * |harperTwoHeightBlockCoordinateCovariance y S t s t s| *
          T ^ (4 : Nat)) := by
  apply abs_harperBivariateSmoothRectangle_sub_le_of_identity_quadratic
    (harperTwoHeightGaussianLaw y S t s)
    (harperTwoHeightIndependentGaussianBlockLaw y S t s)
    T |harperTwoHeightBlockCoordinateCovariance y S t s t s|
    a b c d hT.le (abs_nonneg _)
    (harperBivariateFejerRectangleIdentity_of_pos _ _ hT)
  intro z hz
  have hbase :=
    norm_harperBivariateCharacteristic_gaussianLaw_sub_independent_le
      y S t s z.1 z.2
  calc
    _ ≤ |harperTwoHeightBlockCoordinateCovariance y S t s t s| *
        |z.1| * |z.2| := hbase
    _ ≤ |harperTwoHeightBlockCoordinateCovariance y S t s t s| *
        (|z.1| + |z.2|) ^ (2 : Nat) := by
      have hnonneg1 : 0 ≤ |z.1| := abs_nonneg _
      have hnonneg2 : 0 ≤ |z.2| := abs_nonneg _
      have hprod : |z.1| * |z.2| ≤
          (|z.1| + |z.2|) ^ (2 : Nat) := by nlinarith
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hprod
          (abs_nonneg (harperTwoHeightBlockCoordinateCovariance y S t s t s))

/-- Ordinary-rectangle decorrelation: the exact correlated Gaussian mass is
bounded by its independent exact-marginal product on a slightly expanded
rectangle, plus explicit Fejer tail and Fourier errors. -/
theorem harperTwoHeightGaussianRectangleMass_le_independentExpanded
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s T : Real) {a b c d delta alpha : Real}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hT : 0 < T) (hdelta : 0 ≤ delta) (halpha0 : 0 ≤ alpha)
    (halpha1 : alpha ≤ 1)
    (htail : (Problem520.harperFejerMeasureScaled T).real
      {u : Real | delta < |u|} ≤ alpha) :
    (1 - alpha) ^ (2 : Nat) *
        (harperTwoHeightGaussianLaw y S t s).real
          (Ioc a b ×ˢ Ioc c d) ≤
      (harperTwoHeightIndependentGaussianBlockLaw y S t s).real
          (Ioc (a - 2 * delta) (b + 2 * delta) ×ˢ
            Ioc (c - 2 * delta) (d + 2 * delta)) +
        alpha +
        (2 * Real.pi)⁻¹ ^ (2 : Nat) *
          |(b + delta) - (a - delta)| *
          |(d + delta) - (c - delta)| *
          (16 * |harperTwoHeightBlockCoordinateCovariance y S t s t s| *
            T ^ (4 : Nat)) := by
  let kappa := Problem520.harperFejerMeasureScaled T
  let mu := harperTwoHeightGaussianLaw y S t s
  let nu := harperTwoHeightIndependentGaussianBlockLaw y S t s
  let E : Real :=
    (2 * Real.pi)⁻¹ ^ (2 : Nat) *
      |(b + delta) - (a - delta)| *
      |(d + delta) - (c - delta)| *
      (16 * |harperTwoHeightBlockCoordinateCovariance y S t s t s| *
        T ^ (4 : Nat))
  have hlower := one_sub_sq_mul_rectangleMass_le_smoothExpanded
    kappa mu hab hcd hdelta halpha1 htail
  have hsmooth := abs_harperTwoHeightGaussianSmoothRectangle_sub_independent_le
    y S t s T (a - delta) (b + delta) (c - delta) (d + delta) hT
  have hsmoothOne :
      harperBivariateSmoothRectangle kappa mu
          (a - delta) (b + delta) (c - delta) (d + delta) ≤
        harperBivariateSmoothRectangle kappa nu
          (a - delta) (b + delta) (c - delta) (d + delta) + E := by
    have habs := le_abs_self
      (harperBivariateSmoothRectangle kappa mu
          (a - delta) (b + delta) (c - delta) (d + delta) -
        harperBivariateSmoothRectangle kappa nu
          (a - delta) (b + delta) (c - delta) (d + delta))
    have hle := habs.trans (by simpa only [kappa, mu, nu, E] using hsmooth)
    linarith
  have hupper := smoothRectangle_le_expandedRectangleMass_add_tail
    kappa nu
      (a := a - delta) (b := b + delta)
      (c := c - delta) (d := d + delta)
      (delta := delta) (alpha := alpha)
      (by linarith) (by linarith) hdelta halpha0 htail
  change (1 - alpha) ^ (2 : Nat) * mu.real (Ioc a b ×ˢ Ioc c d) ≤ _
  calc
    _ ≤ harperBivariateSmoothRectangle kappa mu
        (a - delta) (b + delta) (c - delta) (d + delta) := hlower
    _ ≤ harperBivariateSmoothRectangle kappa nu
        (a - delta) (b + delta) (c - delta) (d + delta) + E := hsmoothOne
    _ ≤ nu.real
          (Ioc ((a - delta) - delta) ((b + delta) + delta) ×ˢ
            Ioc ((c - delta) - delta) ((d + delta) + delta)) +
          alpha + E := by
      simpa only [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hupper E
    _ = nu.real
          (Ioc (a - 2 * delta) (b + 2 * delta) ×ˢ
            Ioc (c - 2 * delta) (d + 2 * delta)) + alpha + E := by
      ring_nf
    _ = _ := by rfl

theorem harperTwoHeightGaussianRectangleMass_le_independentExpanded_explicit
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s T r : Real) {a b c d : Real}
    (hab : a ≤ b) (hcd : c ≤ d) (hT : 0 < T) (hr : 2 ≤ r) :
    (1 - 2 / r) ^ (2 : Nat) *
        (harperTwoHeightGaussianLaw y S t s).real
          (Ioc a b ×ˢ Ioc c d) ≤
      (harperTwoHeightIndependentGaussianBlockLaw y S t s).real
          (Ioc (a - 2 * (r / T)) (b + 2 * (r / T)) ×ˢ
            Ioc (c - 2 * (r / T)) (d + 2 * (r / T))) +
        2 / r +
        (2 * Real.pi)⁻¹ ^ (2 : Nat) *
          |(b + r / T) - (a - r / T)| *
          |(d + r / T) - (c - r / T)| *
          (16 * |harperTwoHeightBlockCoordinateCovariance y S t s t s| *
            T ^ (4 : Nat)) := by
  apply harperTwoHeightGaussianRectangleMass_le_independentExpanded
    y S t s T hab hcd hT
  · positivity
  · positivity
  · rw [div_le_one (by positivity : (0 : Real) < r)]
    linarith
  · simpa only using harperFejerMeasureScaled_tail_le_two_div hT hr

/-- Complete one-block local comparison: actual tilted Rademacher pair to the
product of the exact Gaussian marginals.  Applying the two ordinary-rectangle
comparisons successively enlarges the rectangle by `4r/T` and squares the
Fejer retention factor. -/
theorem harperScheduledTwoHeightRectangleMass_le_independentGaussian_explicit
    (y j : Nat) (t s T r : Real) {a b c d : Real}
    (hab : a ≤ b) (hcd : c ≤ d) (hT : 0 < T) (hr : 2 ≤ r)
    (hfrequency :
      4 * T ≤ Real.sqrt (Problem520.harperBlockEndpoint j : Real)) :
    ((1 - 2 / r) ^ (2 : Nat)) ^ (2 : Nat) *
        (harperTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y j) t s).real
            (Ioc a b ×ˢ Ioc c d) ≤
      (harperTwoHeightIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y j) t s).real
          (Ioc (a - 4 * (r / T)) (b + 4 * (r / T)) ×ˢ
            Ioc (c - 4 * (r / T)) (d + 4 * (r / T))) +
        2 / r +
        (2 * Real.pi)⁻¹ ^ (2 : Nat) *
          |(b + 3 * (r / T)) - (a - 3 * (r / T))| *
          |(d + 3 * (r / T)) - (c - 3 * (r / T))| *
          (16 *
            |harperTwoHeightBlockCoordinateCovariance y
              (Problem520.harperScheduledPrimeBlock y j) t s t s| *
            T ^ (4 : Nat)) +
        (1 - 2 / r) ^ (2 : Nat) *
          (2 / r +
            (2 * Real.pi)⁻¹ ^ (2 : Nat) *
              |(b + r / T) - (a - r / T)| *
              |(d + r / T) - (c - r / T)| *
              (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
                (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat))) := by
  let beta : Real := (1 - 2 / r) ^ (2 : Nat)
  let ER : Real :=
    (2 * Real.pi)⁻¹ ^ (2 : Nat) *
      |(b + r / T) - (a - r / T)| *
      |(d + r / T) - (c - r / T)| *
      (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
        (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat))
  let EG : Real :=
    (2 * Real.pi)⁻¹ ^ (2 : Nat) *
      |(b + 3 * (r / T)) - (a - 3 * (r / T))| *
      |(d + 3 * (r / T)) - (c - 3 * (r / T))| *
      (16 * |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) t s t s| *
        T ^ (4 : Nat))
  let actual : Real :=
    (harperTwoHeightPrimeBlockVectorLaw y
      (Problem520.harperScheduledPrimeBlock y j) t s).real
      (Ioc a b ×ˢ Ioc c d)
  let gaussian : Real :=
    (harperTwoHeightGaussianLaw y
      (Problem520.harperScheduledPrimeBlock y j) t s).real
      (Ioc (a - 2 * (r / T)) (b + 2 * (r / T)) ×ˢ
        Ioc (c - 2 * (r / T)) (d + 2 * (r / T)))
  let independent : Real :=
    (harperTwoHeightIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y j) t s).real
      (Ioc (a - 4 * (r / T)) (b + 4 * (r / T)) ×ˢ
        Ioc (c - 4 * (r / T)) (d + 4 * (r / T)))
  have hbeta : 0 ≤ beta := by dsimp only [beta]; positivity
  have hdelta : 0 ≤ r / T := div_nonneg (by linarith) hT.le
  have hactual : beta * actual ≤ gaussian + 2 / r + ER := by
    simpa only [beta, actual, gaussian, ER] using
      harperScheduledTwoHeightRectangleMass_le_gaussianExpanded_explicit
        y j t s T r hab hcd hT hr hfrequency
  have hgaussian : beta * gaussian ≤ independent + 2 / r + EG := by
    have h :=
      harperTwoHeightGaussianRectangleMass_le_independentExpanded_explicit
        y (Problem520.harperScheduledPrimeBlock y j) t s T r
          (a := a - 2 * (r / T)) (b := b + 2 * (r / T))
          (c := c - 2 * (r / T)) (d := d + 2 * (r / T))
          (by linarith) (by linarith) hT hr
    dsimp only [beta, gaussian, independent, EG]
    convert h using 1 <;> ring_nf
  have hmul := mul_le_mul_of_nonneg_left hactual hbeta
  change beta ^ (2 : Nat) * actual ≤
    independent + 2 / r + EG + beta * (2 / r + ER)
  calc
    beta ^ (2 : Nat) * actual = beta * (beta * actual) := by ring
    _ ≤ beta * (gaussian + 2 / r + ER) := hmul
    _ = beta * gaussian + beta * (2 / r + ER) := by ring
    _ ≤ (independent + 2 / r + EG) + beta * (2 / r + ER) :=
      add_le_add hgaussian le_rfl
    _ = _ := by ring

#print axioms Erdos.Problem1144.harperBivariateCharacteristic_independentGaussianBlockLaw
#print axioms Erdos.Problem1144.abs_exp_neg_sub_exp_neg_le_abs_sub
#print axioms Erdos.Problem1144.norm_harperBivariateCharacteristic_gaussianLaw_sub_independent_le
#print axioms Erdos.Problem1144.abs_harperTwoHeightGaussianSmoothRectangle_sub_independent_le
#print axioms Erdos.Problem1144.harperTwoHeightGaussianRectangleMass_le_independentExpanded_explicit
#print axioms Erdos.Problem1144.harperScheduledTwoHeightRectangleMass_le_independentGaussian_explicit

end

end Problem1144
end Erdos
