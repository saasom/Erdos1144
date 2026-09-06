import Erdos.Problem1144.HarperCorrelatedGaussianBallot
import Erdos.Problem1144.HarperGaussianDecorrelation

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Exact regression form of the covariance-matched Gaussian

For one scheduled block write its covariance matrix as

`[[a, q], [q, b]]`.

When `a > 0`, the corresponding Gaussian pair is exactly

`(X, (q / a) X + W)`,

where `X` and `W` are independent centered Gaussians of variances `a` and
`b - q^2 / a`.  This file proves that identity at the level of measures.
It is the bridge from the arithmetic covariance estimates to the
summably-correlated Gaussian ballot theorem.
-/

/-- The one-block triangular regression map. -/
noncomputable def harperGaussianRegressionBlockMap (lambda : Real) :
    (Real × Real) →L[Real] (Real × Real) :=
  (ContinuousLinearMap.fst Real Real Real).prod
    (lambda • ContinuousLinearMap.fst Real Real Real +
      ContinuousLinearMap.snd Real Real Real)

@[simp] theorem harperGaussianRegressionBlockMap_apply
    (lambda : Real) (z : Real × Real) :
    harperGaussianRegressionBlockMap lambda z =
      (z.1, lambda * z.1 + z.2) := by
  simp [harperGaussianRegressionBlockMap]

/-- A generic centered Gaussian regression block. -/
noncomputable def harperGaussianRegressionBlockLaw
    (variance residualVariance : NNReal) (lambda : Real) :
    Measure (Real × Real) :=
  Measure.map (harperGaussianRegressionBlockMap lambda)
    ((gaussianReal 0 variance).prod (gaussianReal 0 residualVariance))

instance harperGaussianRegressionBlockLaw_isProbabilityMeasure
    (variance residualVariance : NNReal) (lambda : Real) :
    IsProbabilityMeasure
      (harperGaussianRegressionBlockLaw variance residualVariance lambda) := by
  unfold harperGaussianRegressionBlockLaw
  exact Measure.isProbabilityMeasure_map
    (harperGaussianRegressionBlockMap lambda).measurable.aemeasurable

/-! ## Pairing and unpairing finite paths -/

/-- Zip two scalar paths into a path of pairs, as a continuous linear map. -/
noncomputable def harperPairPathZipCLM (n : Nat) :
    ((Fin n → Real) × (Fin n → Real)) →L[Real] (Fin n → Real × Real) :=
  ContinuousLinearMap.pi fun i ↦
    ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst Real (Fin n → Real) (Fin n → Real))).prod
      ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd Real (Fin n → Real) (Fin n → Real)))

@[simp] theorem harperPairPathZipCLM_apply
    {n : Nat} (z : (Fin n → Real) × (Fin n → Real)) :
    harperPairPathZipCLM n z = fun i ↦ (z.1 i, z.2 i) := by
  rfl

/-- Unzip a path of pairs into its two scalar paths. -/
noncomputable def harperPairPathUnzipCLM (n : Nat) :
    (Fin n → Real × Real) →L[Real]
      ((Fin n → Real) × (Fin n → Real)) :=
  (ContinuousLinearMap.pi fun i ↦
      (ContinuousLinearMap.fst Real Real Real).comp
        (ContinuousLinearMap.proj i)).prod
    (ContinuousLinearMap.pi fun i ↦
      (ContinuousLinearMap.snd Real Real Real).comp
        (ContinuousLinearMap.proj i))

@[simp] theorem harperPairPathUnzipCLM_apply
    {n : Nat} (z : Fin n → Real × Real) :
    harperPairPathUnzipCLM n z =
      ((fun i ↦ (z i).1), fun i ↦ (z i).2) := by
  rfl

@[simp] theorem harperPairPathUnzipCLM_zip
    {n : Nat} (z : (Fin n → Real) × (Fin n → Real)) :
    harperPairPathUnzipCLM n (harperPairPathZipCLM n z) = z := by
  ext <;> rfl

@[simp] theorem harperPairPathZipCLM_unzip
    {n : Nat} (z : Fin n → Real × Real) :
    harperPairPathZipCLM n (harperPairPathUnzipCLM n z) = z := by
  ext <;> rfl

/-- Zipping two independent finite Gaussian product paths is the finite
product of the corresponding independent Gaussian pairs. -/
theorem map_harperPairPathZipCLM_gaussianSource_eq_pi_prod
    {n : Nat} (variance residualVariance : Fin n → NNReal) :
    Measure.map (harperPairPathZipCLM n)
        ((Measure.pi (fun i ↦ gaussianReal 0 (variance i))).prod
          (Measure.pi (fun i ↦ gaussianReal 0 (residualVariance i)))) =
      Measure.pi (fun i ↦
        (gaussianReal 0 (variance i)).prod
          (gaussianReal 0 (residualVariance i))) := by
  classical
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_pi, charFunDual_pi,
    charFunDual_pi]
  simp_rw [charFunDual_prod]
  rw [Finset.prod_mul_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    congr 1
    apply ContinuousLinearMap.ext
    intro x
    simp [harperPairPathZipCLM]
    congr 1
    funext j
    by_cases hij : i = j
    · subst j
      simp [Pi.single, Function.update]
    · have hji : j ≠ i := fun h ↦ hij h.symm
      simp [Pi.single, Function.update, hij, hji]
  · apply Finset.prod_congr rfl
    intro i hi
    congr 1
    apply ContinuousLinearMap.ext
    intro x
    simp [harperPairPathZipCLM]
    congr 1
    funext j
    by_cases hij : i = j
    · subst j
      simp [Pi.single, Function.update]
    · have hji : j ≠ i := fun h ↦ hij h.symm
      simp [Pi.single, Function.update, hij, hji]

/-- Coordinatewise triangular regression on a path of independent pairs. -/
noncomputable def harperGaussianRegressionPairPathCLM
    {n : Nat} (lambda : Fin n → Real) :
    (Fin n → Real × Real) →L[Real] (Fin n → Real × Real) :=
  ContinuousLinearMap.pi fun i ↦
    (harperGaussianRegressionBlockMap (lambda i)).comp
      (ContinuousLinearMap.proj i)

@[simp] theorem harperGaussianRegressionPairPathCLM_apply
    {n : Nat} (lambda : Fin n → Real) (z : Fin n → Real × Real) :
    harperGaussianRegressionPairPathCLM lambda z =
      fun i ↦ ((z i).1, lambda i * (z i).1 + (z i).2) := by
  rfl

/-- The path-level regression law, after zipping its two coordinates, is the
finite product of the one-block regression laws. -/
theorem map_harperPairPathZipCLM_regressedGaussian_eq_pi
    {n : Nat} (variance residualVariance : Fin n → NNReal)
    (lambda : Fin n → Real) :
    Measure.map (harperPairPathZipCLM n)
        (harperRegressedGaussianTwoWalkMeasure
          variance residualVariance lambda) =
      Measure.pi (fun i ↦
        harperGaussianRegressionBlockLaw
          (variance i) (residualVariance i) (lambda i)) := by
  let source := harperGaussianRegressionSource variance residualVariance
  let coordinateMap := harperGaussianRegressionPairPathCLM lambda
  have hsource :
      Measure.map (harperPairPathZipCLM n) source =
        Measure.pi (fun i ↦
          (gaussianReal 0 (variance i)).prod
            (gaussianReal 0 (residualVariance i))) := by
    simpa only [source, harperGaussianRegressionSource] using
      map_harperPairPathZipCLM_gaussianSource_eq_pi_prod
        variance residualVariance
  have hcommute :
      (fun z ↦ harperPairPathZipCLM n
          (harperGaussianRegressionMap lambda z)) =
        fun z ↦ coordinateMap (harperPairPathZipCLM n z) := by
    funext z
    ext i <;> rfl
  unfold harperRegressedGaussianTwoWalkMeasure
  calc
    Measure.map (harperPairPathZipCLM n)
        (Measure.map (harperGaussianRegressionMap lambda) source) =
      Measure.map
        (fun z ↦ harperPairPathZipCLM n
          (harperGaussianRegressionMap lambda z)) source := by
        rw [Measure.map_map]
        · rfl
        · exact (harperPairPathZipCLM n).measurable
        · exact measurable_harperGaussianRegressionMap lambda
    _ = Measure.map (fun z ↦ coordinateMap (harperPairPathZipCLM n z))
          source := by rw [hcommute]
    _ = Measure.map coordinateMap
          (Measure.map (harperPairPathZipCLM n) source) := by
        rw [Measure.map_map]
        · rfl
        · exact coordinateMap.measurable
        · exact (harperPairPathZipCLM n).measurable
    _ = Measure.map coordinateMap
          (Measure.pi (fun i ↦
            (gaussianReal 0 (variance i)).prod
              (gaussianReal 0 (residualVariance i)))) := by rw [hsource]
    _ = Measure.pi (fun i ↦
          Measure.map (harperGaussianRegressionBlockMap (lambda i))
            ((gaussianReal 0 (variance i)).prod
              (gaussianReal 0 (residualVariance i)))) := by
        simpa only [coordinateMap,
          harperGaussianRegressionPairPathCLM_apply] using
          (Measure.pi_map_pi
            (μ := fun i ↦
              (gaussianReal 0 (variance i)).prod
                (gaussianReal 0 (residualVariance i)))
            (f := fun i ↦ harperGaussianRegressionBlockMap (lambda i))
            (fun i ↦
              (harperGaussianRegressionBlockMap
                (lambda i)).measurable.aemeasurable))
    _ = _ := by rfl

/-- Characteristic function of a generic regression block. -/
theorem harperBivariateCharacteristic_gaussianRegressionBlockLaw
    (variance residualVariance : NNReal) (lambda v w : Real) :
    harperBivariateCharacteristic
        (harperGaussianRegressionBlockLaw
          variance residualVariance lambda) (v, w) =
      Complex.exp
        (-((((v + w * lambda) ^ (2 : Nat) * (variance : Real) +
              w ^ (2 : Nat) * (residualVariance : Real)) / 2 :
                Real) : Complex)) := by
  rw [harperBivariateCharacteristic]
  unfold harperGaussianRegressionBlockLaw
  rw [charFunDual_map, charFunDual_prod]
  have hfirst :
      ((harperTwoHeightProjection v w).comp
          (harperGaussianRegressionBlockMap lambda)).comp
            (ContinuousLinearMap.inl Real Real Real) =
        InnerProductSpace.toDualMap Real Real (v + w * lambda) := by
    ext
    simp [harperTwoHeightProjection_apply, real_inner_eq_re_inner,
      RCLike.inner_apply]
  have hsecond :
      ((harperTwoHeightProjection v w).comp
          (harperGaussianRegressionBlockMap lambda)).comp
            (ContinuousLinearMap.inr Real Real Real) =
        InnerProductSpace.toDualMap Real Real w := by
    ext
    simp [harperTwoHeightProjection_apply, real_inner_eq_re_inner,
      RCLike.inner_apply]
  rw [hfirst, hsecond, ← charFun_eq_charFunDual_toDualMap,
    ← charFun_eq_charFunDual_toDualMap]
  change
    charFun (gaussianReal 0 variance) (v + w * lambda) *
      charFun (gaussianReal 0 residualVariance) w = _
  rw [charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Positivity of the Schur-complement variance follows directly from the
positive-semidefinite covariance already constructed for the exact Gaussian
block. -/
theorem harperTwoHeightRegressionResidualVariance_nonneg
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real)
    (ha : 0 < harperTwoHeightBlockCoordinateCovariance y S t s t t) :
    0 ≤ harperTwoHeightBlockCoordinateCovariance y S t s s s -
      harperTwoHeightBlockCoordinateCovariance y S t s t s ^ (2 : Nat) /
        harperTwoHeightBlockCoordinateCovariance y S t s t t := by
  let a := harperTwoHeightBlockCoordinateCovariance y S t s t t
  let b := harperTwoHeightBlockCoordinateCovariance y S t s s s
  let q := harperTwoHeightBlockCoordinateCovariance y S t s t s
  have hproj := harperTwoHeightProjectedBlockVariance_nonneg
    y S t s q (-a)
  rw [harperTwoHeightProjectedBlockVariance_eq_coordinateCovariance] at hproj
  have hdet : 0 ≤ a * b - q ^ (2 : Nat) := by
    have hmul : 0 ≤ a * (a * b - q ^ (2 : Nat)) := by
      dsimp only [a, b, q] at hproj ⊢
      nlinarith
    nlinarith [hmul, show 0 < a by simpa only [a] using ha]
  have ha0 : harperTwoHeightBlockCoordinateCovariance y S t s t t ≠ 0 :=
    ne_of_gt ha
  have heq :
      harperTwoHeightBlockCoordinateCovariance y S t s s s -
          harperTwoHeightBlockCoordinateCovariance y S t s t s ^ (2 : Nat) /
            harperTwoHeightBlockCoordinateCovariance y S t s t t =
        (harperTwoHeightBlockCoordinateCovariance y S t s t t *
              harperTwoHeightBlockCoordinateCovariance y S t s s s -
            harperTwoHeightBlockCoordinateCovariance y S t s t s ^ (2 : Nat)) /
          harperTwoHeightBlockCoordinateCovariance y S t s t t := by
    field_simp [ha0]
  rw [heq]
  exact div_nonneg hdet ha.le

/-- Exact residual variance of one covariance-matched block. -/
noncomputable def harperTwoHeightRegressionResidualVarianceNNReal
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real)
    (ha : 0 < harperTwoHeightBlockCoordinateCovariance y S t s t t) :
    NNReal :=
  ⟨harperTwoHeightBlockCoordinateCovariance y S t s s s -
      harperTwoHeightBlockCoordinateCovariance y S t s t s ^ (2 : Nat) /
        harperTwoHeightBlockCoordinateCovariance y S t s t t,
    harperTwoHeightRegressionResidualVariance_nonneg y S t s ha⟩

@[simp] theorem coe_harperTwoHeightRegressionResidualVarianceNNReal
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real)
    (ha : 0 < harperTwoHeightBlockCoordinateCovariance y S t s t t) :
    (harperTwoHeightRegressionResidualVarianceNNReal y S t s ha : Real) =
      harperTwoHeightBlockCoordinateCovariance y S t s s s -
        harperTwoHeightBlockCoordinateCovariance y S t s t s ^ (2 : Nat) /
          harperTwoHeightBlockCoordinateCovariance y S t s t t := rfl

/-- Exact regression coefficient of one covariance-matched block. -/
noncomputable def harperTwoHeightRegressionCoefficient
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) : Real :=
  harperTwoHeightBlockCoordinateCovariance y S t s t s /
    harperTwoHeightBlockCoordinateCovariance y S t s t t

/-- Every continuous linear functional on `Real × Real` is one of the
two-coordinate projections used by the bivariate characteristic interface. -/
theorem strongDual_real_prod_eq_harperTwoHeightProjection
    (L : StrongDual Real (Real × Real)) :
    L = harperTwoHeightProjection (L (1, 0)) (L (0, 1)) := by
  apply ContinuousLinearMap.ext
  intro z
  calc
    L z = L (z.1 • ((1 : Real), (0 : Real)) +
        z.2 • ((0 : Real), (1 : Real))) := by
      congr 1
      ext <;> simp
    _ = z.1 * L (1, 0) + z.2 * L (0, 1) := by
      rw [map_add, map_smul, map_smul]
      rfl
    _ = harperTwoHeightProjection (L (1, 0)) (L (0, 1)) z := by
      rw [harperTwoHeightProjection_apply]
      ring

/-- The repository's exact covariance-matched Gaussian block is literally
the Gaussian regression block with its Schur-complement residual variance. -/
theorem harperTwoHeightGaussianLaw_eq_regression
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real)
    (ha : 0 < harperTwoHeightBlockCoordinateCovariance y S t s t t) :
    harperTwoHeightGaussianLaw y S t s =
      harperGaussianRegressionBlockLaw
        (harperTwoHeightCoordinateVarianceNNReal y S t s t)
        (harperTwoHeightRegressionResidualVarianceNNReal y S t s ha)
        (harperTwoHeightRegressionCoefficient y S t s) := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [strongDual_real_prod_eq_harperTwoHeightProjection L]
  let v := L (1, 0)
  let w := L (0, 1)
  change harperBivariateCharacteristic
      (harperTwoHeightGaussianLaw y S t s) (v, w) =
    harperBivariateCharacteristic
      (harperGaussianRegressionBlockLaw
        (harperTwoHeightCoordinateVarianceNNReal y S t s t)
        (harperTwoHeightRegressionResidualVarianceNNReal y S t s ha)
        (harperTwoHeightRegressionCoefficient y S t s)) (v, w)
  rw [harperBivariateCharacteristic_harperTwoHeightGaussianLaw,
    harperBivariateCharacteristic_gaussianRegressionBlockLaw,
    harperTwoHeightProjectedBlockVariance_eq_coordinateCovariance]
  congr 2
  simp only [coe_harperTwoHeightCoordinateVarianceNNReal,
    coe_harperTwoHeightRegressionResidualVarianceNNReal,
    harperTwoHeightRegressionCoefficient]
  have ha0 : harperTwoHeightBlockCoordinateCovariance y S t s t t ≠ 0 :=
    ne_of_gt ha
  push_cast
  field_simp [ha0]
  ring

/-! ## Finite exact Gaussian path -/

/-- The exact covariance-matched Gaussian product path is the zipped
path-level regression law. -/
theorem pi_harperTwoHeightGaussianLaw_eq_map_regressed
    {n y : Nat} (S : Fin n → Finset (Problem520.HarperPrimeIndex y))
    (t s : Real)
    (ha : ∀ i,
      0 < harperTwoHeightBlockCoordinateCovariance y (S i) t s t t) :
    Measure.pi (fun i ↦ harperTwoHeightGaussianLaw y (S i) t s) =
      Measure.map (harperPairPathZipCLM n)
        (harperRegressedGaussianTwoWalkMeasure
          (fun i ↦ harperTwoHeightCoordinateVarianceNNReal y (S i) t s t)
          (fun i ↦ harperTwoHeightRegressionResidualVarianceNNReal
            y (S i) t s (ha i))
          (fun i ↦ harperTwoHeightRegressionCoefficient y (S i) t s)) := by
  calc
    Measure.pi (fun i ↦ harperTwoHeightGaussianLaw y (S i) t s) =
      Measure.pi (fun i ↦
        harperGaussianRegressionBlockLaw
          (harperTwoHeightCoordinateVarianceNNReal y (S i) t s t)
          (harperTwoHeightRegressionResidualVarianceNNReal
            y (S i) t s (ha i))
          (harperTwoHeightRegressionCoefficient y (S i) t s)) := by
        congr 1
        funext i
        exact harperTwoHeightGaussianLaw_eq_regression
          y (S i) t s (ha i)
    _ = _ := (map_harperPairPathZipCLM_regressedGaussian_eq_pi
      (fun i ↦ harperTwoHeightCoordinateVarianceNNReal y (S i) t s t)
      (fun i ↦ harperTwoHeightRegressionResidualVarianceNNReal
        y (S i) t s (ha i))
      (fun i ↦ harperTwoHeightRegressionCoefficient y (S i) t s)).symm

/-- The paired-path version of the coarse linear corridor containing the
pinched logarithmic ballot event. -/
def harperPairedLinearGuardPathEvent (n : Nat) :
    Set (Fin n → Real × Real) :=
  harperPairPathUnzipCLM n ⁻¹'
    (harperLinearGuardPathEvent n ×ˢ harperLinearGuardPathEvent n)

theorem measurableSet_harperPairedLinearGuardPathEvent (n : Nat) :
    MeasurableSet (harperPairedLinearGuardPathEvent n) := by
  exact ((measurableSet_harperLinearGuardPathEvent n).prod
    (measurableSet_harperLinearGuardPathEvent n)).preimage
      (harperPairPathUnzipCLM n).measurable

/-- Once the exact block variances and regression coefficients obey the
natural uniform bounds, the exact covariance-matched Gaussian path pays the
sharp squared-ballot cost. -/
theorem pi_harperTwoHeightGaussianLaw_linearGuard_probability_le
    {n y : Nat} (hn : 0 < n)
    (S : Fin n → Finset (Problem520.HarperPrimeIndex y))
    (t s : Real)
    (ha : ∀ i,
      0 < harperTwoHeightBlockCoordinateCovariance y (S i) t s t t)
    (L : Real) (hL : 0 ≤ L)
    (hlambda : ∀ i : Fin n,
      |harperTwoHeightRegressionCoefficient y (S i) t s| ≤
        L * (1 / 2 : Real) ^ i.val)
    (hvarianceLower : ∀ i,
      (1 / 4 : NNReal) ≤
        harperTwoHeightCoordinateVarianceNNReal y (S i) t s t)
    (hvarianceUpper : ∀ i,
      harperTwoHeightCoordinateVarianceNNReal y (S i) t s t ≤
        (1 / 2 : NNReal))
    (hresidualLower : ∀ i,
      (1 / 4 : NNReal) ≤
        harperTwoHeightRegressionResidualVarianceNNReal
          y (S i) t s (ha i))
    (hresidualUpper : ∀ i,
      harperTwoHeightRegressionResidualVarianceNNReal
          y (S i) t s (ha i) ≤ (1 / 2 : NNReal)) :
    (Measure.pi (fun i ↦ harperTwoHeightGaussianLaw y (S i) t s)).real
        (harperPairedLinearGuardPathEvent n) ≤
      (12288 * (512 * L + 3)) * (n : Real)⁻¹ := by
  rw [pi_harperTwoHeightGaussianLaw_eq_map_regressed S t s ha]
  rw [map_measureReal_apply (harperPairPathZipCLM n).measurable
    (measurableSet_harperPairedLinearGuardPathEvent n)]
  have hpre :
      harperPairPathZipCLM n ⁻¹' harperPairedLinearGuardPathEvent n =
        harperLinearGuardPathEvent n ×ˢ harperLinearGuardPathEvent n := by
    ext z
    simp [harperPairedLinearGuardPathEvent]
  rw [hpre]
  exact harperRegressedGaussianTwoWalk_linearGuard_probability_le
    hn
    (fun i ↦ harperTwoHeightCoordinateVarianceNNReal y (S i) t s t)
    (fun i ↦ harperTwoHeightRegressionResidualVarianceNNReal
      y (S i) t s (ha i))
    (fun i ↦ harperTwoHeightRegressionCoefficient y (S i) t s)
    L hL hlambda hvarianceLower hvarianceUpper
      hresidualLower hresidualUpper

/-! ## Elementary parameter bounds -/

/-- The variance window `[1/3, 3/8]` and covariance bound `1/8` put the
Schur-complement residual variance in `[1/4, 1/2]`. -/
theorem regressionResidualVariance_quarter_half
    {a b q : Real}
    (haLower : (1 / 3 : Real) ≤ a) (haUpper : a ≤ 3 / 8)
    (hbLower : (1 / 3 : Real) ≤ b) (hbUpper : b ≤ 3 / 8)
    (hq : |q| ≤ (1 / 8 : Real)) :
    (1 / 4 : Real) ≤ b - q ^ (2 : Nat) / a ∧
      b - q ^ (2 : Nat) / a ≤ (1 / 2 : Real) := by
  have ha : 0 < a := lt_of_lt_of_le (by norm_num) haLower
  have hq2 : q ^ (2 : Nat) ≤ (1 / 8 : Real) ^ (2 : Nat) := by
    rw [sq_le_sq]
    simpa using hq
  have hdivNonneg : 0 ≤ q ^ (2 : Nat) / a :=
    div_nonneg (sq_nonneg q) ha.le
  have hdivUpper : q ^ (2 : Nat) / a ≤ (3 / 64 : Real) := by
    rw [div_le_iff₀ ha]
    nlinarith
  constructor <;> nlinarith

/-- Dividing a covariance envelope by a variance at least `1/3` costs at
most a factor of three. -/
theorem abs_regressionCoefficient_le_three_mul
    {a q B : Real} (ha : (1 / 3 : Real) ≤ a)
    (hB : 0 ≤ B) (hq : |q| ≤ B) :
    |q / a| ≤ 3 * B := by
  have haPos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  rw [abs_div, abs_of_pos haPos, div_le_iff₀ haPos]
  nlinarith

/-- The scheduled square-mass envelope is bounded by the elementary
geometric block scale. -/
theorem harperScheduledSquareEnvelope_le_threeHalves_geometric (j : Nat) :
    Problem520.harperScheduledSquareEnvelope j ≤
      (3 / 2 : Real) * (1 / 2 : Real) ^ j := by
  have hendpointPos :
      (0 : Real) < Problem520.harperBlockEndpoint j := by
    exact_mod_cast Problem520.harperBlockEndpoint_pos j
  have hlogPos :
      0 < Real.log (Problem520.harperBlockEndpoint j : Real) :=
    Real.log_pos (by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 16)
        (Problem520.harperBlockEndpoint_ge_sixteen j))
  have hlogLe :
      Real.log (Problem520.harperBlockEndpoint j : Real) ≤
        (Problem520.harperBlockEndpoint j : Real) := by
    have h := Real.log_le_sub_one_of_pos hendpointPos
    linarith
  have hinv :
      (Problem520.harperBlockEndpoint j : Real)⁻¹ ≤
        Problem520.invLog (Problem520.harperBlockEndpoint j) := by
    unfold Problem520.invLog
    exact (inv_le_inv₀ hendpointPos hlogPos).2 hlogLe
  unfold Problem520.harperScheduledSquareEnvelope
  calc
    (3 / 2 : Real) *
        (Problem520.harperBlockEndpoint j : Real)⁻¹ ≤
      (3 / 2 : Real) *
        Problem520.invLog (Problem520.harperBlockEndpoint j) := by
          gcongr
    _ ≤ (3 / 2 : Real) * (1 / 2 : Real) ^ j := by
      gcongr
      exact Problem520.invLog_harperBlockEndpoint_le_geometric j

/-- Eventually the strong-PNT theta envelope is itself bounded by a fixed
multiple of the elementary geometric block scale. -/
theorem eventually_harperScheduledThetaEnvelope_le_geometric
    {c C : Real} (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ j : Nat in atTop,
      Problem520.harperScheduledThetaEnvelope c C j ≤
        (C + 1) * (1 / 2 : Real) ^ j := by
  filter_upwards
    [Problem520.eventually_harperScheduledThetaEnvelope_le_invLog_sq hc hC]
      with j hj
  have hinv := Problem520.invLog_harperBlockEndpoint_le_geometric j
  have hinv0 : 0 ≤ Problem520.invLog
      (Problem520.harperBlockEndpoint j) :=
    (Problem520.invLog_harperBlockEndpoint_pos j).le
  have hpow0 : 0 ≤ (1 / 2 : Real) ^ j := by positivity
  have hpow1 : (1 / 2 : Real) ^ j ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  calc
    Problem520.harperScheduledThetaEnvelope c C j ≤
        (C + 1) * Problem520.invLog
          (Problem520.harperBlockEndpoint j) ^ (2 : Nat) := hj
    _ ≤ (C + 1) * ((1 / 2 : Real) ^ j) ^ (2 : Nat) := by
      gcongr
    _ ≤ (C + 1) * (1 / 2 : Real) ^ j := by
      have hC1 : 0 ≤ C + 1 := by linarith
      apply mul_le_mul_of_nonneg_left _ hC1
      nlinarith [sq_nonneg ((1 / 2 : Real) ^ j)]

/-! ## The scheduled shell consequence -/

/-- On every dyadic separation shell, starting a fixed number of blocks
after coherence makes the exact covariance-matched Gaussian path a summably
correlated pair.  Its two-walk linear-guard probability is therefore `O(1/n)`
with an absolute constant and no path-length-dependent covariance cutoff. -/
theorem exists_harperScheduledCorrelatedGaussian_linearGuard_probability_le :
    ∃ L > 0, ∃ J : Nat,
      ∀ r n y : Nat, 0 < n →
        Problem520.harperBlockEndpoint (J + (r + 1) + n) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (r + 1) < |t - s| →
                (Measure.pi (fun i : Fin n ↦
                  harperTwoHeightGaussianLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (J + (r + 1) + i.val)) t s)).real
                    (harperPairedLinearGuardPathEvent n) ≤
                  (12288 * (512 * L + 3)) * (n : Real)⁻¹ := by
  obtain ⟨c, hc, C, hC, Jcov, hcov⟩ :=
    exists_harperTwoHeightScheduledCovariance_postCoherence_geometric
  obtain ⟨Jsmall, hsmall⟩ :=
    exists_eventually_harperTwoHeightScheduledCovariance_postCoherence_small
      (by norm_num : (0 : Real) < 1 / 8)
  obtain ⟨Jvar, hvar⟩ :=
    exists_eventually_harperTwoHeightScheduledCoordinateVariance_third_threeEighths
  obtain ⟨c', hc', C', hC', Jerr, herr⟩ :=
    Problem520.exists_harperScheduledSummableBlockErrorBounds 1
  obtain ⟨Jtheta, htheta⟩ := Filter.eventually_atTop.1
    (eventually_harperScheduledThetaEnvelope_le_geometric hc hC.le)
  let J := max Jsmall (max Jcov (max Jvar (max Jerr Jtheta)))
  let K : Real := 395 + 7 * C
  let L : Real := 3 * K
  have hK : 0 < K := by
    dsimp only [K]
    nlinarith
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  refine ⟨L, hL, J, ?_⟩
  intro r n y hn hy t ht s hs hsep
  let S : Fin n → Finset (Problem520.HarperPrimeIndex y) :=
    fun i ↦ Problem520.harperScheduledPrimeBlock y
      (J + (r + 1) + i.val)
  have hblock (i : Fin n) :
      let j := J + (r + 1) + i.val
      let a := harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) t s t t
      let b := harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) t s s s
      let q := harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) t s t s
      (1 / 3 : Real) < a ∧ a < 3 / 8 ∧
        (1 / 3 : Real) < b ∧ b < 3 / 8 ∧
          |q| ≤ K * (1 / 2 : Real) ^ i.val ∧
            |q| ≤ (1 / 8 : Real) := by
    dsimp only
    let j := J + (r + 1) + i.val
    have hjEnd : j + 1 ≤ J + (r + 1) + n := by
      dsimp only [j]
      omega
    have hyj : Problem520.harperBlockEndpoint (j + 1) ≤ y :=
      (Problem520.monotone_harperBlockEndpoint hjEnd).trans hy
    have hJcov : Jcov + (r + 1) ≤ j := by
      dsimp only [j, J]
      have : Jcov ≤ max Jsmall (max Jcov (max Jvar (max Jerr Jtheta))) :=
        (le_max_left Jcov _).trans (le_max_right Jsmall _)
      omega
    have hJsmall : Jsmall + (r + 1) ≤ j := by
      dsimp only [j, J]
      have : Jsmall ≤ max Jsmall (max Jcov (max Jvar (max Jerr Jtheta))) :=
        le_max_left _ _
      omega
    have hJvar : Jvar ≤ j := by
      dsimp only [j, J]
      have : Jvar ≤ max Jsmall (max Jcov (max Jvar (max Jerr Jtheta))) :=
        ((le_max_left Jvar _).trans (le_max_right Jcov _)).trans
          (le_max_right Jsmall _)
      omega
    have hJerr : Jerr ≤ j := by
      dsimp only [j, J]
      have : Jerr ≤ max Jsmall (max Jcov (max Jvar (max Jerr Jtheta))) :=
        (((le_max_left Jerr Jtheta).trans (le_max_right Jvar _)).trans
          (le_max_right Jcov _)).trans (le_max_right Jsmall _)
      omega
    have hJtheta : Jtheta ≤ j := by
      dsimp only [j, J]
      have : Jtheta ≤ max Jsmall (max Jcov (max Jvar (max Jerr Jtheta))) :=
        (((le_max_right Jerr Jtheta).trans (le_max_right Jvar _)).trans
          (le_max_right Jcov _)).trans (le_max_right Jsmall _)
      omega
    have hvarj := hvar j hJvar y hyj t ht s hs
    have htt := hvarj t ht
    have hss := hvarj s hs
    have hcovj := hcov r j y hJcov hyj t ht s hs hsep
    have hsmallj := (hsmall r j y hJsmall hyj t ht s hs hsep).le
    have hthetaJ := htheta j hJtheta
    have hsquareMass : Problem520.harperScheduledSquareMass y j ≤
        Problem520.harperScheduledSquareEnvelope j :=
      (herr j hJerr y hyj).2.2
    have hpDiff :
        (1 / 2 : Real) ^ (j - (r + 1)) ≤
          (1 / 2 : Real) ^ i.val := by
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      dsimp only [j]
      omega
    have hpSum :
        (1 / 2 : Real) ^ (j - 1) ≤
          (1 / 2 : Real) ^ i.val := by
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      dsimp only [j]
      omega
    have hpJ :
        (1 / 2 : Real) ^ j ≤ (1 / 2 : Real) ^ i.val := by
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      dsimp only [j]
      omega
    have hthetaI : Problem520.harperScheduledThetaEnvelope c C j ≤
        (C + 1) * (1 / 2 : Real) ^ i.val := by
      exact hthetaJ.trans (mul_le_mul_of_nonneg_left hpJ (by linarith))
    have hsquareI : Problem520.harperScheduledSquareMass y j ≤
        (3 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
      calc
        Problem520.harperScheduledSquareMass y j ≤
            Problem520.harperScheduledSquareEnvelope j := hsquareMass
        _ ≤ (3 / 2 : Real) * (1 / 2 : Real) ^ j :=
          harperScheduledSquareEnvelope_le_threeHalves_geometric j
        _ ≤ (3 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
          gcongr
    have hq :
        |harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
          K * (1 / 2 : Real) ^ i.val := by
      have hp0 : 0 ≤ (1 / 2 : Real) ^ i.val := by positivity
      calc
        |harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
          2 * (1 / 2 : Real) ^ (j - (r + 1)) +
            2 * (1 / 2 : Real) ^ (j - 1) +
            7 * Problem520.harperScheduledThetaEnvelope c C j +
            256 * Problem520.harperScheduledSquareMass y j := hcovj
        _ ≤ 2 * (1 / 2 : Real) ^ i.val +
            2 * (1 / 2 : Real) ^ i.val +
            7 * ((C + 1) * (1 / 2 : Real) ^ i.val) +
            256 * ((3 / 2 : Real) * (1 / 2 : Real) ^ i.val) := by
          gcongr
        _ = K * (1 / 2 : Real) ^ i.val := by
          dsimp only [K]
          ring
    exact ⟨htt.1, htt.2, hss.1, hss.2, hq, hsmallj⟩
  have ha : ∀ i,
      0 < harperTwoHeightBlockCoordinateCovariance y (S i) t s t t := by
    intro i
    exact lt_trans (by norm_num) (hblock i).1
  apply pi_harperTwoHeightGaussianLaw_linearGuard_probability_le
    hn S t s ha L hL.le
  · intro i
    have hb := hblock i
    unfold harperTwoHeightRegressionCoefficient
    have hraw := abs_regressionCoefficient_le_three_mul
      hb.1.le (mul_nonneg hK.le (by positivity)) hb.2.2.2.2.1
    dsimp only [S] at hraw ⊢
    calc
      |harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y
              (J + (r + 1) + i.val)) t s t s /
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y
              (J + (r + 1) + i.val)) t s t t| ≤
        3 * (K * (1 / 2 : Real) ^ i.val) := hraw
      _ = L * (1 / 2 : Real) ^ i.val := by
        dsimp only [L]
        ring
  · intro i
    exact_mod_cast (show (1 / 4 : Real) ≤
      harperTwoHeightBlockCoordinateCovariance y (S i) t s t t by
        linarith [(hblock i).1])
  · intro i
    exact_mod_cast (show
      harperTwoHeightBlockCoordinateCovariance y (S i) t s t t ≤
        (1 / 2 : Real) by linarith [(hblock i).2.1])
  · intro i
    have hb := hblock i
    have hres := regressionResidualVariance_quarter_half
      hb.1.le hb.2.1.le hb.2.2.1.le hb.2.2.2.1.le
      hb.2.2.2.2.2
    exact_mod_cast hres.1
  · intro i
    have hb := hblock i
    have hqSmall :
        |harperTwoHeightBlockCoordinateCovariance y (S i) t s t s| ≤
          (1 / 8 : Real) := by
      exact hb.2.2.2.2.2
    have hres := regressionResidualVariance_quarter_half
      hb.1.le hb.2.1.le hb.2.2.1.le hb.2.2.2.1.le hqSmall
    exact_mod_cast hres.2

/-! ## A moderate-cell lower bound for the correlated Gaussian -/

/-- A covariance-matched regression block assigns an explicit positive mass
to every short rectangle.  The proof uses a fixed inner source rectangle;
the bound is deliberately elementary because its role is only to absorb the
much smaller Fourier replacement error. -/
theorem harperGaussianRegressionBlockLaw_rectangleMass_lower
    (variance residualVariance : NNReal) (lambda a b delta : Real)
    (hvarianceLower : (1 / 4 : Real) ≤ variance)
    (hvarianceUpper : (variance : Real) ≤ 1 / 2)
    (hresidualLower : (1 / 4 : Real) ≤ residualVariance)
    (hresidualUpper : (residualVariance : Real) ≤ 1 / 2)
    (hlambda : |lambda| ≤ (3 / 8 : Real))
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (delta ^ (2 : Nat) / 64) *
        Real.exp (-2 *
          ((|a| + 1) ^ (2 : Nat) +
            (|b - lambda * a + delta / 4| + 1) ^ (2 : Nat))) ≤
      (harperGaussianRegressionBlockLaw
        variance residualVariance lambda).real
          (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) := by
  let source : Measure (Real × Real) :=
    (gaussianReal 0 variance).prod (gaussianReal 0 residualVariance)
  let A : Set Real := Ioc a (a + delta / 4)
  let c : Real := b - lambda * a + delta / 4
  let B : Set Real := Ioc c (c + delta / 4)
  let R : Set (Real × Real) := Ioc a (a + delta) ×ˢ Ioc b (b + delta)
  have hRmeas : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  have hmap :
      (harperGaussianRegressionBlockLaw
          variance residualVariance lambda).real R =
        source.real (harperGaussianRegressionBlockMap lambda ⁻¹' R) := by
    unfold harperGaussianRegressionBlockLaw
    exact map_measureReal_apply
      (harperGaussianRegressionBlockMap lambda).measurable hRmeas
  have hsubset : A ×ˢ B ⊆
      harperGaussianRegressionBlockMap lambda ⁻¹' R := by
    intro z hz
    have hx := hz.1
    have hw := hz.2
    have hdeltaNonneg : 0 ≤ delta := hdelta0.le
    have hu0 : 0 < z.1 - a := by linarith [hx.1]
    have hu1 : z.1 - a ≤ delta / 4 := by linarith [hx.2]
    have hlambdaU : |lambda * (z.1 - a)| ≤ 3 * delta / 32 := by
      rw [abs_mul]
      have huAbs : |z.1 - a| = z.1 - a := abs_of_pos hu0
      rw [huAbs]
      calc
        |lambda| * (z.1 - a) ≤ (3 / 8 : Real) * (delta / 4) := by
          exact mul_le_mul hlambda hu1 hu0.le (by norm_num)
        _ = 3 * delta / 32 := by ring
    have hlambdaBounds := abs_le.mp hlambdaU
    have hv0 : delta / 4 < z.2 - (b - lambda * a) := by
      dsimp only [B, c] at hw
      linarith [hw.1]
    have hv1 : z.2 - (b - lambda * a) ≤ delta / 2 := by
      dsimp only [B, c] at hw
      linarith [hw.2]
    change harperGaussianRegressionBlockMap lambda z ∈ R
    rw [harperGaussianRegressionBlockMap_apply]
    constructor
    · dsimp only [R]
      constructor <;> linarith [hx.1, hx.2]
    · dsimp only [R]
      constructor <;> nlinarith
  have hmono : source.real (A ×ˢ B) ≤
      source.real (harperGaussianRegressionBlockMap lambda ⁻¹' R) :=
    measureReal_mono hsubset
  have hA :
      ((delta / 4) / 2) * Real.exp (-2 * (|a| + 1) ^ (2 : Nat)) ≤
        (gaussianReal 0 variance).real A := by
    dsimp only [A]
    exact Problem520.gaussianReal_real_Ioc_ge_of_variance_quarter_half
      hvarianceLower hvarianceUpper (by positivity) (by linarith)
  have hB :
      ((delta / 4) / 2) * Real.exp (-2 * (|c| + 1) ^ (2 : Nat)) ≤
        (gaussianReal 0 residualVariance).real B := by
    dsimp only [B]
    exact Problem520.gaussianReal_real_Ioc_ge_of_variance_quarter_half
      hresidualLower hresidualUpper (by positivity) (by linarith)
  have hprod : source.real (A ×ˢ B) =
      (gaussianReal 0 variance).real A *
        (gaussianReal 0 residualVariance).real B := by
    simp only [source, Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  rw [hmap]
  calc
    (delta ^ (2 : Nat) / 64) *
        Real.exp (-2 *
          ((|a| + 1) ^ (2 : Nat) +
            (|b - lambda * a + delta / 4| + 1) ^ (2 : Nat))) =
      (((delta / 4) / 2) *
          Real.exp (-2 * (|a| + 1) ^ (2 : Nat))) *
        (((delta / 4) / 2) *
          Real.exp (-2 * (|c| + 1) ^ (2 : Nat))) := by
      dsimp only [c]
      rw [show
        -2 * ((|a| + 1) ^ (2 : Nat) +
            (|b - lambda * a + delta / 4| + 1) ^ (2 : Nat)) =
          -2 * (|a| + 1) ^ (2 : Nat) +
            -2 * (|b - lambda * a + delta / 4| + 1) ^ (2 : Nat) by ring,
        Real.exp_add]
      ring
    _ ≤ (gaussianReal 0 variance).real A *
        (gaussianReal 0 residualVariance).real B := by
      exact mul_le_mul hA hB (by positivity) measureReal_nonneg
    _ = source.real (A ×ˢ B) := hprod.symm
    _ ≤ source.real (harperGaussianRegressionBlockMap lambda ⁻¹' R) := hmono

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.harperTwoHeightRegressionResidualVariance_nonneg
#print axioms Erdos.Problem1144.strongDual_real_prod_eq_harperTwoHeightProjection
#print axioms Erdos.Problem1144.harperTwoHeightGaussianLaw_eq_regression
#print axioms Erdos.Problem1144.map_harperPairPathZipCLM_regressedGaussian_eq_pi
#print axioms Erdos.Problem1144.pi_harperTwoHeightGaussianLaw_linearGuard_probability_le
#print axioms Erdos.Problem1144.exists_harperScheduledCorrelatedGaussian_linearGuard_probability_le
#print axioms Erdos.Problem1144.harperGaussianRegressionBlockLaw_rectangleMass_lower
