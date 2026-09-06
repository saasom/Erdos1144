import Erdos.Problem1144.HarperGaussianTwoWalkBallot
import Erdos.Problem520.HarperBlockGaussian

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Bivariate characteristic estimates for the two-height tilt

The actual two-height law still has independent prime coordinates.  For a
fixed prime, any linear projection of the two path increments is just a
centered two-point random variable.  This module proves its second-order
characteristic expansion and accumulates it over an arbitrary prime block.

This is the Cramer--Wold core of the missing bivariate local-limit theorem.
The remaining inversion step is genuinely two-dimensional, but all
prime-level Taylor and finite-product error bookkeeping is closed here.
-/

/-- The fluctuation at observation height `u`, centered for the two-height
tilted coin rather than either one-height tilt. -/
noncomputable def harperTwoHeightPrimeFluctuation
    (p : Nat) (t s u : Real) (b : Bool) : Real :=
  (Problem520.cubeSign b - harperTwoHeightTiltBias p t s) *
    (Real.cos (u * Real.log (p : Real)) / Real.sqrt (p : Real))

theorem neg_one_le_harperTwoHeightTiltBias
    {p : Nat} (hp : p.Prime) (t s : Real) :
    (-1 : Real) ≤ harperTwoHeightTiltBias p t s := by
  have hsum := harperTwoHeightCoinWeight_false_add_true hp t s
  have hfalse := harperTwoHeightCoinWeight_nonneg p t s false
  have htrue := harperTwoHeightCoinWeight_nonneg p t s true
  unfold harperTwoHeightTiltBias
  linarith

theorem harperTwoHeightTiltBias_le_one
    {p : Nat} (hp : p.Prime) (t s : Real) :
    harperTwoHeightTiltBias p t s ≤ (1 : Real) := by
  have hsum := harperTwoHeightCoinWeight_false_add_true hp t s
  have hfalse := harperTwoHeightCoinWeight_nonneg p t s false
  have htrue := harperTwoHeightCoinWeight_nonneg p t s true
  unfold harperTwoHeightTiltBias
  linarith

theorem abs_cubeSign_sub_harperTwoHeightTiltBias_le_two
    {p : Nat} (hp : p.Prime) (t s : Real) (b : Bool) :
    |Problem520.cubeSign b - harperTwoHeightTiltBias p t s| ≤ 2 := by
  have hlower := neg_one_le_harperTwoHeightTiltBias hp t s
  have hupper := harperTwoHeightTiltBias_le_one hp t s
  cases b <;> simp only [Problem520.cubeSign, Bool.false_eq_true,
    if_false, if_true] <;> rw [abs_le] <;> constructor <;> linarith

/-- A two-height-centered prime fluctuation has the same `2/sqrt p`
pointwise envelope as an ordinary centered tilted increment. -/
theorem abs_harperTwoHeightPrimeFluctuation_le
    {p : Nat} (hp : p.Prime) (t s u : Real) (b : Bool) :
    |harperTwoHeightPrimeFluctuation p t s u b| ≤
      2 * (Real.sqrt (p : Real))⁻¹ := by
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  have hsqrt : 0 < Real.sqrt (p : Real) := Real.sqrt_pos.2 hpR
  unfold harperTwoHeightPrimeFluctuation
  rw [abs_mul, abs_div]
  calc
    |Problem520.cubeSign b - harperTwoHeightTiltBias p t s| *
          (|Real.cos (u * Real.log (p : Real))| /
            |Real.sqrt (p : Real)|) ≤
        2 * (1 / Real.sqrt (p : Real)) := by
      gcongr
      · exact abs_cubeSign_sub_harperTwoHeightTiltBias_le_two hp t s b
      · exact Real.abs_cos_le_one _
      · rw [abs_of_pos hsqrt]
    _ = 2 * (Real.sqrt (p : Real))⁻¹ := by
      rw [inv_eq_one_div]

/-- The fluctuation is exactly centered under the two-height coin. -/
theorem integral_harperTwoHeightPrimeFluctuation
    (p : Nat) (hp : p.Prime) (t s u : Real) :
    (∫ b, harperTwoHeightPrimeFluctuation p t s u b
        ∂harperTwoHeightCoin p hp t s) = 0 := by
  let c : Real :=
    Real.cos (u * Real.log (p : Real)) / Real.sqrt (p : Real)
  unfold harperTwoHeightPrimeFluctuation
  change (∫ b, (Problem520.cubeSign b -
      harperTwoHeightTiltBias p t s) * c
      ∂harperTwoHeightCoin p hp t s) = 0
  rw [integral_mul_const, integral_sub Integrable.of_finite
    Integrable.of_finite, integral_cubeSign_harperTwoHeightCoin,
    integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self,
    zero_mul]

/-- Linear projection `v X_t + w X_s` of the centered two-height increment
pair. -/
noncomputable def harperTwoHeightProjectedPrimeIncrement
    (p : Nat) (t s v w : Real) (b : Bool) : Real :=
  v * harperTwoHeightPrimeFluctuation p t s t b +
    w * harperTwoHeightPrimeFluctuation p t s s b

theorem integral_harperTwoHeightProjectedPrimeIncrement
    (p : Nat) (hp : p.Prime) (t s v w : Real) :
    (∫ b, harperTwoHeightProjectedPrimeIncrement p t s v w b
        ∂harperTwoHeightCoin p hp t s) = 0 := by
  unfold harperTwoHeightProjectedPrimeIncrement
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_const_mul,
    integral_harperTwoHeightPrimeFluctuation,
    integral_harperTwoHeightPrimeFluctuation, mul_zero, mul_zero, add_zero]

theorem abs_harperTwoHeightProjectedPrimeIncrement_le
    {p : Nat} (hp : p.Prime) (t s v w : Real) (b : Bool) :
    |harperTwoHeightProjectedPrimeIncrement p t s v w b| ≤
      2 * (|v| + |w|) * (Real.sqrt (p : Real))⁻¹ := by
  unfold harperTwoHeightProjectedPrimeIncrement
  calc
    |v * harperTwoHeightPrimeFluctuation p t s t b +
        w * harperTwoHeightPrimeFluctuation p t s s b| ≤
      |v * harperTwoHeightPrimeFluctuation p t s t b| +
        |w * harperTwoHeightPrimeFluctuation p t s s b| := abs_add_le _ _
    _ = |v| * |harperTwoHeightPrimeFluctuation p t s t b| +
        |w| * |harperTwoHeightPrimeFluctuation p t s s b| := by
      rw [abs_mul, abs_mul]
    _ ≤ |v| * (2 * (Real.sqrt (p : Real))⁻¹) +
        |w| * (2 * (Real.sqrt (p : Real))⁻¹) := by
      gcongr
      · exact abs_harperTwoHeightPrimeFluctuation_le hp t s t b
      · exact abs_harperTwoHeightPrimeFluctuation_le hp t s s b
    _ = 2 * (|v| + |w|) * (Real.sqrt (p : Real))⁻¹ := by ring

/-- Exact variance of one projected two-height prime increment. -/
noncomputable def harperTwoHeightProjectedPrimeVariance
    (p : Nat) (hp : p.Prime) (t s v w : Real) : Real :=
  ∫ b, harperTwoHeightProjectedPrimeIncrement p t s v w b ^ (2 : Nat)
    ∂harperTwoHeightCoin p hp t s

theorem harperTwoHeightProjectedPrimeVariance_nonneg
    (p : Nat) (hp : p.Prime) (t s v w : Real) :
    0 ≤ harperTwoHeightProjectedPrimeVariance p hp t s v w := by
  unfold harperTwoHeightProjectedPrimeVariance
  exact integral_nonneg fun b ↦ sq_nonneg _

theorem harperTwoHeightProjectedPrimeVariance_le_envelope
    {p : Nat} (hp : p.Prime) (t s v w : Real) :
    harperTwoHeightProjectedPrimeVariance p hp t s v w ≤
      (2 * (|v| + |w|) * (Real.sqrt (p : Real))⁻¹) ^ (2 : Nat) := by
  let B : Real := 2 * (|v| + |w|) * (Real.sqrt (p : Real))⁻¹
  unfold harperTwoHeightProjectedPrimeVariance
  calc
    (∫ b, harperTwoHeightProjectedPrimeIncrement p t s v w b ^ (2 : Nat)
        ∂harperTwoHeightCoin p hp t s) ≤
      ∫ _b : Bool, B ^ (2 : Nat)
        ∂harperTwoHeightCoin p hp t s := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro b
      have habs := abs_harperTwoHeightProjectedPrimeIncrement_le
        hp t s v w b
      have hsq := pow_le_pow_left₀ (abs_nonneg _) (by
        simpa only [B] using habs) 2
      simpa only [sq_abs] using hsq
    _ = B ^ (2 : Nat) := by
      rw [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- Purely imaginary characteristic exponent of the projected pair. -/
noncomputable def harperTwoHeightProjectedCharacteristicExponent
    (p : Nat) (t s v w : Real) (b : Bool) : Complex :=
  ((harperTwoHeightProjectedPrimeIncrement p t s v w b : Real) : Complex) *
    Complex.I

theorem norm_harperTwoHeightProjectedCharacteristicExponent
    (p : Nat) (t s v w : Real) (b : Bool) :
    ‖harperTwoHeightProjectedCharacteristicExponent p t s v w b‖ =
      |harperTwoHeightProjectedPrimeIncrement p t s v w b| := by
  rw [harperTwoHeightProjectedCharacteristicExponent, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]

noncomputable def harperTwoHeightProjectedPrimeCharacteristic
    (p : Nat) (hp : p.Prime) (t s v w : Real) : Complex :=
  ∫ b, Complex.exp
      (harperTwoHeightProjectedCharacteristicExponent p t s v w b)
    ∂harperTwoHeightCoin p hp t s

theorem norm_harperTwoHeightProjectedPrimeCharacteristic_le_one
    (p : Nat) (hp : p.Prime) (t s v w : Real) :
    ‖harperTwoHeightProjectedPrimeCharacteristic p hp t s v w‖ ≤ 1 := by
  unfold harperTwoHeightProjectedPrimeCharacteristic
  calc
    ‖∫ b, Complex.exp
          (harperTwoHeightProjectedCharacteristicExponent p t s v w b)
        ∂harperTwoHeightCoin p hp t s‖ ≤
        ∫ b, ‖Complex.exp
          (harperTwoHeightProjectedCharacteristicExponent p t s v w b)‖
          ∂harperTwoHeightCoin p hp t s := norm_integral_le_integral_norm _
    _ = ∫ _b : Bool, (1 : Real) ∂harperTwoHeightCoin p hp t s := by
      apply integral_congr_ae
      exact ae_of_all _ fun b ↦ by
        exact Complex.norm_exp_ofReal_mul_I _
    _ = 1 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- One-prime projected characteristic expansion.  Its error is cubic in
the two-dimensional Fourier radius `|v|+|w|`. -/
theorem norm_harperTwoHeightProjectedPrimeCharacteristic_sub_quadratic_le
    {p : Nat} (hp : p.Prime) (t s v w : Real)
    (hsmall :
      2 * (|v| + |w|) * (Real.sqrt (p : Real))⁻¹ ≤ 1) :
    ‖harperTwoHeightProjectedPrimeCharacteristic p hp t s v w -
        (1 - ((harperTwoHeightProjectedPrimeVariance p hp t s v w / 2 :
          Real) : Complex))‖ ≤
      (2 * (|v| + |w|) * (Real.sqrt (p : Real))⁻¹) ^ (3 : Nat) := by
  let X : Bool → Real :=
    harperTwoHeightProjectedPrimeIncrement p t s v w
  let Z : Bool → Complex := fun b ↦ ((X b : Real) : Complex) * Complex.I
  let Q : Bool → Complex := fun b ↦ 1 + Z b + Z b ^ (2 : Nat) / 2
  let B : Real := 2 * (|v| + |w|) * (Real.sqrt (p : Real))⁻¹
  have hZ (b : Bool) : ‖Z b‖ ≤ 1 := by
    have hX := abs_harperTwoHeightProjectedPrimeIncrement_le
      hp t s v w b
    have hnorm : ‖Z b‖ = |X b| := by
      dsimp only [Z]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one]
    rw [hnorm]
    exact hX.trans hsmall
  have hTaylor (b : Bool) :
      ‖Complex.exp (Z b) - Q b‖ ≤ B ^ (3 : Nat) := by
    have hExp := Complex.exp_bound (hZ b) (n := 3) (by decide)
    have hpoly :
        (∑ m ∈ Finset.range 3, Z b ^ m / (m.factorial : Complex)) =
          Q b := by
      dsimp only [Q]
      norm_num [Finset.sum_range_succ, Nat.factorial]
    rw [hpoly] at hExp
    have hnorm : ‖Z b‖ = |X b| := by
      dsimp only [Z]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one]
    calc
      ‖Complex.exp (Z b) - Q b‖ ≤
          ‖Z b‖ ^ 3 *
            ((Nat.succ 3 : Real) *
              ((Nat.factorial 3) * (3 : Nat) : Real)⁻¹) := hExp
      _ ≤ ‖Z b‖ ^ 3 := by
        have hzpow : 0 ≤ ‖Z b‖ ^ 3 := by positivity
        norm_num [Nat.factorial]
        linarith
      _ = |X b| ^ 3 := by rw [hnorm]
      _ ≤ B ^ 3 := by
        exact pow_le_pow_left₀ (abs_nonneg _) (by
          simpa only [X, B] using
            abs_harperTwoHeightProjectedPrimeIncrement_le hp t s v w b) 3
  have hmeanZ : (∫ b, Z b ∂harperTwoHeightCoin p hp t s) = 0 := by
    dsimp only [Z]
    calc
      (∫ b, (((X b : Real) : Complex) * Complex.I)
          ∂harperTwoHeightCoin p hp t s) =
          (∫ b, ((X b : Real) : Complex)
            ∂harperTwoHeightCoin p hp t s) * Complex.I :=
        integral_mul_const Complex.I _
      _ = (((∫ b, X b ∂harperTwoHeightCoin p hp t s) : Real) :
          Complex) * Complex.I := by
        have hcast :
            (∫ b, ((X b : Real) : Complex)
                ∂harperTwoHeightCoin p hp t s) =
              (((∫ b, X b ∂harperTwoHeightCoin p hp t s) : Real) :
                Complex) := integral_ofReal
        rw [hcast]
      _ = 0 := by
        rw [show (∫ b, X b ∂harperTwoHeightCoin p hp t s) = 0 by
          simpa only [X] using
            integral_harperTwoHeightProjectedPrimeIncrement
              p hp t s v w]
        simp
  have hsecondZ :
      (∫ b, Z b ^ (2 : Nat) ∂harperTwoHeightCoin p hp t s) =
        -((harperTwoHeightProjectedPrimeVariance p hp t s v w : Real) :
          Complex) := by
    have hpoint (b : Bool) : Z b ^ (2 : Nat) =
        -(((X b) ^ (2 : Nat) : Real) : Complex) := by
      dsimp only [Z]
      rw [mul_pow, Complex.I_sq]
      push_cast
      ring
    simp_rw [hpoint]
    rw [integral_neg]
    have hcast :
        (∫ b, (((X b) ^ (2 : Nat) : Real) : Complex)
            ∂harperTwoHeightCoin p hp t s) =
          (((∫ b, X b ^ (2 : Nat)
              ∂harperTwoHeightCoin p hp t s) : Real) : Complex) :=
      integral_ofReal
    rw [hcast]
    rfl
  have hquad :
      (∫ b, Q b ∂harperTwoHeightCoin p hp t s) =
        1 - ((harperTwoHeightProjectedPrimeVariance p hp t s v w / 2 :
          Real) : Complex) := by
    have hone : (∫ _b : Bool, (1 : Complex)
        ∂harperTwoHeightCoin p hp t s) = 1 := by
      rw [integral_const, probReal_univ]
      exact one_smul Real (1 : Complex)
    have hdiv :
        (∫ b, Z b ^ (2 : Nat) / 2
            ∂harperTwoHeightCoin p hp t s) =
          -((harperTwoHeightProjectedPrimeVariance p hp t s v w : Real) :
            Complex) / 2 := by
      calc
        (∫ b, Z b ^ (2 : Nat) / 2
            ∂harperTwoHeightCoin p hp t s) =
            (∫ b, Z b ^ (2 : Nat)
              ∂harperTwoHeightCoin p hp t s) / 2 :=
          integral_div 2 _
        _ = -((harperTwoHeightProjectedPrimeVariance p hp t s v w : Real) :
              Complex) / 2 := by rw [hsecondZ]
    dsimp only [Q]
    rw [integral_add Integrable.of_finite Integrable.of_finite,
      integral_add Integrable.of_finite Integrable.of_finite,
      hone, hmeanZ, hdiv]
    push_cast
    ring
  let R : Bool → Complex := fun b ↦ Complex.exp (Z b) - Q b
  have hidentity :
      harperTwoHeightProjectedPrimeCharacteristic p hp t s v w -
          (1 - ((harperTwoHeightProjectedPrimeVariance p hp t s v w / 2 :
            Real) : Complex)) =
        ∫ b, R b ∂harperTwoHeightCoin p hp t s := by
    rw [← hquad]
    unfold harperTwoHeightProjectedPrimeCharacteristic
    change (∫ b, Complex.exp (Z b) ∂harperTwoHeightCoin p hp t s) -
        ∫ b, Q b ∂harperTwoHeightCoin p hp t s = _
    exact (integral_sub Integrable.of_finite Integrable.of_finite).symm
  rw [hidentity]
  calc
    ‖∫ b, R b ∂harperTwoHeightCoin p hp t s‖ ≤
        ∫ b, ‖R b‖ ∂harperTwoHeightCoin p hp t s :=
      norm_integral_le_integral_norm R
    _ ≤ ∫ _b : Bool, B ^ (3 : Nat)
        ∂harperTwoHeightCoin p hp t s := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro b
      simpa only [R] using hTaylor b
    _ = B ^ (3 : Nat) := by
      rw [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-! ## Accumulation over a finite prime block -/

/-- Projected centered sum over an arbitrary finite prime block. -/
noncomputable def harperTwoHeightProjectedPrimeBlockSum
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) (eta : Problem520.HarperPrimeCube y) : Real :=
  ∑ p ∈ S, harperTwoHeightProjectedPrimeIncrement p.1 t s v w (eta p)

/-- Characteristic function of the projected block under the actual
two-height tilted cube law. -/
noncomputable def harperTwoHeightProjectedCubeCharacteristic
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) : Complex :=
  ∫ eta, Complex.exp
      (((harperTwoHeightProjectedPrimeBlockSum y S t s v w eta : Real) :
        Complex) * Complex.I)
    ∂harperTwoHeightCubeLaw y t s

/-- Complex-valued marginal integration for one coordinate of the
two-height cube. -/
theorem integral_harperTwoHeightCube_eval_complex
    (y : Nat) (t s : Real) (p : Problem520.HarperPrimeIndex y)
    (g : Bool → Complex) :
    (∫ eta, g (eta p) ∂harperTwoHeightCubeLaw y t s) =
      ∫ b, g b ∂harperTwoHeightCoin p.1
        (Nat.prime_of_mem_primesBelow p.property) t s := by
  have hmp := measurePreserving_harperTwoHeightCube_eval y t s p
  calc
    (∫ eta, g (eta p) ∂harperTwoHeightCubeLaw y t s) =
        ∫ b, g b ∂Measure.map
          (fun eta : Problem520.HarperPrimeCube y ↦ eta p)
          (harperTwoHeightCubeLaw y t s) := by
      symm
      exact integral_map hmp.measurable.aemeasurable
        (measurable_of_finite g).aestronglyMeasurable
    _ = ∫ b, g b ∂harperTwoHeightCoin p.1
          (Nat.prime_of_mem_primesBelow p.property) t s := by
      rw [hmp.map_eq]

noncomputable def harperTwoHeightProjectedBlockCharacteristic
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) : Complex :=
  ∏ p ∈ S, harperTwoHeightProjectedPrimeCharacteristic p.1
    (Nat.prime_of_mem_primesBelow p.property) t s v w

/-- Independence of prime coordinates factors the actual projected block
characteristic function into its one-prime factors. -/
theorem harperTwoHeightProjectedCubeCharacteristic_eq_block
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) :
    harperTwoHeightProjectedCubeCharacteristic y S t s v w =
      harperTwoHeightProjectedBlockCharacteristic y S t s v w := by
  let coord : S → Problem520.HarperPrimeCube y → Bool :=
    fun p eta ↦ eta p.1
  let g : (p : S) → Bool → Complex := fun p b ↦
    Complex.exp
      (((harperTwoHeightProjectedPrimeIncrement p.1.1 t s v w b : Real) :
        Complex) * Complex.I)
  have hcoord : iIndepFun coord (harperTwoHeightCubeLaw y t s) := by
    exact iIndepFun.precomp Subtype.val_injective
      (iIndepFun_harperTwoHeightCube_coordinates y t s)
  have hfunctions : iIndepFun
      (fun p : S ↦ g p ∘ coord p) (harperTwoHeightCubeLaw y t s) :=
    hcoord.comp g (fun _ ↦ measurable_of_finite _)
  have hprod := hfunctions.integral_fun_prod_eq_prod_integral
    (fun p ↦ (measurable_of_finite (g p ∘ coord p)).aestronglyMeasurable)
  calc
    harperTwoHeightProjectedCubeCharacteristic y S t s v w =
        ∫ eta, ∏ p ∈ S, Complex.exp
          (((harperTwoHeightProjectedPrimeIncrement p.1 t s v w (eta p) :
            Real) : Complex) * Complex.I)
          ∂harperTwoHeightCubeLaw y t s := by
      unfold harperTwoHeightProjectedCubeCharacteristic
        harperTwoHeightProjectedPrimeBlockSum
      apply integral_congr_ae
      exact ae_of_all _ fun eta ↦ by
        change
          Complex.exp
              (((∑ p ∈ S,
                harperTwoHeightProjectedPrimeIncrement p.1 t s v w
                  (eta p) : Real) : Complex) * Complex.I) =
            ∏ p ∈ S, Complex.exp
              (((harperTwoHeightProjectedPrimeIncrement p.1 t s v w
                (eta p) : Real) : Complex) * Complex.I)
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        rw [Finset.sum_mul]
    _ = ∫ eta, ∏ p : S, Complex.exp
          (((harperTwoHeightProjectedPrimeIncrement p.1.1 t s v w
            (eta p.1) : Real) : Complex) * Complex.I)
          ∂harperTwoHeightCubeLaw y t s := by
      congr 1
      funext eta
      exact (Finset.prod_coe_sort S (fun p ↦ Complex.exp
        (((harperTwoHeightProjectedPrimeIncrement p.1 t s v w (eta p) :
          Real) : Complex) * Complex.I))).symm
    _ = ∏ p : S, ∫ eta, Complex.exp
          (((harperTwoHeightProjectedPrimeIncrement p.1.1 t s v w
            (eta p.1) : Real) : Complex) * Complex.I)
          ∂harperTwoHeightCubeLaw y t s := by
      simpa only [g, coord, Function.comp_apply] using hprod
    _ = ∏ p : S, harperTwoHeightProjectedPrimeCharacteristic p.1.1
          (Nat.prime_of_mem_primesBelow p.1.property) t s v w := by
      apply Finset.prod_congr rfl
      intro p hpS
      exact integral_harperTwoHeightCube_eval_complex y t s p.1
        (fun b ↦ Complex.exp
          (((harperTwoHeightProjectedPrimeIncrement p.1.1 t s v w b :
            Real) : Complex) * Complex.I))
    _ = harperTwoHeightProjectedBlockCharacteristic y S t s v w := by
      unfold harperTwoHeightProjectedBlockCharacteristic
      exact Finset.prod_coe_sort S (fun p ↦
        harperTwoHeightProjectedPrimeCharacteristic p.1
          (Nat.prime_of_mem_primesBelow p.property) t s v w)

noncomputable def harperTwoHeightProjectedBlockVariance
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) : Real :=
  ∑ p ∈ S, harperTwoHeightProjectedPrimeVariance p.1
    (Nat.prime_of_mem_primesBelow p.property) t s v w

theorem harperTwoHeightProjectedBlockVariance_nonneg
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real) :
    0 ≤ harperTwoHeightProjectedBlockVariance y S t s v w := by
  unfold harperTwoHeightProjectedBlockVariance
  exact Finset.sum_nonneg fun p hpS ↦
    harperTwoHeightProjectedPrimeVariance_nonneg p.1
      (Nat.prime_of_mem_primesBelow p.property) t s v w

/-- Finite-block bivariate characteristic comparison in every Fourier
direction.  The first error is cubic and the second is the elementary
quadratic-to-exponential correction. -/
theorem norm_harperTwoHeightProjectedBlockCharacteristic_sub_gaussian_le
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real)
    (hsmall : ∀ p ∈ S,
      2 * (|v| + |w|) * (Real.sqrt (p.1 : Real))⁻¹ ≤ 1)
    (hquad : ∀ p ∈ S,
      harperTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) t s v w / 2 ≤
        1 / 2) :
    ‖harperTwoHeightProjectedBlockCharacteristic y S t s v w -
        Complex.exp
          (-((harperTwoHeightProjectedBlockVariance y S t s v w / 2 :
            Real) : Complex))‖ ≤
      (∑ p ∈ S,
        (2 * (|v| + |w|) *
          (Real.sqrt (p.1 : Real))⁻¹) ^ (3 : Nat)) +
      ∑ p ∈ S,
        (harperTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) t s v w / 2) ^
            (2 : Nat) := by
  let phi : Problem520.HarperPrimeIndex y → Complex := fun p ↦
    harperTwoHeightProjectedPrimeCharacteristic p.1
      (Nat.prime_of_mem_primesBelow p.property) t s v w
  let q : Problem520.HarperPrimeIndex y → Real := fun p ↦
    harperTwoHeightProjectedPrimeVariance p.1
      (Nat.prime_of_mem_primesBelow p.property) t s v w / 2
  let linear : Problem520.HarperPrimeIndex y → Complex := fun p ↦
    1 - (q p : Complex)
  let gaussian : Problem520.HarperPrimeIndex y → Complex := fun p ↦
    Complex.exp (-(q p : Complex))
  have hphi : ∀ p ∈ S, ‖phi p‖ ≤ 1 := by
    intro p hpS
    exact norm_harperTwoHeightProjectedPrimeCharacteristic_le_one p.1
      (Nat.prime_of_mem_primesBelow p.property) t s v w
  have hqNonneg : ∀ p, 0 ≤ q p := by
    intro p
    exact div_nonneg
      (harperTwoHeightProjectedPrimeVariance_nonneg p.1
        (Nat.prime_of_mem_primesBelow p.property) t s v w)
      (by norm_num)
  have hlinear : ∀ p ∈ S, ‖linear p‖ ≤ 1 := by
    intro p hpS
    have hqle : q p ≤ 1 := (hquad p hpS).trans (by norm_num)
    change ‖(1 : Complex) - (q p : Complex)‖ ≤ 1
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hqle)]
    linarith [hqNonneg p]
  have hgaussian : ∀ p ∈ S, ‖gaussian p‖ ≤ 1 := by
    intro p hpS
    change ‖Complex.exp (-(q p : Complex))‖ ≤ 1
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hqNonneg p))
  have hfirst := Problem520.norm_prod_sub_prod_le_sum_norm_sub
    S phi linear hphi hlinear
  have hsecond := Problem520.norm_prod_sub_prod_le_sum_norm_sub
    S linear gaussian hlinear hgaussian
  have hfirstBound :
      ‖(∏ p ∈ S, phi p) - ∏ p ∈ S, linear p‖ ≤
        ∑ p ∈ S,
          (2 * (|v| + |w|) *
            (Real.sqrt (p.1 : Real))⁻¹) ^ (3 : Nat) := by
    exact hfirst.trans (Finset.sum_le_sum fun p hpS ↦ by
      simpa only [phi, linear, q] using
        norm_harperTwoHeightProjectedPrimeCharacteristic_sub_quadratic_le
          (Nat.prime_of_mem_primesBelow p.property) t s v w
          (hsmall p hpS))
  have hsecondBound :
      ‖(∏ p ∈ S, linear p) - ∏ p ∈ S, gaussian p‖ ≤
        ∑ p ∈ S, (q p) ^ (2 : Nat) := by
    exact hsecond.trans (Finset.sum_le_sum fun p hpS ↦ by
      simpa only [linear, gaussian] using
        Problem520.norm_one_sub_sub_exp_neg_le_sq
          (hqNonneg p) ((hquad p hpS).trans (by norm_num)))
  have hprodGaussian :
      (∏ p ∈ S, gaussian p) =
        Complex.exp
          (-((harperTwoHeightProjectedBlockVariance y S t s v w / 2 :
            Real) : Complex)) := by
    rw [← Complex.exp_sum]
    congr 1
    unfold harperTwoHeightProjectedBlockVariance
    dsimp only [gaussian, q]
    push_cast
    rw [Finset.sum_neg_distrib, Finset.sum_div]
  change
    ‖(∏ p ∈ S, phi p) -
        Complex.exp
          (-((harperTwoHeightProjectedBlockVariance y S t s v w / 2 :
            Real) : Complex))‖ ≤ _
  rw [← hprodGaussian]
  calc
    ‖(∏ p ∈ S, phi p) - ∏ p ∈ S, gaussian p‖ ≤
        ‖(∏ p ∈ S, phi p) - ∏ p ∈ S, linear p‖ +
          ‖(∏ p ∈ S, linear p) - ∏ p ∈ S, gaussian p‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (∑ p ∈ S,
          (2 * (|v| + |w|) *
            (Real.sqrt (p.1 : Real))⁻¹) ^ (3 : Nat)) +
        ∑ p ∈ S, (q p) ^ (2 : Nat) :=
      add_le_add hfirstBound hsecondBound
    _ = _ := by rfl

/-- Law-level Cramer--Wold comparison for the actual two-height block. -/
theorem norm_harperTwoHeightProjectedCubeCharacteristic_sub_gaussian_le
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s v w : Real)
    (hsmall : ∀ p ∈ S,
      2 * (|v| + |w|) * (Real.sqrt (p.1 : Real))⁻¹ ≤ 1)
    (hquad : ∀ p ∈ S,
      harperTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) t s v w / 2 ≤
        1 / 2) :
    ‖harperTwoHeightProjectedCubeCharacteristic y S t s v w -
        Complex.exp
          (-((harperTwoHeightProjectedBlockVariance y S t s v w / 2 :
            Real) : Complex))‖ ≤
      (∑ p ∈ S,
        (2 * (|v| + |w|) *
          (Real.sqrt (p.1 : Real))⁻¹) ^ (3 : Nat)) +
      ∑ p ∈ S,
        (harperTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) t s v w / 2) ^
            (2 : Nat) := by
  rw [harperTwoHeightProjectedCubeCharacteristic_eq_block]
  exact norm_harperTwoHeightProjectedBlockCharacteristic_sub_gaussian_le
    y S t s v w hsmall hquad

/-! ## Scheduled block specialization -/

/-- On the natural two-dimensional Fourier window, a scheduled two-height
block has the same doubly-exponentially decaying characteristic error as the
one-height block. -/
theorem norm_harperTwoHeightScheduledProjectedCubeCharacteristic_sub_gaussian_le
    (y j : Nat) (t s v w : Real)
    (hfrequency :
      2 * (|v| + |w|) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real)) :
    ‖harperTwoHeightProjectedCubeCharacteristic y
          (Problem520.harperScheduledPrimeBlock y j) t s v w -
        Complex.exp
          (-((harperTwoHeightProjectedBlockVariance y
            (Problem520.harperScheduledPrimeBlock y j) t s v w / 2 :
              Real) : Complex))‖ ≤
      (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
        (16 * (|v| + |w|) ^ (3 : Nat) +
          2 * (|v| + |w|) ^ (4 : Nat)) := by
  let S := Problem520.harperScheduledPrimeBlock y j
  let R : Real := |v| + |w|
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hsmall : ∀ p ∈ S,
      2 * R * (Real.sqrt (p.1 : Real))⁻¹ ≤ 1 := by
    intro p hpS
    have hpPos : (0 : Real) < p.1 := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow p.property).pos
    have hsqrtPos : 0 < Real.sqrt (p.1 : Real) := Real.sqrt_pos.2 hpPos
    have hpA : (Problem520.harperBlockEndpoint j : Real) ≤ p.1 := by
      exact_mod_cast
        ((Problem520.mem_harperScheduledPrimeBlock p).mp hpS).1.le
    have hsqrtOrder :
        Real.sqrt (Problem520.harperBlockEndpoint j : Real) ≤
          Real.sqrt (p.1 : Real) := Real.sqrt_le_sqrt hpA
    have hnum : 2 * R ≤ Real.sqrt (p.1 : Real) :=
      hfrequency.trans hsqrtOrder
    rw [mul_inv_le_iff₀ hsqrtPos]
    simpa only [one_mul] using hnum
  have hquad : ∀ p ∈ S,
      harperTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) t s v w / 2 ≤
        1 / 2 := by
    intro p hpS
    let B : Real := 2 * R * (Real.sqrt (p.1 : Real))⁻¹
    have hB0 : 0 ≤ B := by dsimp only [B]; positivity
    have hB1 : B ≤ 1 := hsmall p hpS
    have hvar := harperTwoHeightProjectedPrimeVariance_le_envelope
      (Nat.prime_of_mem_primesBelow p.property) t s v w
    have hBsq : B ^ (2 : Nat) ≤ 1 := by nlinarith [sq_nonneg (1 - B)]
    have hvarB :
        harperTwoHeightProjectedPrimeVariance p.1
            (Nat.prime_of_mem_primesBelow p.property) t s v w ≤ B ^ (2 : Nat) := by
      simpa only [B, R] using hvar
    nlinarith
  have hbase :=
    norm_harperTwoHeightProjectedCubeCharacteristic_sub_gaussian_le
      y S t s v w
      (by simpa only [R] using hsmall)
      hquad
  have hcubicEq :
      (∑ p ∈ S,
        (2 * R * (Real.sqrt (p.1 : Real))⁻¹) ^ (3 : Nat)) =
        12 * R ^ (3 : Nat) *
          Problem520.harperBlockCubicRemainder y S := by
    unfold Problem520.harperBlockCubicRemainder
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hpS
    ring
  have hquarticPoint : ∀ p ∈ S,
      (harperTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) t s v w / 2) ^
          (2 : Nat) ≤
        R ^ (4 : Nat) * (Real.sqrt (p.1 : Real))⁻¹ ^ (3 : Nat) := by
    intro p hpS
    let z : Real := (Real.sqrt (p.1 : Real))⁻¹
    let q : Real := harperTwoHeightProjectedPrimeVariance p.1
      (Nat.prime_of_mem_primesBelow p.property) t s v w / 2
    have hpPrime := Nat.prime_of_mem_primesBelow p.property
    have hp16 : 16 ≤ p.1 :=
      Problem520.sixteen_le_prime_of_mem_harperScheduledPrimeBlock hpS
    have hpPos : (0 : Real) < p.1 := by exact_mod_cast hpPrime.pos
    have hsqrtPos : 0 < Real.sqrt (p.1 : Real) := Real.sqrt_pos.2 hpPos
    have hz0 : 0 ≤ z := by dsimp only [z]; positivity
    have hsqrtFour : (4 : Real) ≤ Real.sqrt (p.1 : Real) := by
      have h16 : (16 : Real) ≤ p.1 := by exact_mod_cast hp16
      have := Real.sqrt_le_sqrt h16
      norm_num at this ⊢
      exact this
    have hzQuarter : z ≤ (1 / 4 : Real) := by
      dsimp only [z]
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : Real) < 4)
          hsqrtFour)
    have hq0 : 0 ≤ q := by
      dsimp only [q]
      exact div_nonneg
        (harperTwoHeightProjectedPrimeVariance_nonneg p.1 hpPrime
          t s v w) (by norm_num)
    have hvar := harperTwoHeightProjectedPrimeVariance_le_envelope
      hpPrime t s v w
    have hqle : q ≤ 2 * R ^ (2 : Nat) * z ^ (2 : Nat) := by
      dsimp only [q, z, R] at hvar ⊢
      nlinarith
    have hqSq := pow_le_pow_left₀ hq0 hqle 2
    calc
      q ^ (2 : Nat) ≤
          (2 * R ^ (2 : Nat) * z ^ (2 : Nat)) ^ (2 : Nat) := hqSq
      _ = R ^ (4 : Nat) * z ^ (3 : Nat) * (4 * z) := by ring
      _ ≤ R ^ (4 : Nat) * z ^ (3 : Nat) * 1 := by
        gcongr
        nlinarith
      _ = R ^ (4 : Nat) * z ^ (3 : Nat) := by ring
  have hquartic :
      (∑ p ∈ S,
        (harperTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) t s v w / 2) ^
            (2 : Nat)) ≤
        (3 / 2 : Real) * R ^ (4 : Nat) *
          Problem520.harperBlockCubicRemainder y S := by
    calc
      (∑ p ∈ S,
          (harperTwoHeightProjectedPrimeVariance p.1
            (Nat.prime_of_mem_primesBelow p.property) t s v w / 2) ^
              (2 : Nat)) ≤
          ∑ p ∈ S,
            R ^ (4 : Nat) *
              (Real.sqrt (p.1 : Real))⁻¹ ^ (3 : Nat) :=
        Finset.sum_le_sum hquarticPoint
      _ = (3 / 2 : Real) * R ^ (4 : Nat) *
          Problem520.harperBlockCubicRemainder y S := by
        unfold Problem520.harperBlockCubicRemainder
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hpS
        ring
  have hremainder := Problem520.harperBlockCubicRemainder_scheduled_le y j
  change
    ‖harperTwoHeightProjectedCubeCharacteristic y S t s v w -
        Complex.exp
          (-((harperTwoHeightProjectedBlockVariance y S t s v w / 2 :
            Real) : Complex))‖ ≤ _
  calc
    _ ≤ (∑ p ∈ S,
          (2 * R * (Real.sqrt (p.1 : Real))⁻¹) ^ (3 : Nat)) +
        ∑ p ∈ S,
          (harperTwoHeightProjectedPrimeVariance p.1
            (Nat.prime_of_mem_primesBelow p.property) t s v w / 2) ^
              (2 : Nat) := by
      simpa only [R] using hbase
    _ ≤ 12 * R ^ (3 : Nat) *
          Problem520.harperBlockCubicRemainder y S +
        (3 / 2 : Real) * R ^ (4 : Nat) *
          Problem520.harperBlockCubicRemainder y S := by
      rw [hcubicEq]
      gcongr
    _ ≤ 12 * R ^ (3 : Nat) *
          ((4 / 3 : Real) *
            (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹) +
        (3 / 2 : Real) * R ^ (4 : Nat) *
          ((4 / 3 : Real) *
            (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹) := by
      gcongr
    _ = (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
        (16 * R ^ (3 : Nat) + 2 * R ^ (4 : Nat)) := by ring
    _ = _ := by rfl

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.norm_harperTwoHeightProjectedPrimeCharacteristic_sub_quadratic_le
#print axioms Erdos.Problem1144.norm_harperTwoHeightProjectedBlockCharacteristic_sub_gaussian_le
#print axioms Erdos.Problem1144.harperTwoHeightProjectedCubeCharacteristic_eq_block
#print axioms Erdos.Problem1144.norm_harperTwoHeightProjectedCubeCharacteristic_sub_gaussian_le
#print axioms Erdos.Problem1144.norm_harperTwoHeightScheduledProjectedCubeCharacteristic_sub_gaussian_le
