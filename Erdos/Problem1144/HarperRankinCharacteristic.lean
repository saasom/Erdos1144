import Erdos.Problem1144.HarperRankinTiltedLaw
import Erdos.Problem520.HarperBlockGaussian

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Gaussian characteristic comparison for a Rankin-shifted coordinate

The shifted centered coordinate has exactly zero mean, its explicit shifted
variance, and the same cubic envelope as the critical-line coordinate.  The
existing Taylor argument therefore transfers with unchanged numerical error.
-/

/-- Purely imaginary characteristic exponent of one shifted centered
coordinate. -/
noncomputable def harperRankinCharacteristicExponent
    (p : ℕ) (a t u v : ℝ) (b : Bool) : ℂ :=
  ((v * harperRankinCenteredLinearPrimeIncrement p a t u b : ℝ) : ℂ) *
    Complex.I

theorem norm_harperRankinCharacteristicExponent
    (p : ℕ) (a t u v : ℝ) (b : Bool) :
    ‖harperRankinCharacteristicExponent p a t u v b‖ =
      |v| * |harperRankinCenteredLinearPrimeIncrement p a t u b| := by
  rw [harperRankinCharacteristicExponent, norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs, abs_mul]

theorem norm_harperRankinCharacteristicExponent_le_one
    {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a)
    (t u v : ℝ)
    (hsmall : |v| * (2 * (Real.sqrt (p : ℝ))⁻¹) ≤ 1)
    (b : Bool) :
    ‖harperRankinCharacteristicExponent p a t u v b‖ ≤ 1 := by
  rw [norm_harperRankinCharacteristicExponent]
  exact (mul_le_mul_of_nonneg_left
      (abs_harperRankinCenteredLinearPrimeIncrement_le hp ha t u b)
      (abs_nonneg v)).trans hsmall

/-- Second-order Taylor polynomial for the shifted characteristic
exponent. -/
noncomputable def harperRankinCharacteristicQuadratic
    (p : ℕ) (a t u v : ℝ) (b : Bool) : ℂ :=
  1 + harperRankinCharacteristicExponent p a t u v b +
    harperRankinCharacteristicExponent p a t u v b ^ 2 / 2

theorem norm_exp_harperRankinCharacteristicExponent_sub_quadratic_le
    {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a)
    (t u v : ℝ)
    (hsmall : |v| * (2 * (Real.sqrt (p : ℝ))⁻¹) ≤ 1)
    (b : Bool) :
    ‖Complex.exp (harperRankinCharacteristicExponent p a t u v b) -
        harperRankinCharacteristicQuadratic p a t u v b‖ ≤
      |v| ^ 3 *
        |harperRankinCenteredLinearPrimeIncrement p a t u b| ^ 3 := by
  let z := harperRankinCharacteristicExponent p a t u v b
  have hz : ‖z‖ ≤ 1 :=
    norm_harperRankinCharacteristicExponent_le_one hp ha t u v hsmall b
  have hExp := Complex.exp_bound hz (n := 3) (by decide)
  have hpoly :
      (∑ m ∈ Finset.range 3, z ^ m / (m.factorial : ℂ)) =
        harperRankinCharacteristicQuadratic p a t u v b := by
    dsimp [harperRankinCharacteristicQuadratic, z]
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hpoly] at hExp
  calc
    ‖Complex.exp z - harperRankinCharacteristicQuadratic p a t u v b‖ ≤
        ‖z‖ ^ 3 *
          ((Nat.succ 3 : ℝ) * ((Nat.factorial 3) * (3 : ℕ) : ℝ)⁻¹) :=
      hExp
    _ ≤ ‖z‖ ^ 3 := by
      have hzpow : 0 ≤ ‖z‖ ^ 3 := by positivity
      norm_num [Nat.factorial]
      linarith
    _ = |v| ^ 3 *
        |harperRankinCenteredLinearPrimeIncrement p a t u b| ^ 3 := by
      rw [norm_harperRankinCharacteristicExponent]
      ring

/-- One-coordinate characteristic function under the shifted tilted coin. -/
noncomputable def harperRankinTiltedLinearPrimeCharacteristic
    (p : ℕ) (a t u v : ℝ) : ℂ :=
  ∫ b, Complex.exp (harperRankinCharacteristicExponent p a t u v b)
    ∂harperRankinTiltedCoin p a t

theorem integral_harperRankinCharacteristicExponent
    (p : ℕ) (a t u v : ℝ) :
    (∫ b, harperRankinCharacteristicExponent p a t u v b
        ∂harperRankinTiltedCoin p a t) = 0 := by
  unfold harperRankinCharacteristicExponent
  calc
    (∫ b,
        ((v * harperRankinCenteredLinearPrimeIncrement p a t u b : ℝ) : ℂ) *
          Complex.I ∂harperRankinTiltedCoin p a t) =
        (∫ b,
          ((v * harperRankinCenteredLinearPrimeIncrement p a t u b : ℝ) : ℂ)
          ∂harperRankinTiltedCoin p a t) * Complex.I :=
      integral_mul_const Complex.I _
    _ =
        (((∫ b, v * harperRankinCenteredLinearPrimeIncrement p a t u b
            ∂harperRankinTiltedCoin p a t : ℝ) : ℂ) * Complex.I) := by
      congr 1
      exact integral_ofReal
    _ = 0 := by
      rw [integral_const_mul,
        integral_harperRankinCenteredLinearPrimeIncrement]
      simp

theorem integral_harperRankinCharacteristicExponent_sq
    (p : ℕ) (a t u v : ℝ) :
    (∫ b, harperRankinCharacteristicExponent p a t u v b ^ 2
        ∂harperRankinTiltedCoin p a t) =
      -((v ^ 2 * harperRankinCenteredLinearPrimeVariance p a t u : ℝ) : ℂ) := by
  have hpoint (b : Bool) :
      harperRankinCharacteristicExponent p a t u v b ^ 2 =
        -((v ^ 2 *
          harperRankinCenteredLinearPrimeIncrement p a t u b ^ 2 : ℝ) : ℂ) := by
    unfold harperRankinCharacteristicExponent
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  simp_rw [hpoint]
  rw [integral_neg]
  have hcast :
      (∫ b,
          ((v ^ 2 *
            harperRankinCenteredLinearPrimeIncrement p a t u b ^ 2 : ℝ) : ℂ)
          ∂harperRankinTiltedCoin p a t) =
        ((∫ b, v ^ 2 *
            harperRankinCenteredLinearPrimeIncrement p a t u b ^ 2
            ∂harperRankinTiltedCoin p a t : ℝ) : ℂ) :=
    integral_ofReal
  rw [hcast, integral_const_mul,
    integral_harperRankinCenteredLinearPrimeIncrement_sq]

theorem integral_harperRankinCharacteristicQuadratic
    (p : ℕ) (a t u v : ℝ) :
    (∫ b, harperRankinCharacteristicQuadratic p a t u v b
        ∂harperRankinTiltedCoin p a t) =
      1 - ((v ^ 2 * harperRankinCenteredLinearPrimeVariance p a t u / 2 : ℝ) : ℂ) := by
  have hone :
      (∫ _b : Bool, (1 : ℂ) ∂harperRankinTiltedCoin p a t) = 1 := by
    rw [integral_const, probReal_univ, one_smul]
  have hdiv :
      (∫ b, harperRankinCharacteristicExponent p a t u v b ^ 2 / 2
          ∂harperRankinTiltedCoin p a t) =
        -((v ^ 2 * harperRankinCenteredLinearPrimeVariance p a t u : ℝ) : ℂ) /
          2 := by
    calc
      (∫ b, harperRankinCharacteristicExponent p a t u v b ^ 2 / 2
          ∂harperRankinTiltedCoin p a t) =
          (∫ b, harperRankinCharacteristicExponent p a t u v b ^ 2
            ∂harperRankinTiltedCoin p a t) / 2 := integral_div 2 _
      _ = _ := by rw [integral_harperRankinCharacteristicExponent_sq]
  unfold harperRankinCharacteristicQuadratic
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite,
    hone, integral_harperRankinCharacteristicExponent, hdiv]
  push_cast
  ring

/-- The shifted one-coordinate characteristic error has exactly the same
critical-line cubic budget. -/
theorem norm_harperRankinTiltedLinearPrimeCharacteristic_sub_quadratic_le
    {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a)
    (t u v : ℝ)
    (hsmall : |v| * (2 * (Real.sqrt (p : ℝ))⁻¹) ≤ 1) :
    ‖harperRankinTiltedLinearPrimeCharacteristic p a t u v -
        (1 - ((v ^ 2 * harperRankinCenteredLinearPrimeVariance p a t u / 2 : ℝ) : ℂ))‖ ≤
      8 * |v| ^ 3 * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  let R : Bool → ℂ := fun b ↦
    Complex.exp (harperRankinCharacteristicExponent p a t u v b) -
      harperRankinCharacteristicQuadratic p a t u v b
  have hidentity :
      harperRankinTiltedLinearPrimeCharacteristic p a t u v -
          (1 - ((v ^ 2 * harperRankinCenteredLinearPrimeVariance p a t u / 2 : ℝ) : ℂ)) =
        ∫ b, R b ∂harperRankinTiltedCoin p a t := by
    rw [← integral_harperRankinCharacteristicQuadratic p a t u v]
    exact (integral_sub Integrable.of_finite Integrable.of_finite).symm
  rw [hidentity]
  calc
    ‖∫ b, R b ∂harperRankinTiltedCoin p a t‖ ≤
        ∫ b, ‖R b‖ ∂harperRankinTiltedCoin p a t :=
      norm_integral_le_integral_norm R
    _ ≤ ∫ b,
        |v| ^ 3 * |harperRankinCenteredLinearPrimeIncrement p a t u b| ^ 3
        ∂harperRankinTiltedCoin p a t := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro b
      exact norm_exp_harperRankinCharacteristicExponent_sub_quadratic_le
        hp ha t u v hsmall b
    _ = |v| ^ 3 *
        ∫ b, |harperRankinCenteredLinearPrimeIncrement p a t u b| ^ 3
          ∂harperRankinTiltedCoin p a t := by
      rw [integral_const_mul]
    _ ≤ |v| ^ 3 * (8 * (Real.sqrt (p : ℝ))⁻¹ ^ 3) := by
      exact mul_le_mul_of_nonneg_left
        (integral_abs_harperRankinCenteredLinearPrimeIncrement_pow_three_le
          hp ha t u) (by positivity)
    _ = 8 * |v| ^ 3 * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by ring

/-! ## Finite shifted block comparison -/

/-- Sum of shifted centered coordinates over a finite prime block. -/
noncomputable def harperRankinCenteredLinearPrimeBlockSum
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) (eta : Problem520.HarperPrimeCube y) : ℝ :=
  ∑ p ∈ S, harperRankinCenteredLinearPrimeIncrement p.1 a t u (eta p)

/-- Exact variance of the shifted centered finite block. -/
noncomputable def harperRankinLinearBlockVariance
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) : ℝ :=
  ∑ p ∈ S, harperRankinCenteredLinearPrimeVariance p.1 a t u

theorem harperRankinCenteredLinearPrimeVariance_nonneg
    (p : ℕ) (a t u : ℝ) :
    0 ≤ harperRankinCenteredLinearPrimeVariance p a t u := by
  rw [← integral_harperRankinCenteredLinearPrimeIncrement_sq]
  exact integral_nonneg fun b ↦ sq_nonneg _

theorem harperRankinLinearBlockVariance_nonneg
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) :
    0 ≤ harperRankinLinearBlockVariance y S a t u := by
  unfold harperRankinLinearBlockVariance
  exact Finset.sum_nonneg fun p hp ↦
    harperRankinCenteredLinearPrimeVariance_nonneg p.1 a t u

/-- A nonnegative Rankin shift does not enlarge the critical one-prime
variance. -/
theorem harperRankinCenteredLinearPrimeVariance_le_inv
    {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a) (t u : ℝ) :
    harperRankinCenteredLinearPrimeVariance p a t u ≤ (p : ℝ)⁻¹ := by
  let r : ℝ := harperRankinEulerRadius p a
  let c : ℝ := Real.cos (u * Real.log (p : ℝ))
  let bias : ℝ := harperRankinTiltBias p a t
  have hr : 0 ≤ r := harperRankinEulerRadius_nonneg p a
  have hrle : r ≤ (Real.sqrt (p : ℝ))⁻¹ :=
    harperRankinEulerRadius_le_inv_sqrt hp ha
  have hcSq : c ^ 2 ≤ 1 := by
    dsimp only [c]
    nlinarith [Real.neg_one_le_cos (u * Real.log (p : ℝ)),
      Real.cos_le_one (u * Real.log (p : ℝ))]
  have hbAbs : |bias| ≤ 1 := abs_harperRankinTiltBias_le_one p a t
  have hbSq : bias ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg bias) hbAbs
  have hbFactor0 : 0 ≤ 1 - bias ^ 2 := sub_nonneg.mpr hbSq
  have hrSq : r ^ 2 ≤ (Real.sqrt (p : ℝ))⁻¹ ^ 2 :=
    pow_le_pow_left₀ hr hrle 2
  have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hinvSq : (Real.sqrt (p : ℝ))⁻¹ ^ 2 = (p : ℝ)⁻¹ := by
    calc
      (Real.sqrt (p : ℝ))⁻¹ ^ 2 =
          (Real.sqrt (p : ℝ) ^ 2)⁻¹ := by rw [inv_pow]
      _ = (p : ℝ)⁻¹ := by rw [Real.sq_sqrt hpR]
  unfold harperRankinCenteredLinearPrimeVariance
  change (r * c) ^ 2 * (1 - bias ^ 2) ≤ (p : ℝ)⁻¹
  calc
    (r * c) ^ 2 * (1 - bias ^ 2) ≤ (r * c) ^ 2 * 1 := by
      gcongr
      nlinarith [sq_nonneg bias]
    _ = r ^ 2 * c ^ 2 := by ring
    _ ≤ r ^ 2 * 1 := by gcongr
    _ ≤ (Real.sqrt (p : ℝ))⁻¹ ^ 2 := by simpa using hrSq
    _ = (p : ℝ)⁻¹ := hinvSq

/-- Imaginary exponent of the shifted centered block sum. -/
noncomputable def harperRankinCharacteristicBlockExponent
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u v : ℝ) (eta : Problem520.HarperPrimeCube y) : ℂ :=
  ((v * harperRankinCenteredLinearPrimeBlockSum y S a t u eta : ℝ) : ℂ) *
    Complex.I

theorem harperRankinCharacteristicBlockExponent_eq_sum
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u v : ℝ) (eta : Problem520.HarperPrimeCube y) :
    harperRankinCharacteristicBlockExponent y S a t u v eta =
      ∑ p ∈ S,
        harperRankinCharacteristicExponent p.1 a t u v (eta p) := by
  unfold harperRankinCharacteristicBlockExponent
    harperRankinCenteredLinearPrimeBlockSum harperRankinCharacteristicExponent
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

theorem exp_harperRankinCharacteristicBlockExponent_eq_prod
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u v : ℝ) (eta : Problem520.HarperPrimeCube y) :
    Complex.exp (harperRankinCharacteristicBlockExponent y S a t u v eta) =
      ∏ p ∈ S,
        Complex.exp (harperRankinCharacteristicExponent p.1 a t u v (eta p)) := by
  rw [harperRankinCharacteristicBlockExponent_eq_sum, Complex.exp_sum]

/-- Characteristic function of a shifted centered finite prime block. -/
noncomputable def harperRankinTiltedLinearPrimeBlockCharacteristic
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u v : ℝ) : ℂ :=
  ∫ eta, Complex.exp
      (harperRankinCharacteristicBlockExponent y S a t u v eta)
    ∂harperRankinTiltedCubeLaw y a t

theorem integral_harperRankinTiltedCube_eval_complex
    (y : ℕ) (a t : ℝ) (p : Problem520.HarperPrimeIndex y)
    (g : Bool → ℂ) :
    (∫ eta, g (eta p) ∂harperRankinTiltedCubeLaw y a t) =
      ∫ b, g b ∂harperRankinTiltedCoin p.1 a t := by
  have hmp := measurePreserving_harperRankinTiltedCube_eval y a t p
  calc
    (∫ eta, g (eta p) ∂harperRankinTiltedCubeLaw y a t) =
        ∫ b, g b ∂Measure.map
          (fun eta : Problem520.HarperPrimeCube y ↦ eta p)
          (harperRankinTiltedCubeLaw y a t) := by
      symm
      exact integral_map hmp.measurable.aemeasurable
        (measurable_of_finite g).aestronglyMeasurable
    _ = ∫ b, g b ∂harperRankinTiltedCoin p.1 a t := by
      rw [hmp.map_eq]

theorem harperRankinTiltedLinearPrimeBlockCharacteristic_eq_prod
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u v : ℝ) :
    harperRankinTiltedLinearPrimeBlockCharacteristic y S a t u v =
      ∏ p ∈ S,
        harperRankinTiltedLinearPrimeCharacteristic p.1 a t u v := by
  let coord : S → Problem520.HarperPrimeCube y → Bool :=
    fun p eta ↦ eta p.1
  let g : (p : S) → Bool → ℂ := fun p b ↦
    Complex.exp (harperRankinCharacteristicExponent p.1.1 a t u v b)
  have hcoord : iIndepFun coord (harperRankinTiltedCubeLaw y a t) := by
    exact iIndepFun.precomp Subtype.val_injective
      (iIndepFun_harperRankinTiltedCube_coordinates y a t)
  have hfunctions : iIndepFun
      (fun p : S ↦ g p ∘ coord p) (harperRankinTiltedCubeLaw y a t) :=
    hcoord.comp g (fun _ ↦ measurable_of_finite _)
  have hprod := hfunctions.integral_fun_prod_eq_prod_integral
    (fun p ↦ (measurable_of_finite (g p ∘ coord p)).aestronglyMeasurable)
  calc
    harperRankinTiltedLinearPrimeBlockCharacteristic y S a t u v =
        ∫ eta, ∏ p ∈ S,
          Complex.exp
            (harperRankinCharacteristicExponent p.1 a t u v (eta p))
          ∂harperRankinTiltedCubeLaw y a t := by
      apply integral_congr_ae
      exact ae_of_all _ fun eta ↦
        exp_harperRankinCharacteristicBlockExponent_eq_prod
          y S a t u v eta
    _ = ∫ eta, ∏ p : S,
          Complex.exp
            (harperRankinCharacteristicExponent p.1.1 a t u v (eta p.1))
          ∂harperRankinTiltedCubeLaw y a t := by
      congr 1
      funext eta
      exact (Finset.prod_coe_sort S
        (fun p ↦ Complex.exp
          (harperRankinCharacteristicExponent p.1 a t u v (eta p)))).symm
    _ = ∏ p : S,
        ∫ eta,
          Complex.exp
            (harperRankinCharacteristicExponent p.1.1 a t u v (eta p.1))
          ∂harperRankinTiltedCubeLaw y a t := by
      simpa only [coord, g, Function.comp_apply] using hprod
    _ = ∏ p : S,
        harperRankinTiltedLinearPrimeCharacteristic p.1.1 a t u v := by
      apply Finset.prod_congr rfl
      intro p hp
      simpa only [harperRankinTiltedLinearPrimeCharacteristic] using
        integral_harperRankinTiltedCube_eval_complex y a t p.1
          (fun b ↦ Complex.exp
            (harperRankinCharacteristicExponent p.1.1 a t u v b))
    _ = ∏ p ∈ S,
        harperRankinTiltedLinearPrimeCharacteristic p.1 a t u v :=
      Finset.prod_coe_sort S
        (fun p ↦ harperRankinTiltedLinearPrimeCharacteristic p.1 a t u v)

/-- One-prime nonnegative quadratic Gaussian exponent. -/
noncomputable def harperRankinPrimeGaussianQuadratic
    (p : ℕ) (a t u v : ℝ) : ℝ :=
  v ^ 2 * harperRankinCenteredLinearPrimeVariance p a t u / 2

theorem harperRankinPrimeGaussianQuadratic_nonneg
    (p : ℕ) (a t u v : ℝ) :
    0 ≤ harperRankinPrimeGaussianQuadratic p a t u v := by
  unfold harperRankinPrimeGaussianQuadratic
  exact div_nonneg
    (mul_nonneg (sq_nonneg v)
      (harperRankinCenteredLinearPrimeVariance_nonneg p a t u))
    (by norm_num)

theorem sum_harperRankinPrimeGaussianQuadratic
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u v : ℝ) :
    (∑ p ∈ S, harperRankinPrimeGaussianQuadratic p.1 a t u v) =
      v ^ 2 * harperRankinLinearBlockVariance y S a t u / 2 := by
  unfold harperRankinPrimeGaussianQuadratic harperRankinLinearBlockVariance
  rw [← Finset.sum_div, ← Finset.mul_sum]

theorem norm_harperRankinTiltedLinearPrimeCharacteristic_le_one
    (p : ℕ) (a t u v : ℝ) :
    ‖harperRankinTiltedLinearPrimeCharacteristic p a t u v‖ ≤ 1 := by
  unfold harperRankinTiltedLinearPrimeCharacteristic
  calc
    ‖∫ b, Complex.exp (harperRankinCharacteristicExponent p a t u v b)
        ∂harperRankinTiltedCoin p a t‖ ≤
        ∫ b, ‖Complex.exp (harperRankinCharacteristicExponent p a t u v b)‖
          ∂harperRankinTiltedCoin p a t := norm_integral_le_integral_norm _
    _ = ∫ _b : Bool, (1 : ℝ) ∂harperRankinTiltedCoin p a t := by
      apply integral_congr_ae
      exact ae_of_all _ fun b ↦ by
        unfold harperRankinCharacteristicExponent
        exact Complex.norm_exp_ofReal_mul_I _
    _ = 1 := by rw [integral_const, probReal_univ, one_smul]

theorem prod_exp_neg_harperRankinPrimeGaussianQuadratic
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u v : ℝ) :
    (∏ p ∈ S,
        Complex.exp (-(harperRankinPrimeGaussianQuadratic p.1 a t u v : ℂ))) =
      Complex.exp
        (-((v ^ 2 * harperRankinLinearBlockVariance y S a t u / 2 : ℝ) : ℂ)) := by
  rw [← Complex.exp_sum]
  congr 1
  rw [← sum_harperRankinPrimeGaussianQuadratic y S a t u v]
  push_cast
  rw [Finset.sum_neg_distrib]

/-- Arbitrary finite shifted block versus its matching Gaussian.  The cubic
term is literally unchanged from the critical line. -/
theorem norm_harperRankinTiltedLinearPrimeBlockCharacteristic_sub_gaussian_le
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (hprime : ∀ p ∈ S, 1 ≤ p.1) {a : ℝ} (ha : 0 ≤ a)
    (t u v : ℝ)
    (hsmall : ∀ p ∈ S,
      |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) ≤ 1)
    (hquad : ∀ p ∈ S,
      harperRankinPrimeGaussianQuadratic p.1 a t u v ≤ 1 / 2) :
    ‖harperRankinTiltedLinearPrimeBlockCharacteristic y S a t u v -
        Complex.exp
          (-((v ^ 2 * harperRankinLinearBlockVariance y S a t u / 2 : ℝ) : ℂ))‖ ≤
      (∑ p ∈ S, 8 * |v| ^ 3 * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3) +
        ∑ p ∈ S, harperRankinPrimeGaussianQuadratic p.1 a t u v ^ 2 := by
  let phi : Problem520.HarperPrimeIndex y → ℂ := fun p ↦
    harperRankinTiltedLinearPrimeCharacteristic p.1 a t u v
  let linearGaussian : Problem520.HarperPrimeIndex y → ℂ := fun p ↦
    (1 : ℂ) - (harperRankinPrimeGaussianQuadratic p.1 a t u v : ℂ)
  let exactGaussian : Problem520.HarperPrimeIndex y → ℂ := fun p ↦
    Complex.exp (-(harperRankinPrimeGaussianQuadratic p.1 a t u v : ℂ))
  have hphi : ∀ p ∈ S, ‖phi p‖ ≤ 1 := fun p hp ↦
    norm_harperRankinTiltedLinearPrimeCharacteristic_le_one p.1 a t u v
  have hlinear' : ∀ p ∈ S, ‖linearGaussian p‖ ≤ 1 := by
    intro p hp
    have hq0 := harperRankinPrimeGaussianQuadratic_nonneg p.1 a t u v
    have hq1 : harperRankinPrimeGaussianQuadratic p.1 a t u v ≤ 1 :=
      (hquad p hp).trans (by norm_num)
    rw [show linearGaussian p =
      (1 : ℂ) - (harperRankinPrimeGaussianQuadratic p.1 a t u v : ℂ) by rfl,
      ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hq1)]
    linarith
  have hexact : ∀ p ∈ S, ‖exactGaussian p‖ ≤ 1 := by
    intro p hp
    rw [show exactGaussian p =
      Complex.exp (-(harperRankinPrimeGaussianQuadratic p.1 a t u v : ℂ)) by rfl,
      Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (harperRankinPrimeGaussianQuadratic_nonneg p.1 a t u v))
  have hfirst := Problem520.norm_prod_sub_prod_le_sum_norm_sub
    S phi linearGaussian hphi hlinear'
  have hsecond := Problem520.norm_prod_sub_prod_le_sum_norm_sub
    S linearGaussian exactGaussian hlinear' hexact
  rw [harperRankinTiltedLinearPrimeBlockCharacteristic_eq_prod,
    ← prod_exp_neg_harperRankinPrimeGaussianQuadratic y S a t u v]
  calc
    ‖(∏ p ∈ S, phi p) - ∏ p ∈ S, exactGaussian p‖ ≤
        ‖(∏ p ∈ S, phi p) - ∏ p ∈ S, linearGaussian p‖ +
          ‖(∏ p ∈ S, linearGaussian p) - ∏ p ∈ S, exactGaussian p‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (∑ p ∈ S,
          8 * |v| ^ 3 * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3) +
        ∑ p ∈ S, harperRankinPrimeGaussianQuadratic p.1 a t u v ^ 2 := by
      apply add_le_add
      · exact hfirst.trans (Finset.sum_le_sum fun p hp ↦ by
          simpa only [phi, linearGaussian,
            harperRankinPrimeGaussianQuadratic] using
            norm_harperRankinTiltedLinearPrimeCharacteristic_sub_quadratic_le
              (hprime p hp) ha t u v (hsmall p hp))
      · exact hsecond.trans (Finset.sum_le_sum fun p hp ↦ by
          simpa only [linearGaussian, exactGaussian] using
            Problem520.norm_one_sub_sub_exp_neg_le_sq
              (harperRankinPrimeGaussianQuadratic_nonneg p.1 a t u v)
              ((hquad p hp).trans (by norm_num)))

/-- Scheduled shifted block comparison with the same cubic constant as the
critical-line theorem. -/
theorem norm_harperRankinScheduledBlockCharacteristic_sub_gaussian_le
    (y j : ℕ) {a : ℝ} (ha : 0 ≤ a) (t u v : ℝ)
    (hsmall : ∀ p ∈ Problem520.harperScheduledPrimeBlock y j,
      |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) ≤ 1)
    (hquad : ∀ p ∈ Problem520.harperScheduledPrimeBlock y j,
      harperRankinPrimeGaussianQuadratic p.1 a t u v ≤ 1 / 2) :
    ‖harperRankinTiltedLinearPrimeBlockCharacteristic y
          (Problem520.harperScheduledPrimeBlock y j) a t u v -
        Complex.exp
          (-((v ^ 2 * harperRankinLinearBlockVariance y
            (Problem520.harperScheduledPrimeBlock y j) a t u / 2 : ℝ) : ℂ))‖ ≤
      16 * |v| ^ 3 *
          (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ +
        ∑ p ∈ Problem520.harperScheduledPrimeBlock y j,
          harperRankinPrimeGaussianQuadratic p.1 a t u v ^ 2 := by
  let S := Problem520.harperScheduledPrimeBlock y j
  have hgeneral :=
    norm_harperRankinTiltedLinearPrimeBlockCharacteristic_sub_gaussian_le
      y S
      (fun p hp ↦ by
        have := Problem520.four_le_prime_of_mem_harperScheduledPrimeBlock hp
        omega)
      ha t u v hsmall hquad
  rw [Problem520.sum_characteristicCubic_eq_blockCubicRemainder] at hgeneral
  have hcubic := Problem520.harperBlockCubicRemainder_scheduled_le y j
  calc
    ‖harperRankinTiltedLinearPrimeBlockCharacteristic y S a t u v -
        Complex.exp
          (-((v ^ 2 * harperRankinLinearBlockVariance y S a t u / 2 : ℝ) : ℂ))‖ ≤
        12 * |v| ^ 3 * Problem520.harperBlockCubicRemainder y S +
          ∑ p ∈ S, harperRankinPrimeGaussianQuadratic p.1 a t u v ^ 2 :=
      hgeneral
    _ ≤ 12 * |v| ^ 3 *
          ((4 / 3 : ℝ) *
            (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹) +
          ∑ p ∈ S, harperRankinPrimeGaussianQuadratic p.1 a t u v ^ 2 := by
      gcongr
    _ = 16 * |v| ^ 3 *
          (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ +
          ∑ p ∈ S, harperRankinPrimeGaussianQuadratic p.1 a t u v ^ 2 := by
      ring

end

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.integral_harperRankinCharacteristicQuadratic
#print axioms Erdos.Problem1144.norm_harperRankinTiltedLinearPrimeCharacteristic_sub_quadratic_le
#print axioms Erdos.Problem1144.harperRankinTiltedLinearPrimeBlockCharacteristic_eq_prod
#print axioms Erdos.Problem1144.norm_harperRankinTiltedLinearPrimeBlockCharacteristic_sub_gaussian_le
#print axioms Erdos.Problem1144.harperRankinCenteredLinearPrimeVariance_le_inv
#print axioms Erdos.Problem1144.norm_harperRankinScheduledBlockCharacteristic_sub_gaussian_le
