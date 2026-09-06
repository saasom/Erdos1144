import Erdos.Problem1144.HarperRankinTwoHeightLaw
import Erdos.Problem1144.HarperRankinCharacteristic

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Centered increments under the Rankin two-height law

The product of two shifted Euler densities is still a product of biased
Rademacher coins.  This file centers the two observed paths under that pair
law and records the exact drift relative to the one-height Rankin centering.
-/

theorem neg_one_le_harperRankinTwoHeightTiltBias
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    (-1 : ℝ) ≤ harperRankinTwoHeightTiltBias p a t s := by
  have hsum := harperRankinTwoHeightCoinWeight_false_add_true hp ha t s
  have hfalse := harperRankinTwoHeightCoinWeight_nonneg hp ha t s false
  have htrue := harperRankinTwoHeightCoinWeight_nonneg hp ha t s true
  unfold harperRankinTwoHeightTiltBias
  linarith

theorem harperRankinTwoHeightTiltBias_le_one
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    harperRankinTwoHeightTiltBias p a t s ≤ (1 : ℝ) := by
  have hsum := harperRankinTwoHeightCoinWeight_false_add_true hp ha t s
  have hfalse := harperRankinTwoHeightCoinWeight_nonneg hp ha t s false
  have htrue := harperRankinTwoHeightCoinWeight_nonneg hp ha t s true
  unfold harperRankinTwoHeightTiltBias
  linarith

theorem abs_cubeSign_sub_harperRankinTwoHeightTiltBias_le_two
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a)
    (t s : ℝ) (b : Bool) :
    |Problem520.cubeSign b - harperRankinTwoHeightTiltBias p a t s| ≤ 2 := by
  have hlower := neg_one_le_harperRankinTwoHeightTiltBias hp ha t s
  have hupper := harperRankinTwoHeightTiltBias_le_one hp ha t s
  cases b <;> simp only [Problem520.cubeSign, Bool.false_eq_true,
    if_false, if_true] <;> rw [abs_le] <;> constructor <;> linarith

/-- The fluctuation at height `u`, centered under the shifted two-height
coin. -/
noncomputable def harperRankinTwoHeightPrimeFluctuation
    (p : ℕ) (a t s u : ℝ) (b : Bool) : ℝ :=
  (Problem520.cubeSign b - harperRankinTwoHeightTiltBias p a t s) *
    (harperRankinEulerRadius p a *
      Real.cos (u * Real.log (p : ℝ)))

theorem abs_harperRankinTwoHeightPrimeFluctuation_le
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a)
    (t s u : ℝ) (b : Bool) :
    |harperRankinTwoHeightPrimeFluctuation p a t s u b| ≤
      2 * (Real.sqrt (p : ℝ))⁻¹ := by
  have hr := harperRankinEulerRadius_le_inv_sqrt hp.one_le ha
  have hr0 := harperRankinEulerRadius_nonneg p a
  unfold harperRankinTwoHeightPrimeFluctuation
  rw [abs_mul, abs_mul, abs_of_nonneg hr0]
  calc
    |Problem520.cubeSign b - harperRankinTwoHeightTiltBias p a t s| *
          (harperRankinEulerRadius p a *
            |Real.cos (u * Real.log (p : ℝ))|) ≤
        2 * ((Real.sqrt (p : ℝ))⁻¹ * 1) := by
      gcongr
      · exact abs_cubeSign_sub_harperRankinTwoHeightTiltBias_le_two
          hp ha t s b
      · exact Real.abs_cos_le_one _
    _ = 2 * (Real.sqrt (p : ℝ))⁻¹ := by ring

theorem integral_harperRankinTwoHeightPrimeFluctuation
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s u : ℝ) :
    (∫ b, harperRankinTwoHeightPrimeFluctuation p a t s u b
        ∂harperRankinTwoHeightCoin p hp a ha t s) = 0 := by
  let c : ℝ := harperRankinEulerRadius p a *
    Real.cos (u * Real.log (p : ℝ))
  unfold harperRankinTwoHeightPrimeFluctuation
  change (∫ b, (Problem520.cubeSign b -
      harperRankinTwoHeightTiltBias p a t s) * c
      ∂harperRankinTwoHeightCoin p hp a ha t s) = 0
  rw [integral_mul_const, integral_sub Integrable.of_finite
    Integrable.of_finite, integral_cubeSign_harperRankinTwoHeightCoin,
    integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self, zero_mul]

/-- A Cramer--Wold projection of the centered pair. -/
noncomputable def harperRankinTwoHeightProjectedPrimeIncrement
    (p : ℕ) (a t s v w : ℝ) (b : Bool) : ℝ :=
  v * harperRankinTwoHeightPrimeFluctuation p a t s t b +
    w * harperRankinTwoHeightPrimeFluctuation p a t s s b

theorem integral_harperRankinTwoHeightProjectedPrimeIncrement
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s v w : ℝ) :
    (∫ b, harperRankinTwoHeightProjectedPrimeIncrement p a t s v w b
        ∂harperRankinTwoHeightCoin p hp a ha t s) = 0 := by
  unfold harperRankinTwoHeightProjectedPrimeIncrement
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_const_mul,
    integral_harperRankinTwoHeightPrimeFluctuation,
    integral_harperRankinTwoHeightPrimeFluctuation,
    mul_zero, mul_zero, add_zero]

theorem abs_harperRankinTwoHeightProjectedPrimeIncrement_le
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a)
    (t s v w : ℝ) (b : Bool) :
    |harperRankinTwoHeightProjectedPrimeIncrement p a t s v w b| ≤
      2 * (|v| + |w|) * (Real.sqrt (p : ℝ))⁻¹ := by
  unfold harperRankinTwoHeightProjectedPrimeIncrement
  calc
    |v * harperRankinTwoHeightPrimeFluctuation p a t s t b +
        w * harperRankinTwoHeightPrimeFluctuation p a t s s b| ≤
      |v * harperRankinTwoHeightPrimeFluctuation p a t s t b| +
        |w * harperRankinTwoHeightPrimeFluctuation p a t s s b| :=
      abs_add_le _ _
    _ = |v| * |harperRankinTwoHeightPrimeFluctuation p a t s t b| +
        |w| * |harperRankinTwoHeightPrimeFluctuation p a t s s b| := by
      rw [abs_mul, abs_mul]
    _ ≤ |v| * (2 * (Real.sqrt (p : ℝ))⁻¹) +
        |w| * (2 * (Real.sqrt (p : ℝ))⁻¹) := by
      gcongr
      · exact abs_harperRankinTwoHeightPrimeFluctuation_le hp ha t s t b
      · exact abs_harperRankinTwoHeightPrimeFluctuation_le hp ha t s s b
    _ = 2 * (|v| + |w|) * (Real.sqrt (p : ℝ))⁻¹ := by ring

/-- Exact projected variance of one shifted pair coordinate. -/
noncomputable def harperRankinTwoHeightProjectedPrimeVariance
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s v w : ℝ) : ℝ :=
  ∫ b, harperRankinTwoHeightProjectedPrimeIncrement p a t s v w b ^ 2
    ∂harperRankinTwoHeightCoin p hp a ha t s

theorem harperRankinTwoHeightProjectedPrimeVariance_nonneg
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s v w : ℝ) :
    0 ≤ harperRankinTwoHeightProjectedPrimeVariance p hp a ha t s v w := by
  unfold harperRankinTwoHeightProjectedPrimeVariance
  exact integral_nonneg fun b ↦ sq_nonneg _

theorem harperRankinTwoHeightProjectedPrimeVariance_le_envelope
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a)
    (t s v w : ℝ) :
    harperRankinTwoHeightProjectedPrimeVariance p hp a ha t s v w ≤
      (2 * (|v| + |w|) * (Real.sqrt (p : ℝ))⁻¹) ^ 2 := by
  let B : ℝ := 2 * (|v| + |w|) * (Real.sqrt (p : ℝ))⁻¹
  unfold harperRankinTwoHeightProjectedPrimeVariance
  calc
    (∫ b, harperRankinTwoHeightProjectedPrimeIncrement p a t s v w b ^ 2
        ∂harperRankinTwoHeightCoin p hp a ha t s) ≤
      ∫ _b : Bool, B ^ 2
        ∂harperRankinTwoHeightCoin p hp a ha t s := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro b
      have habs := abs_harperRankinTwoHeightProjectedPrimeIncrement_le
        hp ha t s v w b
      have hsq := pow_le_pow_left₀ (abs_nonneg _) (by
        simpa only [B] using habs) 2
      simpa only [sq_abs] using hsq
    _ = B ^ 2 := by
      rw [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- Purely imaginary characteristic exponent of one projected shifted pair
coordinate. -/
noncomputable def harperRankinTwoHeightProjectedCharacteristicExponent
    (p : ℕ) (a t s v w : ℝ) (b : Bool) : ℂ :=
  ((harperRankinTwoHeightProjectedPrimeIncrement p a t s v w b : ℝ) : ℂ) *
    Complex.I

theorem norm_harperRankinTwoHeightProjectedCharacteristicExponent
    (p : ℕ) (a t s v w : ℝ) (b : Bool) :
    ‖harperRankinTwoHeightProjectedCharacteristicExponent p a t s v w b‖ =
      |harperRankinTwoHeightProjectedPrimeIncrement p a t s v w b| := by
  rw [harperRankinTwoHeightProjectedCharacteristicExponent, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]

noncomputable def harperRankinTwoHeightProjectedPrimeCharacteristic
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s v w : ℝ) : ℂ :=
  ∫ b, Complex.exp
      (harperRankinTwoHeightProjectedCharacteristicExponent p a t s v w b)
    ∂harperRankinTwoHeightCoin p hp a ha t s

theorem norm_harperRankinTwoHeightProjectedPrimeCharacteristic_le_one
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s v w : ℝ) :
    ‖harperRankinTwoHeightProjectedPrimeCharacteristic
        p hp a ha t s v w‖ ≤ 1 := by
  unfold harperRankinTwoHeightProjectedPrimeCharacteristic
  calc
    ‖∫ b, Complex.exp
          (harperRankinTwoHeightProjectedCharacteristicExponent
            p a t s v w b)
        ∂harperRankinTwoHeightCoin p hp a ha t s‖ ≤
        ∫ b, ‖Complex.exp
          (harperRankinTwoHeightProjectedCharacteristicExponent
            p a t s v w b)‖
          ∂harperRankinTwoHeightCoin p hp a ha t s :=
      norm_integral_le_integral_norm _
    _ = ∫ _b : Bool, (1 : ℝ)
        ∂harperRankinTwoHeightCoin p hp a ha t s := by
      apply integral_congr_ae
      exact ae_of_all _ fun b ↦ by
        exact Complex.norm_exp_ofReal_mul_I _
    _ = 1 := by
      rw [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- One-prime Cramer--Wold characteristic expansion.  The shifted pair has
exactly the same cubic error envelope as the critical-line pair. -/
theorem norm_harperRankinTwoHeightProjectedPrimeCharacteristic_sub_quadratic_le
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a)
    (t s v w : ℝ)
    (hsmall :
      2 * (|v| + |w|) * (Real.sqrt (p : ℝ))⁻¹ ≤ 1) :
    ‖harperRankinTwoHeightProjectedPrimeCharacteristic
          p hp a ha t s v w -
        (1 - ((harperRankinTwoHeightProjectedPrimeVariance
          p hp a ha t s v w / 2 : ℝ) : ℂ))‖ ≤
      (2 * (|v| + |w|) * (Real.sqrt (p : ℝ))⁻¹) ^ 3 := by
  let X : Bool → ℝ :=
    harperRankinTwoHeightProjectedPrimeIncrement p a t s v w
  let Z : Bool → ℂ := fun b ↦ ((X b : ℝ) : ℂ) * Complex.I
  let Q : Bool → ℂ := fun b ↦ 1 + Z b + Z b ^ 2 / 2
  let B : ℝ := 2 * (|v| + |w|) * (Real.sqrt (p : ℝ))⁻¹
  have hZ (b : Bool) : ‖Z b‖ ≤ 1 := by
    have hX := abs_harperRankinTwoHeightProjectedPrimeIncrement_le
      hp ha t s v w b
    have hnorm : ‖Z b‖ = |X b| := by
      dsimp only [Z]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one]
    rw [hnorm]
    exact hX.trans hsmall
  have hTaylor (b : Bool) :
      ‖Complex.exp (Z b) - Q b‖ ≤ B ^ 3 := by
    have hExp := Complex.exp_bound (hZ b) (n := 3) (by decide)
    have hpoly :
        (∑ m ∈ Finset.range 3, Z b ^ m / (m.factorial : ℂ)) =
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
            ((Nat.succ 3 : ℝ) *
              ((Nat.factorial 3) * (3 : ℕ) : ℝ)⁻¹) := hExp
      _ ≤ ‖Z b‖ ^ 3 := by
        have hzpow : 0 ≤ ‖Z b‖ ^ 3 := by positivity
        norm_num [Nat.factorial]
        linarith
      _ = |X b| ^ 3 := by rw [hnorm]
      _ ≤ B ^ 3 := by
        exact pow_le_pow_left₀ (abs_nonneg _) (by
          simpa only [X, B] using
            abs_harperRankinTwoHeightProjectedPrimeIncrement_le
              hp ha t s v w b) 3
  have hmeanZ :
      (∫ b, Z b ∂harperRankinTwoHeightCoin p hp a ha t s) = 0 := by
    dsimp only [Z]
    calc
      (∫ b, (((X b : ℝ) : ℂ) * Complex.I)
          ∂harperRankinTwoHeightCoin p hp a ha t s) =
          (∫ b, ((X b : ℝ) : ℂ)
            ∂harperRankinTwoHeightCoin p hp a ha t s) * Complex.I :=
        integral_mul_const Complex.I _
      _ = (((∫ b, X b
          ∂harperRankinTwoHeightCoin p hp a ha t s) : ℝ) : ℂ) *
            Complex.I := by
        have hcast :
            (∫ b, ((X b : ℝ) : ℂ)
                ∂harperRankinTwoHeightCoin p hp a ha t s) =
              (((∫ b, X b
                ∂harperRankinTwoHeightCoin p hp a ha t s) : ℝ) : ℂ) :=
          integral_ofReal
        rw [hcast]
      _ = 0 := by
        rw [show (∫ b, X b
            ∂harperRankinTwoHeightCoin p hp a ha t s) = 0 by
          simpa only [X] using
            integral_harperRankinTwoHeightProjectedPrimeIncrement
              p hp a ha t s v w]
        simp
  have hsecondZ :
      (∫ b, Z b ^ 2
          ∂harperRankinTwoHeightCoin p hp a ha t s) =
        -((harperRankinTwoHeightProjectedPrimeVariance
          p hp a ha t s v w : ℝ) : ℂ) := by
    have hpoint (b : Bool) : Z b ^ 2 =
        -(((X b) ^ 2 : ℝ) : ℂ) := by
      dsimp only [Z]
      rw [mul_pow, Complex.I_sq]
      push_cast
      ring
    simp_rw [hpoint]
    rw [integral_neg]
    have hcast :
        (∫ b, (((X b) ^ 2 : ℝ) : ℂ)
            ∂harperRankinTwoHeightCoin p hp a ha t s) =
          (((∫ b, X b ^ 2
            ∂harperRankinTwoHeightCoin p hp a ha t s) : ℝ) : ℂ) :=
      integral_ofReal
    rw [hcast]
    rfl
  have hquad :
      (∫ b, Q b ∂harperRankinTwoHeightCoin p hp a ha t s) =
        1 - ((harperRankinTwoHeightProjectedPrimeVariance
          p hp a ha t s v w / 2 : ℝ) : ℂ) := by
    have hone : (∫ _b : Bool, (1 : ℂ)
        ∂harperRankinTwoHeightCoin p hp a ha t s) = 1 := by
      rw [integral_const, probReal_univ]
      exact one_smul ℝ (1 : ℂ)
    have hdiv :
        (∫ b, Z b ^ 2 / 2
            ∂harperRankinTwoHeightCoin p hp a ha t s) =
          -((harperRankinTwoHeightProjectedPrimeVariance
            p hp a ha t s v w : ℝ) : ℂ) / 2 := by
      calc
        (∫ b, Z b ^ 2 / 2
            ∂harperRankinTwoHeightCoin p hp a ha t s) =
            (∫ b, Z b ^ 2
              ∂harperRankinTwoHeightCoin p hp a ha t s) / 2 :=
          integral_div 2 _
        _ = _ := by rw [hsecondZ]
    dsimp only [Q]
    rw [integral_add Integrable.of_finite Integrable.of_finite,
      integral_add Integrable.of_finite Integrable.of_finite,
      hone, hmeanZ, hdiv]
    push_cast
    ring
  let R : Bool → ℂ := fun b ↦ Complex.exp (Z b) - Q b
  have hidentity :
      harperRankinTwoHeightProjectedPrimeCharacteristic
          p hp a ha t s v w -
          (1 - ((harperRankinTwoHeightProjectedPrimeVariance
            p hp a ha t s v w / 2 : ℝ) : ℂ)) =
        ∫ b, R b ∂harperRankinTwoHeightCoin p hp a ha t s := by
    rw [← hquad]
    unfold harperRankinTwoHeightProjectedPrimeCharacteristic
    change (∫ b, Complex.exp (Z b)
        ∂harperRankinTwoHeightCoin p hp a ha t s) -
      ∫ b, Q b ∂harperRankinTwoHeightCoin p hp a ha t s = _
    exact (integral_sub Integrable.of_finite Integrable.of_finite).symm
  rw [hidentity]
  calc
    ‖∫ b, R b ∂harperRankinTwoHeightCoin p hp a ha t s‖ ≤
        ∫ b, ‖R b‖ ∂harperRankinTwoHeightCoin p hp a ha t s :=
      norm_integral_le_integral_norm R
    _ ≤ ∫ _b : Bool, B ^ 3
        ∂harperRankinTwoHeightCoin p hp a ha t s := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro b
      simpa only [R] using hTaylor b
    _ = B ^ 3 := by
      rw [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- Mean drift, under the shifted pair law, of a Rankin increment centered
for the one-height law at `t`. -/
noncomputable def harperRankinTwoHeightCenteredPrimeDrift
    (p : ℕ) (a t s u : ℝ) : ℝ :=
  (harperRankinTwoHeightTiltBias p a t s -
      harperRankinTiltBias p a t) *
    harperRankinEulerRadius p a *
      Real.cos (u * Real.log (p : ℝ))

theorem integral_harperRankinCenteredLinearPrimeIncrement_twoHeightCoin
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s u : ℝ) :
    (∫ b, harperRankinCenteredLinearPrimeIncrement p a t u b
        ∂harperRankinTwoHeightCoin p hp a ha t s) =
      harperRankinTwoHeightCenteredPrimeDrift p a t s u := by
  rw [integral_harperRankinTwoHeightCoin]
  unfold harperRankinCenteredLinearPrimeIncrement
    harperRankinLinearPrimeIncrement
    harperRankinTwoHeightCenteredPrimeDrift
  have hsum := harperRankinTwoHeightCoinWeight_false_add_true hp ha t s
  unfold harperRankinTwoHeightTiltBias
  simp only [Problem520.cubeSign, Bool.false_eq_true, if_false, if_true]
  calc
    _ = (harperRankinTwoHeightCoinWeight p a t s true -
          harperRankinTwoHeightCoinWeight p a t s false) *
            harperRankinEulerRadius p a *
              Real.cos (u * Real.log (p : ℝ)) -
        (harperRankinTwoHeightCoinWeight p a t s false +
          harperRankinTwoHeightCoinWeight p a t s true) *
            harperRankinTiltBias p a t *
              harperRankinEulerRadius p a *
                Real.cos (u * Real.log (p : ℝ)) := by ring
    _ = _ := by rw [hsum]; ring

/-- Exact drift of a finite shifted prime block. -/
noncomputable def harperRankinTwoHeightCenteredBlockDrift
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t s u : ℝ) : ℝ :=
  ∑ p ∈ S, harperRankinTwoHeightCenteredPrimeDrift p.1 a t s u

theorem integral_harperRankinCenteredLinearPrimeBlockSum_twoHeightCube
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s u : ℝ) :
    (∫ eta, harperRankinCenteredLinearPrimeBlockSum y S a t u eta
        ∂harperRankinTwoHeightCubeLaw y a ha t s) =
      harperRankinTwoHeightCenteredBlockDrift y S a t s u := by
  unfold harperRankinCenteredLinearPrimeBlockSum
    harperRankinTwoHeightCenteredBlockDrift
  rw [integral_finset_sum S fun _ _ ↦ Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro p hpS
  rw [integral_harperRankinTwoHeightCube_eval,
    integral_harperRankinCenteredLinearPrimeIncrement_twoHeightCoin]

theorem harperRankinTwoHeightTiltBias_comm
    (p : ℕ) (a t s : ℝ) :
    harperRankinTwoHeightTiltBias p a t s =
      harperRankinTwoHeightTiltBias p a s t := by
  have hnormalizer :
      harperRankinTwoHeightPrimeNormalizer p a t s =
        harperRankinTwoHeightPrimeNormalizer p a s t := by
    unfold harperRankinTwoHeightPrimeNormalizer
    apply integral_congr_ae
    exact ae_of_all _ fun b ↦ by ring
  unfold harperRankinTwoHeightTiltBias harperRankinTwoHeightCoinWeight
  rw [hnormalizer]
  ring

#print axioms Erdos.Problem1144.abs_harperRankinTwoHeightPrimeFluctuation_le
#print axioms Erdos.Problem1144.integral_harperRankinTwoHeightPrimeFluctuation
#print axioms Erdos.Problem1144.harperRankinTwoHeightProjectedPrimeVariance_le_envelope
#print axioms Erdos.Problem1144.norm_harperRankinTwoHeightProjectedPrimeCharacteristic_sub_quadratic_le
#print axioms Erdos.Problem1144.integral_harperRankinCenteredLinearPrimeBlockSum_twoHeightCube

end

end Problem1144
end Erdos
