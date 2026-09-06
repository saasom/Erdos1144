import Erdos.Problem520.HarperTiltedLaw

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# The Rankin-shifted one-prime tilted law

The coefficient-energy localization uses the Euler line

`1/2 + a/2 + it`.

This file isolates the only genuinely new local object: the Euler radius
`p^(-(1+a)/2)`.  After normalization, the squared factor is still exactly an
affine density `1 + bias * epsilon`.  Thus the shifted law remains a product
of explicit biased Rademacher coins, with no approximation or correction
term.
-/

/-- Radius of the Euler factor on the Rankin-shifted line
`Re(s) = (1+a)/2`. -/
noncomputable def harperRankinEulerRadius (p : ℕ) (a : ℝ) : ℝ :=
  (p : ℝ) ^ (-(1 + a) / 2)

theorem harperRankinEulerRadius_nonneg (p : ℕ) (a : ℝ) :
    0 ≤ harperRankinEulerRadius p a :=
  Real.rpow_nonneg (Nat.cast_nonneg p) _

theorem harperRankinEulerRadius_pos {p : ℕ} (hp : 0 < p) (a : ℝ) :
    0 < harperRankinEulerRadius p a :=
  Real.rpow_pos_of_pos (by exact_mod_cast hp) _

/-- A nonnegative Rankin shift can only shrink the critical Euler radius. -/
theorem harperRankinEulerRadius_le_inv_sqrt
    {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a) :
    harperRankinEulerRadius p a ≤ (Real.sqrt (p : ℝ))⁻¹ := by
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hexp : -(1 + a) / 2 ≤ -(1 : ℝ) / 2 := by linarith
  calc
    harperRankinEulerRadius p a ≤ (p : ℝ) ^ (-(1 : ℝ) / 2) := by
      exact Real.rpow_le_rpow_of_exponent_le hpR hexp
    _ = (Real.sqrt (p : ℝ))⁻¹ := by
      rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
        Real.rpow_neg (Nat.cast_nonneg p), ← Real.sqrt_eq_rpow]

theorem harperRankinEulerRadius_zero
    (p : ℕ) :
    harperRankinEulerRadius p 0 = (Real.sqrt (p : ℝ))⁻¹ := by
  unfold harperRankinEulerRadius
  norm_num
  rw [Real.rpow_neg (Nat.cast_nonneg p), ← Real.sqrt_eq_rpow]

/-- Squared norm of one shifted Rademacher Euler factor. -/
noncomputable def harperRankinEulerFactor
    (omega : Problem520.Omega) (p : ℕ) (a t : ℝ) : ℝ :=
  (1 + Problem520.ε omega p * harperRankinEulerRadius p a *
      Real.cos (t * Real.log (p : ℝ))) ^ 2 +
    (Problem520.ε omega p * harperRankinEulerRadius p a *
      Real.sin (t * Real.log (p : ℝ))) ^ 2

theorem harperRankinEulerFactor_nonneg
    (omega : Problem520.Omega) (p : ℕ) (a t : ℝ) :
    0 ≤ harperRankinEulerFactor omega p a t := by
  unfold harperRankinEulerFactor
  positivity

/-- Exact affine expansion of one shifted squared Euler factor. -/
theorem harperRankinEulerFactor_eq
    (omega : Problem520.Omega) (p : ℕ) (a t : ℝ) :
    harperRankinEulerFactor omega p a t =
      1 + harperRankinEulerRadius p a ^ 2 +
        2 * Problem520.ε omega p * harperRankinEulerRadius p a *
          Real.cos (t * Real.log (p : ℝ)) := by
  have htrig := Real.sin_sq_add_cos_sq (t * Real.log (p : ℝ))
  have heps := Problem520.ε_sq omega p
  unfold harperRankinEulerFactor
  calc
    (1 + Problem520.ε omega p * harperRankinEulerRadius p a *
          Real.cos (t * Real.log (p : ℝ))) ^ 2 +
        (Problem520.ε omega p * harperRankinEulerRadius p a *
          Real.sin (t * Real.log (p : ℝ))) ^ 2 =
      1 + 2 * Problem520.ε omega p * harperRankinEulerRadius p a *
          Real.cos (t * Real.log (p : ℝ)) +
        Problem520.ε omega p ^ 2 * harperRankinEulerRadius p a ^ 2 *
          (Real.sin (t * Real.log (p : ℝ)) ^ 2 +
            Real.cos (t * Real.log (p : ℝ)) ^ 2) := by ring
    _ = _ := by rw [htrig, heps]; ring

/-- The one-prime first-moment normalizer. -/
noncomputable def harperRankinEulerNormalizer (p : ℕ) (a : ℝ) : ℝ :=
  1 + harperRankinEulerRadius p a ^ 2

theorem harperRankinEulerNormalizer_pos (p : ℕ) (a : ℝ) :
    0 < harperRankinEulerNormalizer p a := by
  unfold harperRankinEulerNormalizer
  positivity

theorem harperRankinEulerNormalizer_zero
    {p : ℕ} (hp : 0 < p) :
    harperRankinEulerNormalizer p 0 = 1 + (p : ℝ)⁻¹ := by
  have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
  rw [harperRankinEulerNormalizer, harperRankinEulerRadius_zero p]
  congr 1
  calc
    (Real.sqrt (p : ℝ))⁻¹ ^ 2 =
        (Real.sqrt (p : ℝ) ^ 2)⁻¹ := by rw [inv_pow]
    _ = (p : ℝ)⁻¹ := by rw [Real.sq_sqrt hpR]

/-- Exact sign bias after tilting by the shifted squared Euler factor. -/
noncomputable def harperRankinTiltBias (p : ℕ) (a t : ℝ) : ℝ :=
  2 * harperRankinEulerRadius p a *
      Real.cos (t * Real.log (p : ℝ)) /
    harperRankinEulerNormalizer p a

/-- Every shifted tilted coin has a legitimate Rademacher bias. -/
theorem abs_harperRankinTiltBias_le_one (p : ℕ) (a t : ℝ) :
    |harperRankinTiltBias p a t| ≤ 1 := by
  let r : ℝ := harperRankinEulerRadius p a
  have hr : 0 ≤ r := harperRankinEulerRadius_nonneg p a
  have hN : 0 < 1 + r ^ 2 := by positivity
  have hcos : |Real.cos (t * Real.log (p : ℝ))| ≤ 1 :=
    Real.abs_cos_le_one _
  have hnum : |2 * r * Real.cos (t * Real.log (p : ℝ))| ≤ 2 * r := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hr]
    nlinarith
  have hamgm : 2 * r ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  unfold harperRankinTiltBias harperRankinEulerNormalizer
  change |2 * r * Real.cos (t * Real.log (p : ℝ)) / (1 + r ^ 2)| ≤ 1
  rw [abs_div, abs_of_pos hN]
  exact (div_le_one hN).2 (hnum.trans hamgm)

/-- The shifted bias has the same elementary prime-scale envelope as the
critical bias. -/
theorem abs_harperRankinTiltBias_le_two_mul_inv_sqrt
    {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    |harperRankinTiltBias p a t| ≤
      2 * (Real.sqrt (p : ℝ))⁻¹ := by
  let r : ℝ := harperRankinEulerRadius p a
  have hr : 0 ≤ r := harperRankinEulerRadius_nonneg p a
  have hrle : r ≤ (Real.sqrt (p : ℝ))⁻¹ :=
    harperRankinEulerRadius_le_inv_sqrt hp ha
  have hN : 1 ≤ harperRankinEulerNormalizer p a := by
    unfold harperRankinEulerNormalizer
    exact le_add_of_nonneg_right (sq_nonneg r)
  have hNpos : 0 < harperRankinEulerNormalizer p a :=
    harperRankinEulerNormalizer_pos p a
  have hcos := Real.abs_cos_le_one (t * Real.log (p : ℝ))
  unfold harperRankinTiltBias
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg hr, abs_of_pos hNpos]
  calc
    2 * r * |Real.cos (t * Real.log (p : ℝ))| /
        harperRankinEulerNormalizer p a ≤ 2 * r / 1 := by
      apply (div_le_iff₀ hNpos).2
      have hnum :
          2 * r * |Real.cos (t * Real.log (p : ℝ))| ≤ 2 * r := by
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left hcos
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr))
      nlinarith
    _ ≤ 2 * (Real.sqrt (p : ℝ))⁻¹ := by nlinarith

theorem harperRankinTiltBias_sq_le_four_div
    {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    harperRankinTiltBias p a t ^ 2 ≤ 4 / (p : ℝ) := by
  have hbound := abs_harperRankinTiltBias_le_two_mul_inv_sqrt hp ha t
  have hsquare := pow_le_pow_left₀ (abs_nonneg _ ) hbound 2
  have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
  rw [sq_abs] at hsquare
  calc
    harperRankinTiltBias p a t ^ 2 ≤
        (2 * (Real.sqrt (p : ℝ))⁻¹) ^ 2 := hsquare
    _ = 4 / (p : ℝ) := by
      rw [mul_pow]
      have hinvSq : (Real.sqrt (p : ℝ))⁻¹ ^ 2 = (p : ℝ)⁻¹ := by
        calc
          (Real.sqrt (p : ℝ))⁻¹ ^ 2 =
              (Real.sqrt (p : ℝ) ^ 2)⁻¹ := by rw [inv_pow]
          _ = (p : ℝ)⁻¹ := by rw [Real.sq_sqrt hpR]
      rw [hinvSq]
      norm_num [div_eq_mul_inv]

theorem fifteen_sixteenths_le_one_sub_harperRankinTiltBias_sq
    {p : ℕ} (hp : 64 ≤ p) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    (15 / 16 : ℝ) ≤ 1 - harperRankinTiltBias p a t ^ 2 := by
  have hb := harperRankinTiltBias_sq_le_four_div (show 1 ≤ p by omega) ha t
  have hpR : (64 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hfour : 4 / (p : ℝ) ≤ (1 / 16 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (p : ℝ))).2
    nlinarith
  linarith

/-- The normalized local density is exactly affine in the sign. -/
theorem harperRankinEulerFactor_div_normalizer_eq
    (omega : Problem520.Omega) (p : ℕ) (a t : ℝ) :
    harperRankinEulerFactor omega p a t /
        harperRankinEulerNormalizer p a =
      1 + harperRankinTiltBias p a t * Problem520.ε omega p := by
  rw [harperRankinEulerFactor_eq]
  unfold harperRankinTiltBias harperRankinEulerNormalizer
  field_simp [ne_of_gt (harperRankinEulerNormalizer_pos p a)]

/-- The shifted factor evaluated at one Boolean sign. -/
noncomputable def harperRankinCoordinateFactor
    (p : ℕ) (a t : ℝ) (b : Bool) : ℝ :=
  harperRankinEulerFactor (fun _ ↦ b) p a t

/-- Probability weight of one sign under the shifted tilt. -/
noncomputable def harperRankinTiltedCoinWeight
    (p : ℕ) (a t : ℝ) (b : Bool) : ℝ :=
  harperRankinCoordinateFactor p a t b /
    (2 * harperRankinEulerNormalizer p a)

theorem harperRankinTiltedCoinWeight_nonneg
    (p : ℕ) (a t : ℝ) (b : Bool) :
    0 ≤ harperRankinTiltedCoinWeight p a t b := by
  unfold harperRankinTiltedCoinWeight harperRankinCoordinateFactor
  exact div_nonneg
    (harperRankinEulerFactor_nonneg (fun _ ↦ b) p a t)
    (mul_nonneg (by norm_num) (harperRankinEulerNormalizer_pos p a).le)

theorem harperRankinCoordinateFactor_false_add_true
    (p : ℕ) (a t : ℝ) :
    harperRankinCoordinateFactor p a t false +
        harperRankinCoordinateFactor p a t true =
      2 * harperRankinEulerNormalizer p a := by
  unfold harperRankinCoordinateFactor
  rw [harperRankinEulerFactor_eq, harperRankinEulerFactor_eq]
  simp [Problem520.ε, harperRankinEulerNormalizer]
  ring

theorem harperRankinTiltedCoinWeight_false_add_true
    (p : ℕ) (a t : ℝ) :
    harperRankinTiltedCoinWeight p a t false +
        harperRankinTiltedCoinWeight p a t true = 1 := by
  unfold harperRankinTiltedCoinWeight
  rw [← add_div, harperRankinCoordinateFactor_false_add_true]
  field_simp [ne_of_gt (harperRankinEulerNormalizer_pos p a)]

theorem harperRankinTiltedCoinWeight_eq_affine
    (p : ℕ) (a t : ℝ) (b : Bool) :
    harperRankinTiltedCoinWeight p a t b =
      (1 + harperRankinTiltBias p a t * Problem520.cubeSign b) / 2 := by
  unfold harperRankinTiltedCoinWeight harperRankinCoordinateFactor
  have hnormalized :=
    harperRankinEulerFactor_div_normalizer_eq (fun _ ↦ b) p a t
  have heps : Problem520.ε (fun _ ↦ b) p = Problem520.cubeSign b := by
    cases b <;> rfl
  rw [heps] at hnormalized
  calc
    harperRankinEulerFactor (fun _ ↦ b) p a t /
        (2 * harperRankinEulerNormalizer p a) =
      (harperRankinEulerFactor (fun _ ↦ b) p a t /
        harperRankinEulerNormalizer p a) / 2 := by ring
    _ = _ := by rw [hnormalized]

/-- NNReal form of the shifted tilted mass. -/
noncomputable def harperRankinTiltedCoinWeightNNReal
    (p : ℕ) (a t : ℝ) (b : Bool) : ℝ≥0 :=
  ⟨harperRankinTiltedCoinWeight p a t b,
    harperRankinTiltedCoinWeight_nonneg p a t b⟩

@[simp] theorem coe_harperRankinTiltedCoinWeightNNReal
    (p : ℕ) (a t : ℝ) (b : Bool) :
    (harperRankinTiltedCoinWeightNNReal p a t b : ℝ) =
      harperRankinTiltedCoinWeight p a t b := rfl

theorem harperRankinTiltedCoinWeightNNReal_false_add_true
    (p : ℕ) (a t : ℝ) :
    harperRankinTiltedCoinWeightNNReal p a t false +
        harperRankinTiltedCoinWeightNNReal p a t true = 1 := by
  ext
  exact harperRankinTiltedCoinWeight_false_add_true p a t

/-- The explicit shifted one-prime tilted probability law. -/
noncomputable def harperRankinTiltedCoin
    (p : ℕ) (a t : ℝ) : Measure Bool :=
  (harperRankinTiltedCoinWeightNNReal p a t false : ℝ≥0∞) •
      Measure.dirac false +
    (harperRankinTiltedCoinWeightNNReal p a t true : ℝ≥0∞) •
      Measure.dirac true

instance harperRankinTiltedCoin_isProbabilityMeasure
    (p : ℕ) (a t : ℝ) :
    IsProbabilityMeasure (harperRankinTiltedCoin p a t) where
  measure_univ := by
    simp [harperRankinTiltedCoin]
    rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one]
    rw [← ENNReal.coe_add,
      harperRankinTiltedCoinWeightNNReal_false_add_true]
    simp

@[simp] theorem harperRankinTiltedCoin_apply_singleton
    (p : ℕ) (a t : ℝ) (b : Bool) :
    harperRankinTiltedCoin p a t {b} =
      (harperRankinTiltedCoinWeightNNReal p a t b : ℝ≥0∞) := by
  cases b <;> simp [harperRankinTiltedCoin] <;>
    rw [ENNReal.smul_def, smul_eq_mul, mul_one]

@[simp] theorem harperRankinTiltedCoin_real_singleton
    (p : ℕ) (a t : ℝ) (b : Bool) :
    (harperRankinTiltedCoin p a t).real {b} =
      harperRankinTiltedCoinWeight p a t b := by
  rw [Measure.real, harperRankinTiltedCoin_apply_singleton]
  simp

theorem integral_harperRankinTiltedCoin
    (p : ℕ) (a t : ℝ) (g : Bool → ℝ) :
    (∫ b, g b ∂harperRankinTiltedCoin p a t) =
      harperRankinTiltedCoinWeight p a t false * g false +
        harperRankinTiltedCoinWeight p a t true * g true := by
  let wf : ℝ≥0∞ := harperRankinTiltedCoinWeightNNReal p a t false
  let wt : ℝ≥0∞ := harperRankinTiltedCoinWeightNNReal p a t true
  have hgfalse : Integrable g (wf • Measure.dirac false) :=
    (integrable_dirac (f := g) (by simp)).smul_measure (by simp [wf])
  have hgtrue : Integrable g (wt • Measure.dirac true) :=
    (integrable_dirac (f := g) (by simp)).smul_measure (by simp [wt])
  rw [show harperRankinTiltedCoin p a t =
      wf • Measure.dirac false + wt • Measure.dirac true by rfl,
    integral_add_measure hgfalse hgtrue,
    integral_smul_measure, integral_smul_measure]
  simp [wf, wt, smul_eq_mul]

/-- The mean sign under the shifted tilted coin is exactly its bias. -/
theorem integral_cubeSign_harperRankinTiltedCoin
    (p : ℕ) (a t : ℝ) :
    (∫ b, Problem520.cubeSign b ∂harperRankinTiltedCoin p a t) =
      harperRankinTiltBias p a t := by
  rw [integral_harperRankinTiltedCoin]
  rw [harperRankinTiltedCoinWeight_eq_affine,
    harperRankinTiltedCoinWeight_eq_affine]
  norm_num [Problem520.cubeSign]
  ring

/-- The exact centered sign variance under the shifted coin. -/
theorem integral_cubeSign_sub_rankinBias_sq
    (p : ℕ) (a t : ℝ) :
    (∫ b, (Problem520.cubeSign b - harperRankinTiltBias p a t) ^ 2
        ∂harperRankinTiltedCoin p a t) =
      1 - harperRankinTiltBias p a t ^ 2 := by
  rw [integral_harperRankinTiltedCoin]
  rw [harperRankinTiltedCoinWeight_eq_affine,
    harperRankinTiltedCoinWeight_eq_affine]
  norm_num [Problem520.cubeSign]
  ring

/-! ## Shifted linear increments and exact centered moments -/

/-- First-order logarithmic Euler increment at Rankin shift `a`. -/
noncomputable def harperRankinLinearPrimeIncrement
    (p : ℕ) (a u : ℝ) (b : Bool) : ℝ :=
  Problem520.cubeSign b * harperRankinEulerRadius p a *
    Real.cos (u * Real.log (p : ℝ))

/-- The shifted linear increment centered under its own tilted coin. -/
noncomputable def harperRankinCenteredLinearPrimeIncrement
    (p : ℕ) (a t u : ℝ) (b : Bool) : ℝ :=
  harperRankinLinearPrimeIncrement p a u b -
    harperRankinTiltBias p a t * harperRankinEulerRadius p a *
      Real.cos (u * Real.log (p : ℝ))

/-- Exact centered variance of one shifted coordinate. -/
noncomputable def harperRankinCenteredLinearPrimeVariance
    (p : ℕ) (a t u : ℝ) : ℝ :=
  (harperRankinEulerRadius p a *
      Real.cos (u * Real.log (p : ℝ))) ^ 2 *
    (1 - harperRankinTiltBias p a t ^ 2)

theorem integral_harperRankinLinearPrimeIncrement
    (p : ℕ) (a t u : ℝ) :
    (∫ b, harperRankinLinearPrimeIncrement p a u b
        ∂harperRankinTiltedCoin p a t) =
      harperRankinTiltBias p a t * harperRankinEulerRadius p a *
        Real.cos (u * Real.log (p : ℝ)) := by
  let c : ℝ := harperRankinEulerRadius p a *
    Real.cos (u * Real.log (p : ℝ))
  have hfun : (fun b ↦ harperRankinLinearPrimeIncrement p a u b) =
      fun b ↦ c * Problem520.cubeSign b := by
    funext b
    unfold harperRankinLinearPrimeIncrement
    dsimp only [c]
    ring
  rw [hfun, integral_const_mul,
    integral_cubeSign_harperRankinTiltedCoin]
  dsimp only [c]
  ring

theorem integral_harperRankinCenteredLinearPrimeIncrement
    (p : ℕ) (a t u : ℝ) :
    (∫ b, harperRankinCenteredLinearPrimeIncrement p a t u b
        ∂harperRankinTiltedCoin p a t) = 0 := by
  unfold harperRankinCenteredLinearPrimeIncrement
  rw [integral_sub Integrable.of_finite Integrable.of_finite,
    integral_harperRankinLinearPrimeIncrement, integral_const,
    probReal_univ, one_smul, sub_self]

theorem integral_harperRankinCenteredLinearPrimeIncrement_sq
    (p : ℕ) (a t u : ℝ) :
    (∫ b, harperRankinCenteredLinearPrimeIncrement p a t u b ^ 2
        ∂harperRankinTiltedCoin p a t) =
      harperRankinCenteredLinearPrimeVariance p a t u := by
  let c : ℝ := harperRankinEulerRadius p a *
    Real.cos (u * Real.log (p : ℝ))
  have hpoint (b : Bool) :
      harperRankinCenteredLinearPrimeIncrement p a t u b =
        c * (Problem520.cubeSign b - harperRankinTiltBias p a t) := by
    unfold harperRankinCenteredLinearPrimeIncrement
      harperRankinLinearPrimeIncrement
    dsimp only [c]
    ring
  simp_rw [hpoint, mul_pow]
  rw [integral_const_mul, integral_cubeSign_sub_rankinBias_sq]
  rfl

/-- The shifted centered coordinate has no larger pointwise envelope than
the original critical coordinate. -/
theorem abs_harperRankinCenteredLinearPrimeIncrement_le
    {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a)
    (t u : ℝ) (b : Bool) :
    |harperRankinCenteredLinearPrimeIncrement p a t u b| ≤
      2 * (Real.sqrt (p : ℝ))⁻¹ := by
  let r : ℝ := harperRankinEulerRadius p a
  let c : ℝ := Real.cos (u * Real.log (p : ℝ))
  let bias : ℝ := harperRankinTiltBias p a t
  have hr : 0 ≤ r := harperRankinEulerRadius_nonneg p a
  have hrle : r ≤ (Real.sqrt (p : ℝ))⁻¹ :=
    harperRankinEulerRadius_le_inv_sqrt hp ha
  have hc : |c| ≤ 1 := Real.abs_cos_le_one _
  have hbias : |bias| ≤ 1 := abs_harperRankinTiltBias_le_one p a t
  have hsign : |Problem520.cubeSign b| = 1 := by
    cases b <;> norm_num [Problem520.cubeSign]
  rw [show harperRankinCenteredLinearPrimeIncrement p a t u b =
      r * c * (Problem520.cubeSign b - bias) by
        unfold harperRankinCenteredLinearPrimeIncrement
          harperRankinLinearPrimeIncrement
        dsimp only [r, c, bias]
        ring,
    abs_mul, abs_mul, abs_of_nonneg hr]
  have hdiff : |Problem520.cubeSign b - bias| ≤ 2 := by
    calc
      |Problem520.cubeSign b - bias| ≤
          |Problem520.cubeSign b| + |bias| := abs_sub _ _
      _ ≤ 2 := by rw [hsign]; linarith
  calc
    r * |c| * |Problem520.cubeSign b - bias| ≤ r * 1 * 2 := by
      gcongr
    _ ≤ 2 * (Real.sqrt (p : ℝ))⁻¹ := by nlinarith

/-- Consequently the shifted one-coordinate cubic budget is identical to
the already compiled critical-line budget. -/
theorem integral_abs_harperRankinCenteredLinearPrimeIncrement_pow_three_le
    {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a) (t u : ℝ) :
    (∫ b, |harperRankinCenteredLinearPrimeIncrement p a t u b| ^ 3
        ∂harperRankinTiltedCoin p a t) ≤
      8 * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  calc
    (∫ b, |harperRankinCenteredLinearPrimeIncrement p a t u b| ^ 3
        ∂harperRankinTiltedCoin p a t) ≤
      ∫ _b : Bool, (2 * (Real.sqrt (p : ℝ))⁻¹) ^ 3
        ∂harperRankinTiltedCoin p a t := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro b
      exact pow_le_pow_left₀ (abs_nonneg _)
        (abs_harperRankinCenteredLinearPrimeIncrement_le hp ha t u b) 3
    _ = 8 * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
      rw [integral_const, probReal_univ, one_smul]
      ring

/-! ## Finite shifted product law -/

/-- Product of the independently Rankin-tilted prime-coordinate laws. -/
noncomputable def harperRankinTiltedCubeLaw
    (y : ℕ) (a t : ℝ) : Measure (Problem520.HarperPrimeCube y) :=
  Measure.pi fun p : Problem520.HarperPrimeIndex y ↦
    harperRankinTiltedCoin p.1 a t

instance harperRankinTiltedCubeLaw_isProbabilityMeasure
    (y : ℕ) (a t : ℝ) :
    IsProbabilityMeasure (harperRankinTiltedCubeLaw y a t) := by
  unfold harperRankinTiltedCubeLaw
  infer_instance

/-- Shifted Euler density on the finite prime cube. -/
noncomputable def harperRankinCubeDensity
    (y : ℕ) (a t : ℝ) (eta : Problem520.HarperPrimeCube y) : ℝ :=
  ∏ p : Problem520.HarperPrimeIndex y,
    harperRankinCoordinateFactor p.1 a t (eta p)

/-- Product of the shifted one-prime normalizers. -/
noncomputable def harperRankinEnergyNormalizer (y : ℕ) (a : ℝ) : ℝ :=
  ∏ p : Problem520.HarperPrimeIndex y,
    harperRankinEulerNormalizer p.1 a

theorem harperRankinEnergyNormalizer_pos (y : ℕ) (a : ℝ) :
    0 < harperRankinEnergyNormalizer y a := by
  unfold harperRankinEnergyNormalizer
  exact Finset.prod_pos fun p _ ↦ harperRankinEulerNormalizer_pos p.1 a

/-- Exactly normalized shifted density on the finite cube. -/
noncomputable def normalizedHarperRankinCubeDensity
    (y : ℕ) (a t : ℝ) (eta : Problem520.HarperPrimeCube y) : ℝ :=
  harperRankinCubeDensity y a t eta / harperRankinEnergyNormalizer y a

theorem harperRankinTiltedCoinWeight_eq_normalized_mul_half
    (p : ℕ) (a t : ℝ) (b : Bool) :
    harperRankinTiltedCoinWeight p a t b =
      (harperRankinCoordinateFactor p a t b /
        harperRankinEulerNormalizer p a) * (1 / 2 : ℝ) := by
  unfold harperRankinTiltedCoinWeight
  ring

theorem prod_harperRankinTiltedCoinWeight_eq
    (y : ℕ) (a t : ℝ) (eta : Problem520.HarperPrimeCube y) :
    (∏ p : Problem520.HarperPrimeIndex y,
        harperRankinTiltedCoinWeight p.1 a t (eta p)) =
      normalizedHarperRankinCubeDensity y a t eta *
        ∏ _p : Problem520.HarperPrimeIndex y, (1 / 2 : ℝ) := by
  simp_rw [harperRankinTiltedCoinWeight_eq_normalized_mul_half]
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib]
  rfl

@[simp] theorem harperRankinTiltedCubeLaw_real_singleton
    (y : ℕ) (a t : ℝ) (eta : Problem520.HarperPrimeCube y) :
    (harperRankinTiltedCubeLaw y a t).real {eta} =
      ∏ p : Problem520.HarperPrimeIndex y,
        harperRankinTiltedCoinWeight p.1 a t (eta p) := by
  rw [Measure.real, harperRankinTiltedCubeLaw, Measure.pi_singleton,
    ENNReal.toReal_prod]
  simp

/-- Exact point-mass Radon--Nikodym identity for the shifted product. -/
theorem harperRankinTiltedCubeLaw_real_singleton_eq
    (y : ℕ) (a t : ℝ) (eta : Problem520.HarperPrimeCube y) :
    (harperRankinTiltedCubeLaw y a t).real {eta} =
      normalizedHarperRankinCubeDensity y a t eta *
        (Measure.pi (fun _ : Problem520.HarperPrimeIndex y ↦
          Problem520.coin)).real {eta} := by
  rw [harperRankinTiltedCubeLaw_real_singleton,
    Problem520.fairHarperCubeLaw_real_singleton,
    prod_harperRankinTiltedCoinWeight_eq]

/-- Exact shifted change of measure from the fair finite cube. -/
theorem integral_harperRankinTiltedCubeLaw_eq
    (y : ℕ) (a t : ℝ) (g : Problem520.HarperPrimeCube y → ℝ) :
    (∫ eta, g eta ∂harperRankinTiltedCubeLaw y a t) =
      ∫ eta, normalizedHarperRankinCubeDensity y a t eta * g eta
        ∂Measure.pi (fun _ : Problem520.HarperPrimeIndex y ↦
          Problem520.coin) := by
  rw [integral_fintype (Integrable.of_finite :
      Integrable g (harperRankinTiltedCubeLaw y a t)),
    integral_fintype (Integrable.of_finite :
      Integrable (fun eta ↦ normalizedHarperRankinCubeDensity y a t eta * g eta)
        (Measure.pi (fun _ : Problem520.HarperPrimeIndex y ↦
          Problem520.coin)))]
  apply Finset.sum_congr rfl
  intro eta heta
  rw [harperRankinTiltedCubeLaw_real_singleton_eq]
  simp only [smul_eq_mul]
  ring

/-- Shifted tilted coordinates are independent. -/
theorem iIndepFun_harperRankinTiltedCube_coordinates
    (y : ℕ) (a t : ℝ) :
    iIndepFun
      (fun p : Problem520.HarperPrimeIndex y ↦
        fun eta : Problem520.HarperPrimeCube y ↦ eta p)
      (harperRankinTiltedCubeLaw y a t) := by
  unfold harperRankinTiltedCubeLaw
  exact iIndepFun_pi
    (X := fun _ : Problem520.HarperPrimeIndex y ↦ id)
    (fun _ ↦ aemeasurable_id)

/-- Every coordinate has its explicit shifted tilted coin as marginal. -/
theorem measurePreserving_harperRankinTiltedCube_eval
    (y : ℕ) (a t : ℝ) (p : Problem520.HarperPrimeIndex y) :
    MeasurePreserving
      (fun eta : Problem520.HarperPrimeCube y ↦ eta p)
      (harperRankinTiltedCubeLaw y a t)
      (harperRankinTiltedCoin p.1 a t) := by
  unfold harperRankinTiltedCubeLaw
  exact measurePreserving_eval
    (fun q : Problem520.HarperPrimeIndex y ↦
      harperRankinTiltedCoin q.1 a t) p

/-- Products of shifted one-coordinate observables factor exactly. -/
theorem integral_prod_harperRankinTiltedCubeLaw
    (y : ℕ) (a t : ℝ)
    (g : Problem520.HarperPrimeIndex y → Bool → ℝ) :
    (∫ eta, ∏ p : Problem520.HarperPrimeIndex y, g p (eta p)
        ∂harperRankinTiltedCubeLaw y a t) =
      ∏ p : Problem520.HarperPrimeIndex y,
        ∫ b, g p b ∂harperRankinTiltedCoin p.1 a t := by
  let X : Problem520.HarperPrimeIndex y →
      Problem520.HarperPrimeCube y → ℝ := fun p eta ↦ g p (eta p)
  have hbase := iIndepFun_harperRankinTiltedCube_coordinates y a t
  have hX : iIndepFun X (harperRankinTiltedCubeLaw y a t) := by
    have hcomp := hbase.comp g (fun _ ↦ measurable_of_finite _)
    simpa only [X, Function.comp_apply] using hcomp
  have hprod := hX.integral_fun_prod_eq_prod_integral
    (fun p ↦ (measurable_of_finite (X p)).aestronglyMeasurable)
  calc
    (∫ eta, ∏ p : Problem520.HarperPrimeIndex y, g p (eta p)
        ∂harperRankinTiltedCubeLaw y a t) =
        ∏ p : Problem520.HarperPrimeIndex y,
          ∫ eta, g p (eta p) ∂harperRankinTiltedCubeLaw y a t := by
      simpa only [X] using hprod
    _ = ∏ p : Problem520.HarperPrimeIndex y,
        ∫ b, g p b ∂harperRankinTiltedCoin p.1 a t := by
      apply Finset.prod_congr rfl
      intro p hp
      have hmp := measurePreserving_harperRankinTiltedCube_eval y a t p
      calc
        (∫ eta, g p (eta p) ∂harperRankinTiltedCubeLaw y a t) =
            ∫ b, g p b ∂Measure.map
              (fun eta : Problem520.HarperPrimeCube y ↦ eta p)
              (harperRankinTiltedCubeLaw y a t) := by
          symm
          exact integral_map hmp.measurable.aemeasurable
            (measurable_of_finite (g p)).aestronglyMeasurable
        _ = ∫ b, g p b ∂harperRankinTiltedCoin p.1 a t := by
          rw [hmp.map_eq]

end

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.harperRankinEulerFactor_div_normalizer_eq
#print axioms Erdos.Problem1144.abs_harperRankinTiltBias_le_two_mul_inv_sqrt
#print axioms Erdos.Problem1144.harperRankinTiltBias_sq_le_four_div
#print axioms Erdos.Problem1144.fifteen_sixteenths_le_one_sub_harperRankinTiltBias_sq
#print axioms Erdos.Problem1144.harperRankinTiltedCoinWeight_eq_affine
#print axioms Erdos.Problem1144.integral_cubeSign_harperRankinTiltedCoin
#print axioms Erdos.Problem1144.integral_cubeSign_sub_rankinBias_sq
#print axioms Erdos.Problem1144.integral_harperRankinCenteredLinearPrimeIncrement_sq
#print axioms Erdos.Problem1144.abs_harperRankinCenteredLinearPrimeIncrement_le
#print axioms Erdos.Problem1144.integral_abs_harperRankinCenteredLinearPrimeIncrement_pow_three_le
#print axioms Erdos.Problem1144.harperRankinTiltedCubeLaw_real_singleton_eq
#print axioms Erdos.Problem1144.integral_harperRankinTiltedCubeLaw_eq
#print axioms Erdos.Problem1144.iIndepFun_harperRankinTiltedCube_coordinates
