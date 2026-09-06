import Erdos.Problem1144.HarperRankinEulerProduct
import Erdos.Problem520.HarperFairEulerProduct
import Erdos.Problem520.MertensProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

noncomputable section

/-!
# The shifted small-prime Euler ratio

This proves the near-real-axis cancellation used in Atherfold, §6.2. The
squared ratio is the quotient of the existing literal shifted Euler densities.
The shift parameter `a` means the real line `(1+a)/2`.

The result is uniform for every nonnegative shift. It is only the ratio
estimate; it does not assert the weighted almost-sure bound or the separate
small-height fractional moment of the unnormalized Euler product.
-/

private theorem shifted_radius_sq_le_inv {p : ℕ} (hp : p.Prime)
    {a : ℝ} (ha : 0 ≤ a) :
    harperRankinEulerRadius p a ^ 2 ≤ (p : ℝ)⁻¹ := by
  have h := pow_le_pow_left₀ (harperRankinEulerRadius_nonneg p a)
    (harperRankinEulerRadius_le_inv_sqrt hp.one_le ha) 2
  calc
    _ ≤ (Real.sqrt (p : ℝ))⁻¹ ^ 2 := h
    _ = _ := by rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg p)]

private theorem shifted_radius_sq_le_half {p : ℕ} (hp : p.Prime)
    {a : ℝ} (ha : 0 ≤ a) :
    harperRankinEulerRadius p a ^ 2 ≤ 1 / 2 := by
  refine (shifted_radius_sq_le_inv hp ha).trans ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2

private theorem scalar_euler_ratio_mean {r c : ℝ}
    (hr : 0 ≤ r) (hr2 : r ^ 2 ≤ 1 / 2) :
    ((1 + r ^ 2 - 2 * r * c) / (1 + r ^ 2 - 2 * r) +
      (1 + r ^ 2 + 2 * r * c) / (1 + r ^ 2 + 2 * r)) / 2 =
      1 + 4 * r ^ 2 * (1 - c) / (1 - r ^ 2) ^ 2 := by
  have hr1 : r < 1 := by nlinarith
  have hm : 1 + r ^ 2 - 2 * r ≠ 0 := by nlinarith [sq_pos_of_pos (by linarith : 0 < 1 - r)]
  have hp : 1 + r ^ 2 + 2 * r ≠ 0 := by positivity
  have hd : 1 - r ^ 2 ≠ 0 := by linarith
  have hprod : (1 + r ^ 2 - 2 * r) * (1 + r ^ 2 + 2 * r) =
      (1 - r ^ 2) ^ 2 := by ring
  rw [div_add_div _ _ hm hp, hprod]
  field_simp [hd]
  ring

/-- Exact one-prime cancellation, including the nonnegative Rankin shift. -/
theorem candidate_integral_shifted_euler_ratio_prime {p : ℕ}
    (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    (∫ b, harperRankinCoordinateFactor p a t b /
        harperRankinCoordinateFactor p a 0 b ∂Problem520.coin) =
      1 + 4 * harperRankinEulerRadius p a ^ 2 *
        (1 - Real.cos (t * Real.log (p : ℝ))) /
          (1 - harperRankinEulerRadius p a ^ 2) ^ 2 := by
  rw [Problem520.integral_coin_bool]
  simp only [harperRankinCoordinateFactor, harperRankinEulerFactor_eq,
    Problem520.ε, Bool.false_eq_true, if_false, if_true, zero_mul,
    Real.cos_zero, mul_one]
  convert scalar_euler_ratio_mean
    (harperRankinEulerRadius_nonneg p a) (shifted_radius_sq_le_half hp ha)
    using 1
  ring

/-- The one-prime ratio loss is quadratic in the vertical displacement. -/
theorem candidate_integral_shifted_euler_ratio_prime_le_exp {p : ℕ}
    (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    (∫ b, harperRankinCoordinateFactor p a t b /
        harperRankinCoordinateFactor p a 0 b ∂Problem520.coin) ≤
      Real.exp (8 * t ^ 2 * Real.log (p : ℝ) ^ 2 / (p : ℝ)) := by
  rw [candidate_integral_shifted_euler_ratio_prime hp ha]
  let r := harperRankinEulerRadius p a
  let θ := t * Real.log (p : ℝ)
  have hr2 : r ^ 2 ≤ 1 / 2 := shifted_radius_sq_le_half hp ha
  have hrinv : r ^ 2 ≤ (p : ℝ)⁻¹ := shifted_radius_sq_le_inv hp ha
  have hd : 1 / 4 ≤ (1 - r ^ 2) ^ 2 := by nlinarith [sq_nonneg r]
  have hdpos : 0 < (1 - r ^ 2) ^ 2 := by linarith
  have hc0 : 0 ≤ 1 - Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
  have hc : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
  have hnum : 4 * r ^ 2 * (1 - Real.cos θ) ≤
      8 * (p : ℝ)⁻¹ * θ ^ 2 * (1 - r ^ 2) ^ 2 := by
    calc
      4 * r ^ 2 * (1 - Real.cos θ) ≤ 2 * r ^ 2 * θ ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hc)]
      _ ≤ 2 * (p : ℝ)⁻¹ * θ ^ 2 := by gcongr
      _ ≤ 8 * (p : ℝ)⁻¹ * θ ^ 2 * (1 - r ^ 2) ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))
          (sq_nonneg θ)) (sub_nonneg.mpr hd)]
  have hratio : 4 * r ^ 2 * (1 - Real.cos θ) / (1 - r ^ 2) ^ 2 ≤
      8 * t ^ 2 * Real.log (p : ℝ) ^ 2 / (p : ℝ) := by
    calc
      _ ≤ 8 * (p : ℝ)⁻¹ * θ ^ 2 := (div_le_iff₀ hdpos).2 hnum
      _ = _ := by dsimp [θ]; ring
  calc
    _ ≤ 1 + (8 * t ^ 2 * Real.log (p : ℝ) ^ 2 / (p : ℝ)) := by
      simpa only [add_comm] using add_le_add_left hratio 1
    _ ≤ _ := by
      simpa only [add_comm] using
        (Real.add_one_le_exp (8 * t ^ 2 * Real.log (p : ℝ) ^ 2 / (p : ℝ)))

/-- Literal quotient of the finite shifted squared Euler products. -/
def candidateShiftedEulerRatio (y : ℕ) (a t : ℝ)
    (ω : Problem520.Omega) : ℝ :=
  harperRankinEulerDensity y a ω t / harperRankinEulerDensity y a ω 0

/-- The finite fair law gives an exact product for the literal Euler ratio. -/
theorem candidate_integral_shifted_euler_ratio (y : ℕ)
    {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    (∫ ω, candidateShiftedEulerRatio y a t ω ∂Problem520.μ) =
      ∏ p ∈ (y + 1).primesBelow,
        (1 + 4 * harperRankinEulerRadius p a ^ 2 *
          (1 - Real.cos (t * Real.log (p : ℝ))) /
            (1 - harperRankinEulerRadius p a ^ 2) ^ 2) := by
  let g : Problem520.HarperPrimeCube y → ℝ := fun η ↦
    ∏ p : Problem520.HarperPrimeIndex y,
      harperRankinCoordinateFactor p.1 a t (η p) /
        harperRankinCoordinateFactor p.1 a 0 (η p)
  have hg (ω : Problem520.Omega) :
      g (Problem520.harperPrimeRestriction y ω) =
        candidateShiftedEulerRatio y a t ω := by
    dsimp [g]
    rw [Finset.prod_div_distrib]
    change harperRankinCubeDensity y a t (Problem520.harperPrimeRestriction y ω) /
      harperRankinCubeDensity y a 0 (Problem520.harperPrimeRestriction y ω) = _
    rw [harperRankinCubeDensity_harperPrimeRestriction,
      harperRankinCubeDensity_harperPrimeRestriction]
    rfl
  rw [show candidateShiftedEulerRatio y a t =
      fun ω ↦ g (Problem520.harperPrimeRestriction y ω) from funext fun ω ↦ (hg ω).symm,
    Problem520.integral_comp_harperPrimeRestriction_mu]
  have hf := Problem520.integral_prod_harperFairCubeLaw y
    (fun p b ↦ harperRankinCoordinateFactor p.1 a t b /
      harperRankinCoordinateFactor p.1 a 0 b)
  change (∫ η, g η ∂Problem520.harperFairCubeLaw y) = _
  rw [show g = _ from rfl, hf]
  rw [← Finset.prod_coe_sort ((y + 1).primesBelow)
    (fun p ↦ 1 + 4 * harperRankinEulerRadius p a ^ 2 *
      (1 - Real.cos (t * Real.log (p : ℝ))) /
        (1 - harperRankinEulerRadius p a ^ 2) ^ 2)]
  apply Finset.prod_congr rfl
  intro p _
  exact candidate_integral_shifted_euler_ratio_prime
    (Nat.mem_primesBelow.mp p.2).2 ha t

/-- Exponential bound with its explicit prime sum, uniform in the shift. -/
theorem candidate_integral_shifted_euler_ratio_le_exp (y : ℕ)
    {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    (∫ ω, candidateShiftedEulerRatio y a t ω ∂Problem520.μ) ≤
      Real.exp (8 * t ^ 2 *
        ∑ p ∈ (y + 1).primesBelow, Real.log (p : ℝ) ^ 2 / (p : ℝ)) := by
  rw [candidate_integral_shifted_euler_ratio y ha]
  calc
    _ ≤ ∏ p ∈ (y + 1).primesBelow,
        Real.exp (8 * t ^ 2 * Real.log (p : ℝ) ^ 2 / (p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hc : 0 ≤ 1 - Real.cos (t * Real.log (p : ℝ)) :=
          sub_nonneg.mpr (Real.cos_le_one _)
        positivity
      · intro p hp
        rw [← candidate_integral_shifted_euler_ratio_prime (Nat.mem_primesBelow.mp hp).2 ha]
        exact candidate_integral_shifted_euler_ratio_prime_le_exp
          (Nat.mem_primesBelow.mp hp).2 ha t
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring

/-- The prime logarithmic square sum has the correct quadratic logarithmic scale. -/
theorem candidate_sum_prime_log_sq_div_le {y : ℕ} (hy : 1 ≤ y) :
    (∑ p ∈ (y + 1).primesBelow, Real.log (p : ℝ) ^ 2 / (p : ℝ)) ≤
      Real.log (y : ℝ) * (Real.log (y : ℝ) + (Real.log 4 + 4)) := by
  have hly : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (by exact_mod_cast hy)
  calc
    _ ≤ Real.log (y : ℝ) * Problem520.weightedPrimeReciprocalPrefix y := by
      unfold Problem520.weightedPrimeReciprocalPrefix
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hpP := (Nat.mem_primesBelow.mp hp).2
      have hpy : (p : ℝ) ≤ y := by exact_mod_cast (Nat.lt_succ_iff.mp (Nat.mem_primesBelow.mp hp).1)
      have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpP.one_le)
      have hlog := Real.log_le_log (by exact_mod_cast hpP.pos) hpy
      calc
        Real.log (p : ℝ) ^ 2 / (p : ℝ) = Real.log (p : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by ring
        _ ≤ Real.log (y : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) :=
          mul_le_mul_of_nonneg_right hlog (div_nonneg hlp (Nat.cast_nonneg p))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Problem520.weightedPrimeReciprocalPrefix_le_log_add_const hy) hly

/-- Uniform near-real-axis ratio bound, with one absolute constant. -/
theorem candidate_integral_shifted_euler_ratio_local_le {y : ℕ}
    (hy : 2 ≤ y) {a t : ℝ} (ha : 0 ≤ a)
    (ht : |t| ≤ (Real.log (y : ℝ))⁻¹) :
    (∫ ω, candidateShiftedEulerRatio y a t ω ∂Problem520.μ) ≤
      Real.exp (8 * (1 + (Real.log 4 + 4) / Real.log 2)) := by
  have hly : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2y : Real.log 2 ≤ Real.log (y : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hy)
  have ht2 : t ^ 2 ≤ (Real.log (y : ℝ))⁻¹ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hC : 0 ≤ Real.log 4 + 4 := by positivity
  have hlocal : t ^ 2 * Real.log (y : ℝ) ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right ht2 (sq_nonneg (Real.log (y : ℝ)))
    simpa [← mul_pow, hly.ne'] using h
  have hcoeff : 1 + (Real.log 4 + 4) / Real.log (y : ℝ) ≤
      1 + (Real.log 4 + 4) / Real.log 2 := by
    gcongr
  refine (candidate_integral_shifted_euler_ratio_le_exp y ha t).trans ?_
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ 8 * t ^ 2 * (Real.log (y : ℝ) *
        (Real.log (y : ℝ) + (Real.log 4 + 4))) :=
      mul_le_mul_of_nonneg_left (candidate_sum_prime_log_sq_div_le (by omega)) (by positivity)
    _ = 8 * (t ^ 2 * Real.log (y : ℝ) ^ 2) *
        (1 + (Real.log 4 + 4) / Real.log (y : ℝ)) := by field_simp
    _ ≤ 8 * 1 * (1 + (Real.log 4 + 4) / Real.log 2) := by gcongr
    _ = _ := by ring

end
end Erdos.Problem1144
