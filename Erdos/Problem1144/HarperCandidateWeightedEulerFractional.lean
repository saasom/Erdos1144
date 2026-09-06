import Erdos.Problem1144.HarperCandidateWeightedEulerRatio
import Erdos.Problem520.HarperFixedFractionalMoment

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

noncomputable section

/-!
# Real-axis fractional damping of the shifted squarefree Euler product

The density here is the squarefree Euler product squared, not the complete
Euler product. Its quarter moment is the half moment of the positive
squarefree Euler product on the real axis. The complete process still needs
the separate zeta multiplier and vertical Parseval assembly.
-/

private theorem radius_lt_one {p : ℕ} (hp : p.Prime)
    {a : ℝ} (ha : 0 ≤ a) : harperRankinEulerRadius p a < 1 := by
  refine (harperRankinEulerRadius_le_inv_sqrt hp.one_le ha).trans_lt ?_
  apply inv_lt_one_of_one_lt₀
  apply (Real.lt_sqrt (by norm_num)).mpr
  norm_num
  exact_mod_cast hp.one_lt

/-- A fair real Euler factor has a strictly decaying half moment. -/
theorem candidate_fair_sqrt_euler_factor_le_exp {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (Real.sqrt (1 - r) + Real.sqrt (1 + r)) / 2 ≤
      Real.exp (-r ^ 2 / 8) := by
  have hm : 0 ≤ 1 - r := by linarith
  have hp : 0 ≤ 1 + r := by positivity
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hs : 0 ≤ 1 - r ^ 2 := by linarith
  have hcross : Real.sqrt (1 - r) * Real.sqrt (1 + r) =
      Real.sqrt (1 - r ^ 2) := by
    rw [← Real.sqrt_mul hm]
    congr 1
    ring
  have hsqrt : Real.sqrt (1 - r ^ 2) ≤ 1 - r ^ 2 / 2 := by
    have hs1 := Real.sq_sqrt hs
    have hs0 := Real.sqrt_nonneg (1 - r ^ 2)
    nlinarith [sq_nonneg (r ^ 2)]
  have hsq : ((Real.sqrt (1 - r) + Real.sqrt (1 + r)) / 2) ^ 2 ≤
      1 - r ^ 2 / 4 := by
    nlinarith [Real.sq_sqrt hm, Real.sq_sqrt hp]
  have hexp : 1 - r ^ 2 / 4 ≤ Real.exp (-r ^ 2 / 4) := by
    linarith [Real.add_one_le_exp (-r ^ 2 / 4)]
  have hexpsq : Real.exp (-r ^ 2 / 4) = Real.exp (-r ^ 2 / 8) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [hexpsq] at hexp
  nlinarith [Real.exp_pos (-r ^ 2 / 8)]

private theorem coordinate_real_quarter {p : ℕ} (hp : p.Prime)
    {a : ℝ} (ha : 0 ≤ a) (b : Bool) :
    harperRankinCoordinateFactor p a 0 b ^ (1 / 4 : ℝ) =
      Real.sqrt (1 + (if b then 1 else -1) * harperRankinEulerRadius p a) := by
  have hr0 := harperRankinEulerRadius_nonneg p a
  have hr1 := (radius_lt_one hp ha).le
  have hb : 0 ≤ 1 + (if b then 1 else -1) * harperRankinEulerRadius p a := by
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> linarith
  have heq : harperRankinCoordinateFactor p a 0 b =
      (1 + (if b then 1 else -1) * harperRankinEulerRadius p a) ^ 2 := by
    simp [harperRankinCoordinateFactor, harperRankinEulerFactor, Problem520.ε]
  rw [heq, ← Real.rpow_natCast_mul hb, Real.sqrt_eq_rpow]
  norm_num

/-- Exact shifted real-axis quarter moment of one squared Euler factor. -/
theorem candidate_integral_shifted_euler_quarter_prime {p : ℕ}
    (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) :
    (∫ b, harperRankinCoordinateFactor p a 0 b ^ (1 / 4 : ℝ)
        ∂Problem520.coin) =
      (Real.sqrt (1 - harperRankinEulerRadius p a) +
        Real.sqrt (1 + harperRankinEulerRadius p a)) / 2 := by
  rw [Problem520.integral_coin_bool]
  simp only [coordinate_real_quarter hp ha, Bool.false_eq_true, if_false,
    if_true, neg_one_mul, one_mul, ← sub_eq_add_neg]

/-- Actual fair squarefree Euler damping, uniform over all nonnegative shifts. -/
theorem candidate_integral_shifted_euler_quarter_le_exp (y : ℕ)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ ω, harperRankinEulerDensity y a ω 0 ^ (1 / 4 : ℝ) ∂Problem520.μ) ≤
      Real.exp (-(∑ p ∈ (y + 1).primesBelow,
        harperRankinEulerRadius p a ^ 2) / 8) := by
  let g : Problem520.HarperPrimeCube y → ℝ := fun η ↦
    ∏ p : Problem520.HarperPrimeIndex y,
      harperRankinCoordinateFactor p.1 a 0 (η p) ^ (1 / 4 : ℝ)
  have hg (ω : Problem520.Omega) :
      g (Problem520.harperPrimeRestriction y ω) =
        harperRankinEulerDensity y a ω 0 ^ (1 / 4 : ℝ) := by
    dsimp [g]
    rw [Real.finset_prod_rpow _ _ (fun p _ ↦
      harperRankinEulerFactor_nonneg (fun _ ↦ ω p.1) p.1 a 0)]
    change harperRankinCubeDensity y a 0 (Problem520.harperPrimeRestriction y ω) ^
      (1 / 4 : ℝ) = _
    rw [harperRankinCubeDensity_harperPrimeRestriction]
  rw [show (fun ω ↦ harperRankinEulerDensity y a ω 0 ^ (1 / 4 : ℝ)) =
      (fun ω ↦ g (Problem520.harperPrimeRestriction y ω)) from
        funext fun ω ↦ (hg ω).symm,
    Problem520.integral_comp_harperPrimeRestriction_mu]
  change (∫ η, g η ∂Problem520.harperFairCubeLaw y) ≤ _
  dsimp only [g]
  rw [Problem520.integral_prod_harperFairCubeLaw y
    (fun p b ↦ harperRankinCoordinateFactor p.1 a 0 b ^ (1 / 4 : ℝ))]
  calc
    _ ≤ ∏ p : Problem520.HarperPrimeIndex y,
        Real.exp (-harperRankinEulerRadius p.1 a ^ 2 / 8) := by
      apply Finset.prod_le_prod
      · intro p _
        exact integral_nonneg fun b ↦ Real.rpow_nonneg
          (harperRankinEulerFactor_nonneg (fun _ ↦ b) p.1 a 0) _
      · intro p _
        have hp := (Nat.mem_primesBelow.mp p.2).2
        rw [candidate_integral_shifted_euler_quarter_prime hp ha]
        exact candidate_fair_sqrt_euler_factor_le_exp
          (harperRankinEulerRadius_nonneg p.1 a) (radius_lt_one hp ha).le
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.sum_coe_sort ((y + 1).primesBelow)
        (fun p ↦ harperRankinEulerRadius p a ^ 2)]
      rw [← Finset.sum_div, Finset.sum_neg_distrib]

end
end Erdos.Problem1144
