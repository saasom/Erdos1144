import Erdos.Problem1144.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos
namespace Problem1144

/-- Coin-flip sample space, indexed by natural numbers.

Prime coordinates carry the random multiplicative function. Non-prime
coordinates are harmless noise that keep the index type simple.
-/
abbrev Omega := ℕ → Bool

/-- The fair coin law on `Bool`.

The infinite product construction is isolated as `mu` below, so downstream
work can proceed before the product-measure API is finalized.
-/
noncomputable def coin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true

/-- The fair coin law is a probability measure. -/
instance coin_isProbabilityMeasure : IsProbabilityMeasure coin where
  measure_univ := by
    simp [coin, ENNReal.inv_two_add_inv_two]

/-- Product law for independent fair coins indexed by `ℕ`. -/
noncomputable def mu : Measure Omega :=
  Measure.infinitePi fun _ : ℕ => coin

/-- The infinite fair-coin product is a probability measure. -/
instance mu_isProbabilityMeasure : IsProbabilityMeasure mu := by
  dsimp [mu]
  infer_instance

/-- The coordinate coin flips are independent under the infinite product law. -/
theorem iIndepFun_coordinates :
    iIndepFun (fun p (omega : Omega) => omega p) mu := by
  simpa [mu] using
    (iIndepFun_infinitePi
      (P := fun _ : ℕ => coin)
      (X := fun _ : ℕ => id)
      (by fun_prop))

/-- Each coordinate has the fair coin law. -/
theorem map_eval_mu (p : ℕ) :
    mu.map (fun omega : Omega => omega p) = coin := by
  simpa [mu] using
    (Measure.infinitePi_map_eval (fun _ : ℕ => coin) p)

/-- Rademacher sign attached to the coordinate `p`. -/
def eps (omega : Omega) (p : ℕ) : ℝ :=
  if omega p then 1 else -1

/-- The same Rademacher sign as a function on one Boolean coordinate. -/
noncomputable def boolSign (b : Bool) : ℝ :=
  if b then 1 else -1

/-- Coordinate signs are Boolean signs after evaluation. -/
theorem eps_eq_boolSign (omega : Omega) (p : ℕ) :
    eps omega p = boolSign (omega p) := rfl

/-- Powers of the Boolean sign are integrable under the fair coin law. -/
theorem integrable_boolSign_pow (k : ℕ) :
    Integrable (fun b : Bool => boolSign b ^ k) coin := by
  refine
    Integrable.of_bound
      (by
        exact
          (measurable_of_finite fun b : Bool => boolSign b ^ k).aestronglyMeasurable)
      1 ?_
  exact ae_of_all _ fun b => by
    cases b <;> simp [boolSign]

/-- One-coordinate Rademacher orthogonality. -/
theorem integral_boolSign_pow (k : ℕ) :
    ∫ b : Bool, boolSign b ^ k ∂coin = if Even k then 1 else 0 := by
  rw [integral_fintype (integrable_boolSign_pow k)]
  by_cases hk : Even k
  · rw [if_pos hk]
    simp [boolSign, coin, measureReal_def, ENNReal.toReal_inv, hk.neg_one_pow]
    norm_num
  · rw [if_neg hk]
    have hok : Odd k := Nat.not_even_iff_odd.mp hk
    simp [boolSign, coin, measureReal_def, ENNReal.toReal_inv, hok.neg_one_pow]

/-- The Boolean sign has mean zero. -/
theorem integral_boolSign :
    ∫ b : Bool, boolSign b ∂coin = 0 := by
  simpa using integral_boolSign_pow 1

/-- Each coordinate sign is measurable. -/
theorem measurable_eps (p : ℕ) :
    Measurable fun omega : Omega => eps omega p := by
  exact
    (measurable_of_finite boolSign).comp
      (measurable_pi_apply p)

/-- Rademacher signs square to one. -/
@[simp] theorem eps_mul_self (omega : Omega) (p : ℕ) :
    eps omega p * eps omega p = 1 := by
  unfold eps
  by_cases h : omega p <;> simp [h]

/-- Rademacher signs square to one, power form. -/
@[simp] theorem eps_sq (omega : Omega) (p : ℕ) :
    eps omega p ^ 2 = 1 := by
  rw [pow_two, eps_mul_self]

/-- Prime factors whose exponent in `n` is odd. -/
noncomputable def sfKernel (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p => n.factorization p % 2 = 1

/-- Random completely multiplicative sign, represented by the squarefree kernel.

For positive `n`, this is equivalent to
`∏_{p^a || n} eps omega p ^ a`, since `eps omega p ^ 2 = 1`.
-/
noncomputable def f (omega : Omega) (n : ℕ) : ℝ :=
  ∏ p ∈ sfKernel n, eps omega p

/-- For each integer input, the random multiplicative sign is measurable. -/
theorem measurable_f (n : ℕ) :
    Measurable fun omega : Omega => f omega n := by
  unfold f
  exact Finset.measurable_prod _ fun p _ => measurable_eps p

/-- The empty product gives `f(1) = 1`. -/
@[simp] theorem f_one (omega : Omega) : f omega 1 = 1 := by
  simp [f, sfKernel]

/-- Every value of the complete Rademacher model squares to one. -/
@[simp] theorem f_mul_self (omega : Omega) (n : ℕ) :
    f omega n * f omega n = 1 := by
  rw [f, ← Finset.prod_mul_distrib]
  simp

/-- Every value of the complete Rademacher model squares to one, power form. -/
@[simp] theorem f_sq (omega : Omega) (n : ℕ) :
    f omega n ^ 2 = 1 := by
  rw [pow_two, f_mul_self]

/-- Every value of the complete Rademacher model has absolute value one. -/
@[simp] theorem abs_f (omega : Omega) (n : ℕ) :
    |f omega n| = 1 := by
  rw [← Real.norm_eq_abs]
  rw [f, norm_prod]
  apply Finset.prod_eq_one
  intro p hp
  unfold eps
  by_cases h : omega p <;> simp [h]

end Problem1144
end Erdos
