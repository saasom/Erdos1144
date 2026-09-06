import Erdos.Problem1144.Model
import Mathlib.Order.Filter.AtTopBot.Basic

open scoped BigOperators

namespace Erdos
namespace Problem1144

/-- Summatory function `S(N) = sum_{1 <= n <= N} f(n)`. -/
noncomputable def S (omega : Omega) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, f omega n

/-- For each cutoff, the summatory function is measurable. -/
theorem measurable_S (N : ℕ) :
    Measurable fun omega : Omega => S omega N := by
  unfold S
  exact Finset.measurable_sum _ fun n _ => measurable_f n

/-- The summatory function is bounded by the number of summands, since each
model value has absolute value one. -/
theorem abs_S_le_card (omega : Omega) (N : ℕ) :
    |S omega N| ≤ ((Finset.Icc 1 N).card : ℝ) := by
  unfold S
  calc
    |∑ n ∈ Finset.Icc 1 N, f omega n|
        ≤ ∑ n ∈ Finset.Icc 1 N, |f omega n| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ((Finset.Icc 1 N).card : ℝ) := by
          simp [abs_f]

/-- Cruder but often convenient form of `abs_S_le_card`. -/
theorem abs_S_le (omega : Omega) (N : ℕ) :
    |S omega N| ≤ (N : ℝ) := by
  have h := abs_S_le_card omega N
  simpa [Nat.card_Icc] using h

/-- Square-subsequence normalization `S((r + 1)^2) / (r + 1)`.

The shift avoids division by zero and keeps all sums indexed by `Finset.range`.
-/
noncomputable def Y (omega : Omega) (r : ℕ) : ℝ :=
  S omega ((r + 1) ^ 2) / (((r + 1 : ℕ) : ℝ))

/-- For each square-subsequence index, `Y` is measurable. -/
theorem measurable_Y (r : ℕ) :
    Measurable fun omega : Omega => Y omega r := by
  unfold Y
  exact (measurable_S ((r + 1) ^ 2)).div_const _

/-- Logarithmic quadratic statistic along the square subsequence. -/
noncomputable def Quad (omega : Omega) (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.range R, (Y omega r) ^ 2 / (((r + 1 : ℕ) : ℝ))

/-- The finite quadratic statistic is measurable. -/
theorem measurable_Quad (R : ℕ) :
    Measurable fun omega : Omega => Quad omega R := by
  unfold Quad
  exact Finset.measurable_sum _ fun r _ => ((measurable_Y r).pow_const 2).div_const _

/-- Logarithmic cubic statistic along the square subsequence. -/
noncomputable def Cub (omega : Omega) (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.range R, (Y omega r) ^ 3 / (((r + 1 : ℕ) : ℝ))

/-- The finite cubic statistic is measurable. -/
theorem measurable_Cub (R : ℕ) :
    Measurable fun omega : Omega => Cub omega R := by
  unfold Cub
  exact Finset.measurable_sum _ fun r _ => ((measurable_Y r).pow_const 3).div_const _

/-- Sparse scale `R_j = 2^(2^j)`. -/
def Rseq (j : ℕ) : ℕ :=
  2 ^ (2 ^ j)

/-- Logarithmic scale `L_j = 2^j`. -/
def Lseq (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j

end Problem1144
end Erdos
