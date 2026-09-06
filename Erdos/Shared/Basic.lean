import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Erdos

theorem one_add_one : (1 : Nat) + 1 = 2 := by
  norm_num

theorem square_nonnegative (x : ℝ) : 0 ≤ x ^ 2 := by
  exact sq_nonneg x

theorem exists_positive_nat : ∃ n : Nat, n > 0 := by
  exact ⟨1, by norm_num⟩

end Erdos
