import Erdos.Problem1144.HarperCandidateCovarianceArithmeticMoments

open Finset
open scoped BigOperators

namespace Erdos.Problem1144

/-! The ordered-gap interaction estimate in Harper, arXiv:2012.15809,
Section 3.4. A logarithmic potential gives the needed `m log m` exponent
without a greedy block decomposition. All weights below are literal gap
weights; there is no probabilistic comparison hypothesis. -/

private theorem log_increment_lower {S c : ℝ} (hS : 0 < S)
    (hc : 0 ≤ c) (hcS : c ≤ S) :
    c / S ≤ 2 * (Real.log (S + c) - Real.log S) := by
  have hSc : 0 < S + c := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hSc hS)
  rw [Real.log_div hSc.ne' hS.ne'] at hlog
  have heq : 1 - ((S + c) / S)⁻¹ = c / (S + c) := by field_simp; ring
  rw [heq] at hlog
  have hdiv : c / S ≤ 2 * (c / (S + c)) := by
    rw [show 2 * (c / (S + c)) = (2 * c) / (S + c) by ring]
    apply (div_le_div_iff₀ hS hSc).mpr
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hcS)]
  linarith

private theorem sum_div_prefix_le_log (A : ℝ) (hA : 0 < A)
    (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) (hcA : ∀ j, c j ≤ A) (n : ℕ) :
    (∑ j ∈ range n, c j / (A + ∑ l ∈ range j, c l)) ≤
      2 * (Real.log (A + ∑ j ∈ range n, c j) - Real.log A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : 0 ≤ ∑ j ∈ range n, c j := sum_nonneg fun j _ => hc j
    have hstep := log_increment_lower (by linarith : 0 < A + ∑ j ∈ range n, c j)
      (hc n) ((hcA n).trans (by linarith))
    rw [sum_range_succ, sum_range_succ]
    simp only [← add_assoc]
    linarith

/-- A row of normalized ordered-gap interactions costs at most twice a
logarithm of its number of terms, uniformly in the actual positive weights. -/
theorem candidate_sum_min_div_prefix_le_log (A : ℝ) (hA : 0 < A)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (n : ℕ) :
    (∑ j ∈ range n, min A (b j) / (A + ∑ l ∈ range j, b l)) ≤
      2 * Real.log ((n : ℝ) + 1) := by
  let c : ℕ → ℝ := fun j => min A (b j)
  have hc : ∀ j, 0 ≤ c j := fun j => le_min hA.le (hb j)
  have hcA : ∀ j, c j ≤ A := fun j => min_le_left _ _
  have hcb : ∀ j, c j ≤ b j := fun j => min_le_right _ _
  have hsum : (∑ j ∈ range n, c j) ≤ (n : ℝ) * A := by
    simpa only [sum_const, card_range, nsmul_eq_mul] using
      sum_le_sum (s := range n) (fun j _ => hcA j)
  have hsum0 : 0 ≤ ∑ j ∈ range n, c j := sum_nonneg fun j _ => hc j
  have hlog : Real.log (A + ∑ j ∈ range n, c j) - Real.log A ≤
      Real.log ((n : ℝ) + 1) := by
    rw [← Real.log_div (by linarith : A + ∑ j ∈ range n, c j ≠ 0) hA.ne']
    apply Real.log_le_log (div_pos (by linarith) hA)
    apply (div_le_iff₀ hA).mpr
    nlinarith
  calc
    _ ≤ ∑ j ∈ range n, c j / (A + ∑ l ∈ range j, c l) := by
      apply sum_le_sum
      intro j hj
      apply div_le_div_of_nonneg_left (hc j)
        (by have := sum_nonneg (s := range j) (fun l _ => hc l); linarith)
      exact add_le_add le_rfl (sum_le_sum fun l _ => hcb l)
    _ ≤ 2 * (Real.log (A + ∑ j ∈ range n, c j) - Real.log A) :=
      sum_div_prefix_le_log A hA c hc hcA n
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by norm_num)

/-- Summing the interaction rows gives the required linear-logarithmic cost,
rather than a quadratic loss in the number of Euler factors. -/
theorem candidate_sum_ordered_gap_interactions_le
    (w : ℕ → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ) :
    (∑ i ∈ range m, ∑ j ∈ range (m - i - 1),
      min (w i) (w (i + j + 1)) /
        (w i + ∑ l ∈ range j, w (i + l + 1))) ≤
      2 * (m : ℝ) * Real.log ((m : ℝ) + 1) := by
  calc
    _ ≤ ∑ i ∈ range m, 2 * Real.log ((m - i - 1 : ℕ) + (1 : ℝ)) := by
      apply sum_le_sum
      intro i hi
      exact candidate_sum_min_div_prefix_le_log (w i) (hw i)
        (fun j => w (i + j + 1)) (fun j => (hw _).le) _
    _ ≤ ∑ i ∈ range m, 2 * Real.log ((m : ℝ) + 1) := by
      apply sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.log_le_log (by positivity)
      have h : (m - i - 1 : ℕ) ≤ m := by omega
      exact_mod_cast (Nat.add_le_add_right h 1)
    _ = _ := by simp; ring

/-- Actual ordered heights satisfy the same bound whenever their successive
spacings dominate the retained inverse-logarithmic cutoff weights. -/
theorem candidate_sum_height_gap_interactions_le
    (w t : ℕ → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (hgap : ∀ i, i + 1 < m → w i ≤ t (i + 1) - t i) :
    (∑ i ∈ range m, ∑ j ∈ range (m - i - 1),
      min (w i) (w (i + j + 1)) / (t (i + j + 1) - t i)) ≤
      2 * (m : ℝ) * Real.log ((m : ℝ) + 1) := by
  have hdist (i j : ℕ) (hij : i + j + 1 < m) :
      w i + ∑ l ∈ range j, w (i + l + 1) ≤ t (i + j + 1) - t i := by
    induction j with
    | zero => simpa using hgap i (by omega)
    | succ j ih =>
      have hprev := ih (by omega)
      have hnext := hgap (i + j + 1) (by omega)
      rw [sum_range_succ]
      have heq : i + (j + 1) + 1 = (i + j + 1) + 1 := by omega
      rw [heq]
      linarith
  apply le_trans _ (candidate_sum_ordered_gap_interactions_le w hw m)
  apply sum_le_sum
  intro i hi
  apply sum_le_sum
  intro j hj
  have hij : i + j + 1 < m := by
    have := mem_range.mp hi
    have := mem_range.mp hj
    omega
  apply div_le_div_of_nonneg_left (le_min (hw _).le (hw _).le)
    (by have := sum_nonneg (s := range j) (fun l _ => (hw (i + l + 1)).le); linarith [hw i])
    (hdist i j hij)

/-- The Rademacher sum-frequency contribution costs no more than the
corresponding difference-frequency contribution on a common positive band.
This is the extra interaction in the literal Rademacher mixed Euler moment. -/
theorem candidate_sum_rademacher_height_interactions_le
    (w t : ℕ → ℝ) (hw : ∀ i, 0 < w i) (m : ℕ)
    (ht : ∀ i, i < m → 0 ≤ t i)
    (hgap : ∀ i, i + 1 < m → w i ≤ t (i + 1) - t i) :
    (∑ i ∈ range m, ∑ j ∈ range (m - i - 1),
      (min (w i) (w (i + j + 1)) / (t (i + j + 1) - t i) +
        min (w i) (w (i + j + 1)) / |t (i + j + 1) + t i|)) ≤
      4 * (m : ℝ) * Real.log ((m : ℝ) + 1) := by
  have hmono : StrictMonoOn t (Set.Iio m) := by
    apply strictMonoOn_of_lt_succ Set.ordConnected_Iio
    intro i hmax hi hisucc
    have hg := hgap i hisucc
    change t i < t (i + 1)
    linarith [hw i]
  have hterm (i j : ℕ) (hi : i < m) (hj : j < m - i - 1) :
      min (w i) (w (i + j + 1)) / |t (i + j + 1) + t i| ≤
        min (w i) (w (i + j + 1)) / (t (i + j + 1) - t i) := by
    have hij : i + j + 1 < m := by omega
    have hpos : 0 < t (i + j + 1) - t i :=
      sub_pos.mpr (hmono hi hij (by omega))
    apply div_le_div_of_nonneg_left (le_min (hw _).le (hw _).le) hpos
    rw [abs_of_nonneg (add_nonneg (ht _ hij) (ht _ hi))]
    linarith [ht i hi]
  calc
    _ ≤ ∑ i ∈ range m, ∑ j ∈ range (m - i - 1),
        2 * (min (w i) (w (i + j + 1)) / (t (i + j + 1) - t i)) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      linarith [hterm i j (mem_range.mp hi) (mem_range.mp hj)]
    _ = 2 * (∑ i ∈ range m, ∑ j ∈ range (m - i - 1),
        min (w i) (w (i + j + 1)) / (t (i + j + 1) - t i)) := by
      simp only [mul_sum]
    _ ≤ _ := by
      have h := candidate_sum_height_gap_interactions_le w t hw m hgap
      linarith

end Erdos.Problem1144
