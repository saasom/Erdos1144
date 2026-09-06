import Erdos.Problem1144.HarperCandidateTranslation

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# Discrete enlarged log-window second moments

Nested complete sums have nonnegative pair correlations. Their normalized
interval second moments are therefore controlled by variance increments.
Summing over a log-grid telescopes even when each interval spans several
mesh cells. The loss is the actual overlap count, never the number of cells.
-/

theorem candidate_integral_S_sub_sq_le {M N : ℕ} (hMN : M ≤ N) :
    (∫ ω, (S ω N - S ω M) ^ 2 ∂mu) ≤
      (∫ ω, S ω N ^ 2 ∂mu) - ∫ ω, S ω M ^ 2 ∂mu := by
  have heq : (fun ω ↦ (S ω N - S ω M) ^ 2) =
      (fun ω ↦ S ω N ^ 2 + S ω M ^ 2 - 2 * (S ω N * S ω M)) := by funext ω; ring
  rw [heq]
  have hsum : Integrable (fun ω ↦ S ω N ^ 2 + S ω M ^ 2) mu :=
    (integrable_S_sq N).add (integrable_S_sq M)
  rw [integral_sub hsum ((integrable_S_mul_S N M).const_mul 2),
    integral_add (integrable_S_sq N) (integrable_S_sq M), integral_const_mul]
  linarith [candidate_integral_S_sq_le_cross hMN]

/-- Expected squared interval sum, normalized at the window's left endpoint. -/
noncomputable def candidateLogWindowSecondMoment (u v : ℝ) : ℝ :=
  ∫ ω, ((S ω ⌊Real.exp v⌋₊ - S ω ⌊Real.exp u⌋₊) / Real.exp (u / 2)) ^ 2 ∂mu

theorem candidateLogWindowSecondMoment_nonneg (u v : ℝ) :
    0 ≤ candidateLogWindowSecondMoment u v := integral_nonneg fun _ ↦ sq_nonneg _

/-- This is a bound on expected squared signed sums; it does not compare
signed sums pointwise. -/
theorem candidateLogWindowSecondMoment_le {w : ℝ} (hw : 0 ≤ w) (u : ℝ) :
    candidateLogWindowSecondMoment u (u + w) ≤
      Real.exp w * candidateLogSecondMoment (u + w) - candidateLogSecondMoment u := by
  have hMN : ⌊Real.exp u⌋₊ ≤ ⌊Real.exp (u + w)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr (le_add_of_nonneg_right hw))
  unfold candidateLogWindowSecondMoment
  simp_rw [div_pow]
  rw [integral_div]
  apply (div_le_div_of_nonneg_right (candidate_integral_S_sub_sq_le hMN)
    (sq_nonneg (Real.exp (u / 2)))).trans_eq
  unfold candidateLogSecondMoment
  simp_rw [candidate_logProcess_eq_S_div_exp, div_pow, integral_div]
  have hexp : Real.exp ((u + w) / 2) ^ 2 = Real.exp w * Real.exp (u / 2) ^ 2 := by
    rw [sq, sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  field_simp

private theorem candidate_sum_shift_difference (F : ℕ → ℝ) (n k : ℕ) :
    (∑ j ∈ Finset.range n, (F (j + k) - F j)) =
      (∑ j ∈ Finset.range k, F (j + n)) - ∑ j ∈ Finset.range k, F j := by
  have h₁ := Finset.sum_range_add F n k
  have h₂ := Finset.sum_range_add F k n
  have hn : n + k = k + n := Nat.add_comm _ _
  rw [hn] at h₁
  simp_rw [Nat.add_comm n, Nat.add_comm k] at h₁ h₂
  rw [Finset.sum_sub_distrib]
  linarith

/-- Exact discrete enlarged-window bound. `k` is the number of mesh cells
spanned by one window, and `a + (n+k)h ≤ L` is the actual enclosing horizon. -/
theorem candidate_sum_logWindowSecondMoment_le
    {a L h : ℝ} {n k : ℕ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hcover : a + ((n + k : ℕ) : ℝ) * h ≤ L) :
    h * (∑ j ∈ Finset.range n,
      candidateLogWindowSecondMoment (a + (j : ℝ) * h) (a + ((j + k : ℕ) : ℝ) * h)) ≤
        h * ((k : ℝ) + (Real.exp ((k : ℝ) * h) - 1) * (n : ℝ)) * (1 + L) := by
  let F : ℕ → ℝ := fun j ↦ candidateLogSecondMoment (a + (j : ℝ) * h)
  have hF0 (j : ℕ) : 0 ≤ F j := candidateLogSecondMoment_nonneg _
  have hFB {j : ℕ} (hj : j ≤ n + k) : F j ≤ 1 + L := by
    apply candidateLogSecondMoment_le_of_le hL
    have hjR : (j : ℝ) ≤ (n + k : ℕ) := by exact_mod_cast hj
    have hmul := mul_le_mul_of_nonneg_right hjR hh
    linarith
  have hw : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hh
  have hpoint (j : ℕ) :
      candidateLogWindowSecondMoment (a + (j : ℝ) * h) (a + ((j + k : ℕ) : ℝ) * h) ≤
        (F (j + k) - F j) + (Real.exp ((k : ℝ) * h) - 1) * F (j + k) := by
    have hb := candidateLogWindowSecondMoment_le hw (a + (j : ℝ) * h)
    have heq : (a + (j : ℝ) * h) + (k : ℝ) * h =
        a + ((j + k : ℕ) : ℝ) * h := by push_cast; ring
    rw [heq] at hb
    dsimp only [F]
    linarith
  have htail : (∑ j ∈ Finset.range k, F (j + n)) ≤ (k : ℝ) * (1 + L) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range k, (1 + L) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hFB (by have := Finset.mem_range.mp hj; omega)
      _ = _ := by simp; ring
  have hfuture : (∑ j ∈ Finset.range n, F (j + k)) ≤ (n : ℝ) * (1 + L) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range n, (1 + L) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hFB (by have := Finset.mem_range.mp hj; omega)
      _ = _ := by simp; ring
  have hexp : 0 ≤ Real.exp ((k : ℝ) * h) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr hw)
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun j _ ↦ hpoint j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, candidate_sum_shift_difference] at hsum
  have hfirst : 0 ≤ ∑ j ∈ Finset.range k, F j := Finset.sum_nonneg fun j _ ↦ hF0 j
  have hfuture_mul := mul_le_mul_of_nonneg_left hfuture hexp
  have htotal : (∑ j ∈ Finset.range n,
      candidateLogWindowSecondMoment (a + (j : ℝ) * h) (a + ((j + k : ℕ) : ℝ) * h)) ≤
        ((k : ℝ) + (Real.exp ((k : ℝ) * h) - 1) * (n : ℝ)) * (1 + L) := by
    nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htotal hh

/-- A version making the linear mesh-size factor explicit. For fixed overlap
count and bounded window width, the remaining loss is polynomial in the
logarithmic horizon. -/
theorem candidate_sum_logWindowSecondMoment_le_mesh
    {a L h : ℝ} {n k : ℕ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hcover : a + ((n + k : ℕ) : ℝ) * h ≤ L) :
    h * (∑ j ∈ Finset.range n,
      candidateLogWindowSecondMoment (a + (j : ℝ) * h) (a + ((j + k : ℕ) : ℝ) * h)) ≤
        (k : ℝ) * h * (1 + (n : ℝ) * h * Real.exp ((k : ℝ) * h)) * (1 + L) := by
  have hb := candidate_sum_logWindowSecondMoment_le hh hL hcover
  have he : Real.exp ((k : ℝ) * h) - 1 ≤ (k : ℝ) * h * Real.exp ((k : ℝ) * h) := by
    have he := Real.add_one_le_exp (-((k : ℝ) * h))
    have hp := mul_le_mul_of_nonneg_right he (Real.exp_pos ((k : ℝ) * h)).le
    rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero _)] at hp
    nlinarith
  apply hb.trans
  have hmul := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hall := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add_left hmul (k : ℝ)) hh) (by linarith : 0 ≤ 1 + L)
  nlinarith

end Erdos.Problem1144
