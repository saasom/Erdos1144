import Erdos.Problem1144.HarperCandidateCovarianceRowFourier
import Mathlib.Algebra.Order.Round

open Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- Distance to the nearest integer, with the nearest integer chosen by
mathlib's rounding operation. -/
def candidateIntegerDistance (x : ℝ) : ℝ := |x - round x|

theorem candidateIntegerDistance_nonneg (x : ℝ) : 0 ≤ candidateIntegerDistance x :=
  abs_nonneg _

theorem candidateIntegerDistance_le_abs_sub_int (x : ℝ) (m : ℤ) :
    candidateIntegerDistance x ≤ |x - m| := round_le x m

/-- Moving a frequency by `d` moves its distance from the integers by at
most `d`. This remains valid when the nearest integer changes. -/
theorem candidateIntegerDistance_le_add (x y : ℝ) :
    candidateIntegerDistance x ≤ candidateIntegerDistance y + |x - y| := by
  calc
    _ ≤ |x - round y| := round_le x (round y)
    _ ≤ |y - round y| + |x - y| := by
      convert abs_add_le (y - (round y : ℝ)) (x - y) using 1 <;> ring
    _ = _ := rfl

theorem candidateIntegerDistance_lipschitz : LipschitzWith 1 candidateIntegerDistance := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  apply abs_le.mpr
  have hxy := candidateIntegerDistance_le_add x y
  have hyx := candidateIntegerDistance_le_add y x
  rw [abs_sub_comm y x] at hyx
  constructor <;> linarith

/-- Jordan's inequality turns the exact geometric-sum chord into the
distance to an integer, retaining the factor four. -/
theorem candidate_fourier_chord_ge_integerDistance (x : ℝ) :
    4 * candidateIntegerDistance x ≤ ‖candidateCovariancePhase (2 * Real.pi * x) - 1‖ := by
  have hsmall : |Real.pi * (x - round x)| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [abs_sub_round x, Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hsmall
  have he : |Real.sin (Real.pi * (x - round x))| = |Real.sin (Real.pi * x)| := by
    rw [show Real.pi * (x - round x) = Real.pi * x - (round x : ℝ) * Real.pi by ring,
      Real.sin_sub_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  rw [he, abs_mul, abs_of_pos Real.pi_pos] at hs
  have hj : 2 * candidateIntegerDistance x ≤ |Real.sin (Real.pi * x)| := by
    convert hs using 1
    unfold candidateIntegerDistance
    field_simp
  have hc : ‖candidateCovariancePhase (2 * Real.pi * x) - 1‖ =
      2 * |Real.sin (Real.pi * x)| := by
    unfold candidateCovariancePhase
    rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
    norm_num [Real.norm_eq_abs, abs_mul]
  rw [hc]
  linarith

/-- The actual `2π`-spaced grid has the reciprocal nearest-integer bound.
The hypothesis excludes division by zero at an exact resonance. -/
theorem candidate_rowFourierSum_norm_le_integerDistance (n : ℕ) (x : ℝ)
    (hx : 0 < candidateIntegerDistance x) :
    ‖candidateRowFourierSum n (2 * Real.pi) x‖ ≤
      min (n : ℝ) (1 / (2 * candidateIntegerDistance x)) := by
  have h := candidate_rowFourierSum_norm_le_of_chord_ge n (2 * Real.pi) x
    (show 0 < 4 * candidateIntegerDistance x by positivity)
    (candidate_fourier_chord_ge_integerDistance x)
  convert h using 2 <;> ring

/-- Reversing the grid spacing conjugates the finite Fourier sum and hence
does not change its norm. This matches the sign in the actual row formula. -/
theorem candidate_rowFourierSum_norm_neg_spacing (n : ℕ) (h x : ℝ) :
    ‖candidateRowFourierSum n (-h) x‖ = ‖candidateRowFourierSum n h x‖ := by
  have he : candidateRowFourierSum n (-h) x = starRingEnd ℂ (candidateRowFourierSum n h x) := by
    unfold candidateRowFourierSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [candidateCovariancePhase, candidateCovariancePhase, ← Complex.exp_conj]
    congr 1
    simp
  rw [he, Complex.norm_conj]

/-- The reciprocal resonance bound with the exact negative spacing used
by the Euler-band row expansion. -/
theorem candidate_rowFourierSum_norm_le_neg_integerDistance (n : ℕ) (x : ℝ)
    (hx : 0 < candidateIntegerDistance x) :
    ‖candidateRowFourierSum n (-(2 * Real.pi)) x‖ ≤
      min (n : ℝ) (1 / (2 * candidateIntegerDistance x)) := by
  rw [candidate_rowFourierSum_norm_neg_spacing]
  exact candidate_rowFourierSum_norm_le_integerDistance n x hx

/-- The near-resonant set is exactly a union of intervals around integers. -/
theorem candidateIntegerDistance_le_iff (x ε : ℝ) :
    candidateIntegerDistance x ≤ ε ↔ ∃ m : ℤ, |x - m| ≤ ε := by
  constructor
  · exact fun h => ⟨round x, h⟩
  · rintro ⟨m, hm⟩
    exact (candidateIntegerDistance_le_abs_sub_int x m).trans hm

/-- Coordinatewise near-diagonality gives the exact `2k d` enlargement
of the signed sum appearing in the even Fourier power. -/
theorem candidate_rowPowerFrequency_sub_le {X : Type*} {k : ℕ}
    (b c : X → ℝ) (z : (Fin k → X) × (Fin k → X)) {d : ℝ}
    (h₁ : ∀ i, |b (z.1 i) - c (z.1 i)| ≤ d)
    (h₂ : ∀ i, |b (z.2 i) - c (z.2 i)| ≤ d) :
    |candidateRowPowerFrequency b z - candidateRowPowerFrequency c z| ≤ 2 * k * d := by
  have hsum (t : Fin k → X) (ht : ∀ i, |b (t i) - c (t i)| ≤ d) :
      |(∑ i, b (t i)) - ∑ i, c (t i)| ≤ k * d := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, |b (t i) - c (t i)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin k, d := Finset.sum_le_sum fun i _ => ht i
      _ = _ := by simp
  have h₁' := hsum z.1 h₁
  have h₂' := hsum z.2 h₂
  unfold candidateRowPowerFrequency
  calc
    _ = |((∑ i, b (z.1 i)) - ∑ i, c (z.1 i)) -
        ((∑ i, b (z.2 i)) - ∑ i, c (z.2 i))| := by congr 1; ring
    _ ≤ |(∑ i, b (z.1 i)) - ∑ i, c (z.1 i)| +
        |(∑ i, b (z.2 i)) - ∑ i, c (z.2 i)| := abs_sub _ _
    _ ≤ _ := by linarith

/-- The same integer labels both paired resonant cells, after the explicit
near-diagonal enlargement. -/
theorem candidate_rowPowerFrequency_resonance_transfer {X : Type*} {k : ℕ}
    (b c : X → ℝ) (z : (Fin k → X) × (Fin k → X)) {d ε : ℝ} (m : ℤ)
    (h₁ : ∀ i, |b (z.1 i) - c (z.1 i)| ≤ d)
    (h₂ : ∀ i, |b (z.2 i) - c (z.2 i)| ≤ d)
    (hm : |candidateRowPowerFrequency c z - m| ≤ ε) :
    |candidateRowPowerFrequency b z - m| ≤ ε + 2 * k * d := by
  have hd := candidate_rowPowerFrequency_sub_le b c z h₁ h₂
  calc
    _ ≤ |candidateRowPowerFrequency c z - m| +
        |candidateRowPowerFrequency b z - candidateRowPowerFrequency c z| := by
      convert abs_add_le (candidateRowPowerFrequency c z - (m : ℝ))
        (candidateRowPowerFrequency b z - candidateRowPowerFrequency c z) using 1 <;> ring
    _ ≤ _ := add_le_add hm hd

end
end Erdos.Problem1144
