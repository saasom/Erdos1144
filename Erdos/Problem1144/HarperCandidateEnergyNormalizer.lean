import Erdos.Problem1144.HarperRankinNormalizer

open Finset Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- An absolute normalizer constant for all nonnegative shifts with
`a log y ≤ 1`. It comes from the already proved weighted-prime estimate. -/
noncomputable def candidateRankinNormalizerConstant : ℝ :=
  (1 / 2) * Real.exp (-2 * (1 + (Real.log 4 + 4) / Real.log 4))

theorem candidateRankinNormalizerConstant_pos : 0 < candidateRankinNormalizerConstant := by
  unfold candidateRankinNormalizerConstant
  positivity

/-- Increasing the real shift decreases the literal finite Euler normalizer. -/
theorem candidate_rankinNormalizer_antitone_shift (y : ℕ) {a b : ℝ} (hab : a ≤ b) :
    harperRankinPrimeEnergyNormalizer y b ≤ harperRankinPrimeEnergyNormalizer y a := by
  unfold harperRankinPrimeEnergyNormalizer
  apply Finset.prod_le_prod
  · intro p hp
    exact (harperRankinEulerNormalizer_pos p b).le
  · intro p hp
    have hprime := Nat.prime_of_mem_primesBelow hp
    simp only [harperRankinEulerNormalizer,
      harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg hprime.pos]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hprime.one_le) (neg_le_neg hab)

/-- The shifted normalizer grows with the prime cutoff, since each added
prime factor is at least one. -/
theorem candidate_rankinNormalizer_mono_cutoff {y z : ℕ} (hyz : y ≤ z) (a : ℝ) :
    harperRankinPrimeEnergyNormalizer y a ≤ harperRankinPrimeEnergyNormalizer z a := by
  unfold harperRankinPrimeEnergyNormalizer
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  · intro p hp
    exact (harperRankinEulerNormalizer_pos p a).le
  · intro p hp hpnot
    unfold harperRankinEulerNormalizer
    linarith [sq_nonneg (harperRankinEulerRadius p a)]

/-- Uniform shifted Mertens lower bound on the full effective window.
The constant is absolute and the shift is allowed to vary with the cutoff. -/
theorem candidate_rankinNormalizer_lower_small_shift
    {y : ℕ} (hy : 4 ≤ y) {a : ℝ} (ha : 0 ≤ a) (hay : a * Real.log y ≤ 1) :
    candidateRankinNormalizerConstant * Real.log y ≤
      harperRankinPrimeEnergyNormalizer y a := by
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hab : a ≤ 1 / Real.log y := (le_div_iff₀ hlog).mpr hay
  have hbase := exp_rankinNormalizerConstant_mul_log_le
    (V := (1 / 4 : ℝ)) (by norm_num) hy
  norm_num only [mul_one_div, show (8 : ℝ) / 4 = 2 by norm_num,
    show (4 : ℝ) / 4 = 1 by norm_num] at hbase
  exact hbase.trans (candidate_rankinNormalizer_antitone_shift y hab)

/-- Logarithmic form of the fixed-window lower bound, for the literal sum
of squared shifted Euler radii used by the fractional-moment argument. -/
theorem candidate_shifted_prime_square_mass_lower
    {y : ℕ} (hy : 4 ≤ y) {a : ℝ} (ha : 0 ≤ a) (hay : a * Real.log y ≤ 1) :
    Real.log (Real.log y) + Real.log candidateRankinNormalizerConstant ≤
      ∑ p ∈ (y + 1).primesBelow, harperRankinEulerRadius p a ^ 2 := by
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hlower := Real.log_le_log (mul_pos candidateRankinNormalizerConstant_pos hlog)
    (candidate_rankinNormalizer_lower_small_shift hy ha hay)
  rw [Real.log_mul candidateRankinNormalizerConstant_pos.ne' hlog.ne'] at hlower
  have hupper : Real.log (harperRankinPrimeEnergyNormalizer y a) ≤
      ∑ p ∈ (y + 1).primesBelow, harperRankinEulerRadius p a ^ 2 := by
    unfold harperRankinPrimeEnergyNormalizer
    rw [Real.log_prod (fun p hp => (harperRankinEulerNormalizer_pos p a).ne')]
    apply Finset.sum_le_sum
    intro p hp
    have h := Real.log_le_sub_one_of_pos (harperRankinEulerNormalizer_pos p a)
    simpa only [harperRankinEulerNormalizer, add_sub_cancel_left] using h
  linarith

end Erdos.Problem1144
