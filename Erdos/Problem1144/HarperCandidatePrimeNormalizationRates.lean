import Erdos.Problem1144.HarperCandidatePrimeNormalization

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- The literal mass-normalization error has uniform decay faster than
every inverse power. The displayed envelope covers the endpoint second
moments of both the complete and squarefree processes. -/
theorem candidate_eventually_scaled_prime_normalization_sum_lt
    (D q : ℝ) {ν ε : ℝ} (hD : 0 ≤ D) (hν : ν < 1 / 10) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ n : ℕ,
      (n : ℝ) * Real.exp (-(T ^ ν)) ≤ D * T →
      T ^ q * (∑ j ∈ Finset.range n,
        (Real.sqrt (Problem520.weightedPrimeReciprocalBlock
          ⌊Real.exp (T + (j : ℝ) * Real.exp (-(T ^ ν)))⌋₊
          ⌊Real.exp (T + (j : ℝ) * Real.exp (-(T ^ ν)) +
            Real.exp (-(T ^ ν)))⌋₊) - Real.sqrt (Real.exp (-(T ^ ν)))) ^ 2 *
          ((2 + D * T) / T)) < ε := by
  let C := D * (D + 2) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hεC : 0 < ε / C := div_pos hε hC
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    candidate_eventually_log_prime_bin_relative_error (D + 1) (q + 1) hν hεC,
    candidate_eventually_log_prime_bin_relative_error (D + 1) 0 hν
      (show (0 : ℝ) < 1 by norm_num)] with T hT hsmall hunit
  intro n hn
  have hT0 : 0 < T := by linarith
  let δ := Real.exp (-(T ^ ν))
  have hδ : 0 < δ := Real.exp_pos _
  let r := (ε / C) / T ^ (q + 1)
  have hr : 0 < r := div_pos hεC (Real.rpow_pos_of_pos hT0 _)
  have hden : (2 + D * T) / T ≤ D + 2 := by
    apply (div_le_iff₀ hT0).mpr
    nlinarith
  have hpoint (j : ℕ) (hj : j ∈ Finset.range n) :
      (Real.sqrt (Problem520.weightedPrimeReciprocalBlock
        ⌊Real.exp (T + (j : ℝ) * δ)⌋₊ ⌊Real.exp (T + (j : ℝ) * δ + δ)⌋₊) -
          Real.sqrt δ) ^ 2 * ((2 + D * T) / T) ≤ δ * r * (D + 2) := by
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hj).le
    have hju : T + (j : ℝ) * δ ∈ Icc T ((D + 1) * T) := by
      constructor
      · nlinarith [mul_nonneg (Nat.cast_nonneg j) hδ.le]
      · have hd := (mul_le_mul_of_nonneg_right hjn hδ.le).trans hn
        nlinarith
    let m := Problem520.weightedPrimeReciprocalBlock
      ⌊Real.exp (T + (j : ℝ) * δ)⌋₊ ⌊Real.exp (T + (j : ℝ) * δ + δ)⌋₊
    have he1 : |m / δ - 1| < 1 := by
      simpa only [Real.rpow_zero, one_mul] using hunit (T + (j : ℝ) * δ) hju
    have her : |m / δ - 1| ≤ r := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hT0 (q + 1))).mpr
      exact (by simpa only [mul_comm] using
        (hsmall (T + (j : ℝ) * δ) hju).le)
    have hm : 0 ≤ m :=
      (candidate_prime_bin_mass_pos_of_relative_error hδ he1 le_rfl).le
    have hs := candidate_sqrt_mass_difference_sq_le hm hδ
      (le_refl |m / δ - 1|)
    have hs' : (Real.sqrt m - Real.sqrt δ) ^ 2 ≤ δ * r := by
      have he0 : 0 ≤ |m / δ - 1| := abs_nonneg _
      have he2 : |m / δ - 1| ^ 2 ≤ |m / δ - 1| := by nlinarith
      exact hs.trans ((mul_le_mul_of_nonneg_left he2 hδ.le).trans
        (mul_le_mul_of_nonneg_left her hδ.le))
    exact mul_le_mul hs' hden (by positivity) (by positivity)
  have hsum : (∑ j ∈ Finset.range n,
      (Real.sqrt (Problem520.weightedPrimeReciprocalBlock
        ⌊Real.exp (T + (j : ℝ) * δ)⌋₊ ⌊Real.exp (T + (j : ℝ) * δ + δ)⌋₊) -
          Real.sqrt δ) ^ 2 * ((2 + D * T) / T)) ≤
        D * T * r * (D + 2) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range n, δ * r * (D + 2) := Finset.sum_le_sum hpoint
      _ = ((n : ℝ) * δ) * r * (D + 2) := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hn hr.le) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hT0.le q)
  apply hscaled.trans_lt
  have hpow : T ^ (q + 1) = T ^ q * T := by rw [Real.rpow_add hT0, Real.rpow_one]
  have heq : T ^ q * (D * T * r * (D + 2)) = (D * (D + 2)) * (ε / C) := by
    dsimp only [r]
    rw [hpow]
    field_simp
  rw [heq]
  calc
    _ < C * (ε / C) := mul_lt_mul_of_pos_right (by dsimp only [C]; linarith) hεC
    _ = ε := mul_div_cancel₀ ε hC.ne'

end Erdos.Problem1144
