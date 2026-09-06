import Erdos.Problem1144.AbsoluteTail
import Erdos.Problem1144.HarperCandidateGaussianVariance

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-- A single prime flip changes a squarefree coefficient exactly when that
prime divides its index. Non-squarefree coefficients remain zero. -/
theorem candidate_gSquarefree_flip_singleton
    (ω : Omega) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    gSquarefree (freshSignFlip {p} ω) n =
      if p ∣ n then -gSquarefree ω n else gSquarefree ω n := by
  classical
  by_cases hn : Squarefree n
  · have hmem : p ∈ sfKernel n ↔ p ∣ n := by
      rw [mem_sfKernel_iff_odd_factorization]
      by_cases hd : p ∣ n
      · rw [Nat.factorization_eq_one_of_squarefree hn hp hd]
        simp [hd]
      · rw [Nat.factorization_eq_zero_of_not_dvd hd]
        simp [hd]
    simp only [gSquarefree_of_squarefree _ hn, f_freshSignFlip_singleton, hmem]
  · simp [gSquarefree, hn]

/-- The local Euler-factor recurrence remains exact in the squarefree model,
including indices divisible by the square of the flipped prime. -/
theorem candidate_gSquarefree_flip_recurrence
    (ω : Omega) {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) :
    gSquarefree (freshSignFlip {p} ω) n + eps ω p *
      (if p ∣ n then gSquarefree (freshSignFlip {p} ω) (n / p) else 0) =
    gSquarefree ω n - eps ω p *
      (if p ∣ n then gSquarefree ω (n / p) else 0) := by
  classical
  by_cases hd : p ∣ n
  · simp only [if_pos hd]
    by_cases hsq : Squarefree n
    · have hq : Squarefree (n / p) := hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hd)
      simpa only [gSquarefree_of_squarefree _ hsq,
        gSquarefree_of_squarefree _ hq, if_pos hd] using
          oneCoordinateFlip_coefficient_recurrence p hp ω hn
    · rw [gSquarefree_of_not_squarefree _ hsq,
        gSquarefree_of_not_squarefree _ hsq, zero_add, zero_sub]
      by_cases hq : Squarefree (n / p)
      · have hpq : p ∣ n / p := by
          by_contra h
          have hcop := hp.coprime_iff_not_dvd.mpr h
          have h := (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hq⟩
          rw [Nat.mul_div_cancel' hd] at h
          exact hsq h
        rw [candidate_gSquarefree_flip_singleton ω hp, if_pos hpq]
        ring
      · simp only [gSquarefree_of_not_squarefree _ hq]
        ring
  · rw [candidate_gSquarefree_flip_singleton ω hp, if_neg hd]
    simp only [if_neg hd, mul_zero, add_zero, sub_zero]

/-- Exact summatory Euler-factor recurrence at every natural cutoff. -/
theorem candidate_GSquarefree_flip_recurrence
    (ω : Omega) {p : ℕ} (hp : p.Prime) (N : ℕ) :
    GSquarefree (freshSignFlip {p} ω) N +
      eps ω p * GSquarefree (freshSignFlip {p} ω) (N / p) =
    GSquarefree ω N - eps ω p * GSquarefree ω (N / p) := by
  classical
  unfold GSquarefree
  rw [← sum_dvd_div_eq_sum_Icc_div
      (gSquarefree (freshSignFlip {p} ω)) N p hp.pos,
    ← sum_dvd_div_eq_sum_Icc_div (gSquarefree ω) N p hp.pos,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n hn =>
    candidate_gSquarefree_flip_recurrence ω hp (Finset.mem_Icc.mp hn).1

/-- One prime division becomes one logarithmic translation with the exact
normalization coefficient `exp(-log p / 2)`. -/
theorem candidate_squarefree_log_prime_translate
    (ω : Omega) {p : ℕ} (hp : 0 < p) (t : ℝ) :
    Real.exp (-Real.log p / 2) *
      harperCandidateSquarefreeLogProcess ω (t - Real.log p) =
    GSquarefree ω (⌊Real.exp t⌋₊ / p) / Real.exp (t / 2) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hcut : ⌊Real.exp (t - Real.log p)⌋₊ = ⌊Real.exp t⌋₊ / p := by
    rw [Real.exp_sub, Real.exp_log hpR, Nat.floor_div_natCast]
  rw [harperCandidateSquarefreeLogProcess_eq_quotient, hcut,
    show (t - Real.log p) / 2 = t / 2 + (-Real.log p / 2) by ring, Real.exp_add]
  field_simp

/-- Literal log-process recurrence, valid at negative times as well. -/
theorem candidate_squarefree_log_flip_recurrence
    (ω : Omega) {p : ℕ} (hp : p.Prime) (t : ℝ) :
    harperCandidateSquarefreeLogProcess (freshSignFlip {p} ω) t +
      (eps ω p * Real.exp (-Real.log p / 2)) *
        harperCandidateSquarefreeLogProcess (freshSignFlip {p} ω) (t - Real.log p) =
    harperCandidateSquarefreeLogProcess ω t -
      (eps ω p * Real.exp (-Real.log p / 2)) *
        harperCandidateSquarefreeLogProcess ω (t - Real.log p) := by
  simp only [mul_assoc]
  rw [candidate_squarefree_log_prime_translate _ hp.pos,
    candidate_squarefree_log_prime_translate _ hp.pos]
  simp only [harperCandidateSquarefreeLogProcess_eq_quotient,
    ← mul_div_assoc, ← add_div, ← sub_div]
  rw [candidate_GSquarefree_flip_recurrence ω hp]

/-- Prime division contracts the log-normalized L² translation coefficient
by at least `3/4`; the resulting squared energy loss is at most `49`. -/
theorem candidate_prime_log_translation_coefficient_le
    {p : ℕ} (hp : p.Prime) : Real.exp (-Real.log p / 2) ≤ 3 / 4 := by
  have hpos := Real.exp_pos (-Real.log (p : ℝ) / 2)
  have hsq : Real.exp (-Real.log (p : ℝ) / 2) ^ 2 = (p : ℝ)⁻¹ := by
    rw [pow_two, ← Real.exp_add,
      show -Real.log (p : ℝ) / 2 + -Real.log p / 2 = -Real.log p by ring,
      Real.exp_neg, Real.exp_log (Nat.cast_pos.mpr hp.pos)]
  have hi : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        (by exact_mod_cast hp.two_le : (2 : ℝ) ≤ p)
  nlinarith

end Erdos.Problem1144
