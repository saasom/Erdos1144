import Erdos.Problem1144.HarperCandidateCovarianceMixedCutoffs
import Erdos.Problem520.HarperCubicTail
import Erdos.Problem520.MertensProduct

open Finset Set MeasureTheory
open scoped BigOperators

namespace Erdos.Problem1144

/-! The residual mixed Euler exponent, with the prime and height sums
interchanged. A pair survives precisely above the larger of its two
prefix cutoffs. Thus the arithmetic oscillation theorem can be applied
at the actual scheduled endpoints selected by the gaps. -/

private theorem sum_filtered_swap {α β : Type*} (s : Finset α) (v : Finset β)
    (P : α → β → Prop) [∀ a b, Decidable (P a b)]
    (f : α → β → ℝ) :
    (∑ a ∈ s, ∑ b ∈ v.filter (P a), f a b) =
      ∑ b ∈ v, ∑ a ∈ s.filter (fun a => P a b), f a b := by
  classical
  simp only [Finset.sum_filter]
  exact Finset.sum_comm

/-- Exact diagonal, pairwise, and cubic decomposition of the exponent.
Both ordered Rademacher interaction frequencies are retained. -/
theorem candidate_sum_mixedEulerExponent_eq_prime_tails
    {ι : Type*} [DecidableEq ι] (P : Finset ℕ) (s : Finset ι)
    (c : ι → ℕ) (t : ι → ℝ) :
    (∑ p ∈ P, candidateEulerMixedExponent p (s.filter (fun i => c i < p)) t) =
      (∑ i ∈ s, ∑ p ∈ P.filter (fun p => c i < p), (p : ℝ)⁻¹) +
      (∑ ij ∈ s.offDiag, ∑ p ∈ P.filter (fun p => max (c ij.1) (c ij.2) < p),
        (Real.cos ((t ij.1 - t ij.2) * Real.log (p : ℝ)) +
          Real.cos ((t ij.1 + t ij.2) * Real.log (p : ℝ))) / p) +
      (4 / 3 : ℝ) * ∑ i ∈ s,
        ∑ p ∈ P.filter (fun p => c i < p), (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  classical
  have hoff (p : ℕ) :
      (s.filter (fun i => c i < p)).offDiag =
        s.offDiag.filter (fun ij => max (c ij.1) (c ij.2) < p) := by
    ext ij
    simp only [Finset.mem_offDiag, mem_filter, max_lt_iff]
    tauto
  have hpoint (p : ℕ) :
      candidateEulerMixedExponent p (s.filter (fun i => c i < p)) t =
        (∑ i ∈ s.filter (fun i => c i < p), (p : ℝ)⁻¹) +
        (∑ ij ∈ s.offDiag.filter (fun ij => max (c ij.1) (c ij.2) < p),
          (Real.cos ((t ij.1 - t ij.2) * Real.log (p : ℝ)) +
            Real.cos ((t ij.1 + t ij.2) * Real.log (p : ℝ))) / p) +
        (4 / 3 : ℝ) * ∑ i ∈ s.filter (fun i => c i < p),
          (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
    rw [candidateEulerMixedExponent_eq_pairKernel, hoff, ← Finset.sum_div]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← hoff]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (sum_filtered_swap P s _ _)
      (sum_filtered_swap P s.offDiag _ _))
    (congrArg ((4 / 3 : ℝ) * ·) (sum_filtered_swap P s _ _))

private theorem freshPrimes_eq_filter_Ioc (a b : ℕ) :
    Problem520.freshPrimes a b = (Finset.Ioc a b).filter Nat.Prime := by
  ext p
  simp [Problem520.mem_freshPrimes, and_comm, and_left_comm]

/-- The cubic Taylor remainder is uniformly bounded in the upper prime
cutoff, retaining the inverse-square-root gain at the removed prefix. -/
theorem candidate_sum_prime_cubic_tail_le {a y : ℕ} (ha : 1 ≤ a) :
    (∑ p ∈ (Finset.Ioc a y).filter Nat.Prime,
      (Real.sqrt (p : ℝ))⁻¹ ^ 3) ≤ 2 * (Real.sqrt (a : ℝ))⁻¹ := by
  by_cases hay : a ≤ y
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => by positivity)).trans
      (Problem520.sum_Ioc_harperCubicScale_le_inv_sqrt ha hay)
  · simp only [Finset.Ioc_eq_empty_of_le (by omega : y ≤ a), filter_empty, sum_empty]
    positivity

private theorem inv_le_log_one_add_add_sq (x : ℝ) (hx : 0 ≤ x) :
    x ≤ Real.log (1 + x) + x ^ 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < 1 + x)
  have heq : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  rw [heq] at h
  have hrem : x - x ^ 2 ≤ x / (1 + x) := by
    rw [le_div_iff₀ (by positivity : 0 < 1 + x)]
    nlinarith [mul_nonneg hx (sq_nonneg x)]
  linarith

/-- The diagonal exponential is at most a fixed absolute factor times
the exact fresh Euler normalizer. This requires no prime asymptotic. -/
theorem candidate_exp_freshReciprocalSum_le_normalizer (a y : ℕ) :
    Real.exp (Problem520.freshReciprocalSum a y) ≤
      Real.exp 2 * Problem520.freshPrimeEnergyNormalizer a y := by
  have hsum : Problem520.freshReciprocalSum a y ≤
      Real.log (Problem520.freshPrimeEnergyNormalizer a y) + 2 := by
    unfold Problem520.freshReciprocalSum Problem520.freshPrimeEnergyNormalizer
    rw [Real.log_prod (fun p hp => by positivity)]
    have h := Finset.sum_le_sum (s := Problem520.freshPrimes a y)
      (fun p _ => inv_le_log_one_add_add_sq (p : ℝ)⁻¹ (by positivity))
    rw [Finset.sum_add_distrib] at h
    have hsq : (∑ p ∈ Problem520.freshPrimes a y, ((p : ℝ)⁻¹) ^ 2) ≤ 2 := by
      have hsub : Problem520.freshPrimes a y ⊆ Finset.Ioo 0 (y + 1) := by
        intro p hp
        obtain ⟨hpprime, hpa, hpy⟩ := Problem520.mem_freshPrimes.mp hp
        exact Finset.mem_Ioo.mpr ⟨hpprime.pos, by omega⟩
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun p : ℕ => ((p : ℝ)⁻¹) ^ 2) (fun p _ _ => sq_nonneg _)
      have hb := sum_Ioo_inv_sq_le (α := ℝ) 0 (y + 1)
      norm_num at hb
      simpa only [inv_pow] using hle.trans (by simpa using hb)
    linarith
  calc
    _ ≤ Real.exp (Real.log (Problem520.freshPrimeEnergyNormalizer a y) + 2) :=
      Real.exp_le_exp.mpr hsum
    _ = _ := by rw [Real.exp_add, Real.exp_log (Problem520.freshPrimeEnergyNormalizer_pos a y)]; ring

/-- The sharp diagonal scale is the logarithmic ratio, with an absolute
constant valid at every natural cutoff at least two. -/
theorem candidate_exists_exp_freshReciprocalSum_le_log_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ a y : ℕ, 2 ≤ a → a ≤ y →
      Real.exp (Problem520.freshReciprocalSum a y) ≤
        C * (Real.log (y : ℝ) / Real.log (a : ℝ)) := by
  let C₀ := Real.exp
    (1 - Real.log (Real.log 2) + 2 * (Real.log 4 + 4) / Real.log 2)
  refine ⟨Real.exp 2 * (2 * C₀), by dsimp [C₀]; positivity, ?_⟩
  intro a y ha hay
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hnorm : Problem520.freshPrimeEnergyNormalizer a y ≤
      2 * C₀ * (Real.log (y : ℝ) / Real.log (a : ℝ)) := by
    have hup := Problem520.primeEnergyNormalizer_le_mertensConstant_mul_log (ha.trans hay)
    rw [Problem520.primeEnergyNormalizer_factor hay] at hup
    have hlo := mul_le_mul_of_nonneg_right
      (Problem520.half_mul_log_le_primeEnergyNormalizer ha)
      (Problem520.freshPrimeEnergyNormalizer_pos a y).le
    rw [← mul_div_assoc, le_div_iff₀ hloga]
    dsimp only [C₀] at hup ⊢
    nlinarith
  exact (candidate_exp_freshReciprocalSum_le_normalizer a y).trans
    ((mul_le_mul_of_nonneg_left hnorm (Real.exp_pos 2).le).trans_eq (by ring))

/-- The actual all-prime exponent has only a linear error beyond its
diagonal reciprocal masses and its two ordered pairwise cosine tails.
The effective cutoff `max 3 (c i)` also handles the unremoved root. -/
theorem candidate_allPrime_mixedExponent_le_prime_tails
    {ι : Type*} [Fintype ι] (y : ℕ) (c : ι → ℕ) (t : ι → ℝ) :
    (∑ p : Problem520.HarperPrimeIndex y,
      if 4 ≤ p.1 then candidateEulerMixedExponent p.1
        (Finset.univ.filter (fun i => c i < p.1)) t
      else (Finset.univ.filter (fun i => c i < p.1)).card * Real.log 4) ≤
      (∑ i, Problem520.freshReciprocalSum (max 3 (c i)) y) +
      (∑ ij ∈ (Finset.univ : Finset ι).offDiag,
        ∑ p ∈ (Finset.Ioc (max 3 (max (c ij.1) (c ij.2))) y).filter Nat.Prime,
          (Real.cos ((t ij.1 - t ij.2) * Real.log (p : ℝ)) +
            Real.cos ((t ij.1 + t ij.2) * Real.log (p : ℝ))) / p) +
      (4 * Real.log 4 + 8 / 3) * Fintype.card ι := by
  classical
  let P := (y + 1).primesBelow
  let Q := P.filter (fun p => 4 ≤ p)
  let R := P.filter (fun p => ¬4 ≤ p)
  let s : Finset ι := univ
  have hsplit : (∑ p : Problem520.HarperPrimeIndex y,
      if 4 ≤ p.1 then candidateEulerMixedExponent p.1 (s.filter (fun i => c i < p.1)) t
      else (s.filter (fun i => c i < p.1)).card * Real.log 4) =
      (∑ p ∈ Q, candidateEulerMixedExponent p (s.filter (fun i => c i < p)) t) +
      ∑ p ∈ R, (s.filter (fun i => c i < p)).card * Real.log 4 := by
    rw [show (∑ p : Problem520.HarperPrimeIndex y,
        if 4 ≤ p.1 then candidateEulerMixedExponent p.1 (s.filter (fun i => c i < p.1)) t
        else (s.filter (fun i => c i < p.1)).card * Real.log 4) =
        ∑ p ∈ P, if 4 ≤ p then candidateEulerMixedExponent p (s.filter (fun i => c i < p)) t
        else (s.filter (fun i => c i < p)).card * Real.log 4 by
      exact Finset.sum_coe_sort P (fun p : ℕ =>
        if 4 ≤ p then candidateEulerMixedExponent p (s.filter (fun i => c i < p)) t
        else (s.filter (fun i => c i < p)).card * Real.log 4)]
    simp only [Q, R, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp
  have hf (a : ℕ) : Q.filter (fun p => a < p) =
      (Finset.Ioc (max 3 a) y).filter Nat.Prime := by
    ext p
    simp only [Q, P, Finset.mem_filter, Nat.mem_primesBelow, Finset.mem_Ioc, max_lt_iff]
    constructor
    · rintro ⟨⟨⟨hpy, hp⟩, hp4⟩, hpa⟩
      exact ⟨⟨⟨by omega, hpa⟩, by omega⟩, hp⟩
    · rintro ⟨⟨⟨hp3, hpa⟩, hpy⟩, hp⟩
      exact ⟨⟨⟨by omega, hp⟩, by omega⟩, hpa⟩
  have hsmall : (∑ p ∈ R, (s.filter (fun i => c i < p)).card * Real.log 4) ≤
      4 * Real.log 4 * Fintype.card ι := by
    have hcard (p : ℕ) : ((s.filter (fun i => c i < p)).card : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast (Finset.card_filter_le s (fun i => c i < p))
    have hR : R.card ≤ 4 := by
      calc
        R.card ≤ (Finset.range 4).card := Finset.card_le_card (by
          intro p hp
          have hp' := (Finset.mem_filter.mp hp).2
          exact Finset.mem_range.mpr (by omega))
        _ = 4 := Finset.card_range 4
    calc
      _ ≤ ∑ _p ∈ R, (Fintype.card ι : ℝ) * Real.log 4 :=
        Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_right (hcard p) (by positivity))
      _ = (R.card : ℝ) * (Fintype.card ι * Real.log 4) := by simp
      _ ≤ 4 * (Fintype.card ι * Real.log 4) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hR) (by positivity)
      _ = _ := by ring
  have hcubic : (∑ i ∈ s, ∑ p ∈ Q.filter (fun p => c i < p),
      (Real.sqrt (p : ℝ))⁻¹ ^ 3) ≤ 2 * Fintype.card ι := by
    calc
      _ ≤ ∑ i ∈ s, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hf]
        have h := candidate_sum_prime_cubic_tail_le (y := y)
          (show 1 ≤ max 3 (c i) by omega)
        have hinv : (Real.sqrt ((max 3 (c i) : ℕ) : ℝ))⁻¹ ≤ 1 := by
          apply inv_le_one_of_one_le₀
          apply Real.le_sqrt_of_sq_le
          exact_mod_cast (show 1 ^ 2 ≤ max 3 (c i) by omega)
        linarith
      _ = _ := by simp [s]; ring
  rw [hsplit, candidate_sum_mixedEulerExponent_eq_prime_tails]
  have hdiag : (∑ i ∈ s, ∑ p ∈ Q.filter (fun p => c i < p), (p : ℝ)⁻¹) =
      ∑ i, Problem520.freshReciprocalSum (max 3 (c i)) y := by
    simp only [hf, Problem520.freshReciprocalSum, freshPrimes_eq_filter_Ioc, s]
  rw [hdiag]
  simp_rw [hf]
  have hcubic' := mul_le_mul_of_nonneg_left hcubic (by norm_num : (0 : ℝ) ≤ 4 / 3)
  simp_rw [hf] at hcubic'
  dsimp only [s] at *
  linarith

end Erdos.Problem1144
