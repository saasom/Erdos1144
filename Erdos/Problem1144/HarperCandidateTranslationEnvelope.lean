import Erdos.Problem1144.HarperCandidateTranslationDiscrete

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# Expected-square envelopes inside logarithmic bins

All interval comparisons below are comparisons of expectations. Nonnegative
complete-model pair correlations make the expected square of an interval
sum monotone under enlargement, even though the signed sums themselves need
not be monotone.
-/

theorem candidate_integral_finset_f_sq (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) :
    (∫ ω, (∑ n ∈ s, f ω n) ^ 2 ∂mu) =
      ∑ m ∈ s, ∑ n ∈ s, squareIndicator (m * n) := by
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro n hn
      exact integral_f_mul_f_eq_squareIndicator (hs m hm) (hs n hn)
    · intro n _
      exact integrable_f_mul_f m n
  · intro m _
    exact integrable_finset_sum _ fun n _ ↦ integrable_f_mul_f m n

theorem candidate_integral_finset_f_sq_mono {s t : Finset ℕ}
    (hst : s ⊆ t) (ht : ∀ n ∈ t, 1 ≤ n) :
    (∫ ω, (∑ n ∈ s, f ω n) ^ 2 ∂mu) ≤
      ∫ ω, (∑ n ∈ t, f ω n) ^ 2 ∂mu := by
  rw [candidate_integral_finset_f_sq s (fun n hn ↦ ht n (hst hn)),
    candidate_integral_finset_f_sq t ht]
  calc
    _ ≤ ∑ m ∈ s, ∑ n ∈ t, squareIndicator (m * n) := by
      apply Finset.sum_le_sum
      intro m _
      exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun n _ _ ↦ squareIndicator_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hst
      (fun m _ _ ↦ Finset.sum_nonneg fun n _ ↦ squareIndicator_nonneg _)

theorem candidate_S_sub_eq_sum_Ioc (ω : Omega) {M N : ℕ} (hMN : M ≤ N) :
    S ω N - S ω M = ∑ n ∈ Finset.Ioc M N, f ω n := by
  have hd : Finset.Icc 1 N \ Finset.Icc 1 M = Finset.Ioc M N := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hs := Finset.sum_sdiff (s₁ := Finset.Icc 1 M) (f := f ω) (Finset.Icc_subset_Icc_right hMN)
  rw [hd] at hs
  unfold S
  linarith

/-- Enlarging a natural-number interval enlarges its expected squared sum. -/
theorem candidate_integral_S_sub_sq_mono {A M N B : ℕ}
    (hAM : A ≤ M) (hMN : M ≤ N) (hNB : N ≤ B) :
    (∫ ω, (S ω N - S ω M) ^ 2 ∂mu) ≤
      ∫ ω, (S ω B - S ω A) ^ 2 ∂mu := by
  simp_rw [candidate_S_sub_eq_sum_Ioc _ hMN,
    candidate_S_sub_eq_sum_Ioc _ (hAM.trans (hMN.trans hNB))]
  exact candidate_integral_finset_f_sq_mono (Finset.Ioc_subset_Ioc hAM hNB)
    (fun n hn ↦ by have := (Finset.mem_Ioc.mp hn).1; omega)

/-- The normalization may also be moved to the earlier enclosing endpoint. -/
theorem candidateLogWindowSecondMoment_mono {a u v b : ℝ}
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    candidateLogWindowSecondMoment u v ≤ candidateLogWindowSecondMoment a b := by
  unfold candidateLogWindowSecondMoment
  simp_rw [div_pow, integral_div]
  have hmono := candidate_integral_S_sub_sq_mono
    (Nat.floor_mono (Real.exp_le_exp.mpr hau))
    (Nat.floor_mono (Real.exp_le_exp.mpr huv))
    (Nat.floor_mono (Real.exp_le_exp.mpr hvb))
  apply div_le_div₀ (integral_nonneg (fun _ ↦ sq_nonneg _)) hmono
    (sq_pos_of_pos (Real.exp_pos _))
  exact pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith)) 2

theorem candidate_integrable_S_sub_sq (M N : ℕ) :
    Integrable (fun ω ↦ (S ω N - S ω M) ^ 2) mu := by
  have hN := (memLp_two_iff_integrable_sq (measurable_S N).aestronglyMeasurable).mpr
    (integrable_S_sq N)
  have hM := (memLp_two_iff_integrable_sq (measurable_S M).aestronglyMeasurable).mpr
    (integrable_S_sq M)
  exact (hN.sub hM).integrable_sq

/-- A uniform normalized-process replacement bound anywhere inside one
logarithmic window. This includes the jump at zero. -/
theorem candidate_logProcess_difference_sq_le_window {a u v b : ℝ}
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    (∫ ω, (harperCandidateLogProcess ω v - harperCandidateLogProcess ω u) ^ 2 ∂mu) ≤
      2 * candidateLogWindowSecondMoment a b + (b - a) ^ 2 / 2 * candidateLogSecondMoment u := by
  let r := Real.exp (-(v - u) / 2)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hrd : 1 - r ≤ (v - u) / 2 := by
    have he := Real.add_one_le_exp (-(v - u) / 2)
    dsimp only [r]
    linarith
  have hsq : (r - 1) ^ 2 ≤ (b - a) ^ 2 / 4 := by
    have hlen : 0 ≤ b - a := by linarith
    have hsub : 0 ≤ 1 - r := by linarith
    have hmax : 1 - r ≤ (b - a) / 2 := by linarith
    nlinarith [sq_nonneg ((b - a) / 2 - (1 - r))]
  let J : Omega → ℝ := fun ω ↦
    (S ω ⌊Real.exp v⌋₊ - S ω ⌊Real.exp u⌋₊) / Real.exp (u / 2)
  have hid (ω : Omega) :
      harperCandidateLogProcess ω v - harperCandidateLogProcess ω u =
        r * J ω + (r - 1) * harperCandidateLogProcess ω u := by
    simp only [candidate_logProcess_eq_S_div_exp, J, r]
    have he : Real.exp (-(v - u) / 2) * Real.exp (v / 2) = Real.exp (u / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [neg_div] at he
    field_simp
    rw [← he]
    ring
  have hp (ω : Omega) :
      (harperCandidateLogProcess ω v - harperCandidateLogProcess ω u) ^ 2 ≤
        2 * J ω ^ 2 + (b - a) ^ 2 / 2 * harperCandidateLogProcess ω u ^ 2 := by
    rw [hid]
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    have hJ := mul_le_mul_of_nonneg_right hr2 (sq_nonneg (J ω))
    have hA := mul_le_mul_of_nonneg_right hsq (sq_nonneg (harperCandidateLogProcess ω u))
    nlinarith [sq_nonneg (r * J ω - (r - 1) * harperCandidateLogProcess ω u)]
  have hJi : Integrable (fun ω ↦ J ω ^ 2) mu := by
    simp only [J, div_pow]
    exact (candidate_integrable_S_sub_sq _ _).div_const _
  have hAi := candidate_integrable_logProcess_sq u
  have hDi : Integrable (fun ω ↦
      (harperCandidateLogProcess ω v - harperCandidateLogProcess ω u) ^ 2) mu := by
    simpa only [show u + (v - u) = v by ring] using
      candidate_integrable_logProcess_translation_sq (v - u) u
  have hi := integral_mono hDi ((hJi.const_mul 2).add (hAi.const_mul ((b - a) ^ 2 / 2))) hp
  change _ ≤ ∫ ω, 2 * J ω ^ 2 + (b - a) ^ 2 / 2 * harperCandidateLogProcess ω u ^ 2 ∂mu at hi
  rw [integral_add (hJi.const_mul 2) (hAi.const_mul ((b - a) ^ 2 / 2)),
    integral_const_mul, integral_const_mul] at hi
  have hwin := candidateLogWindowSecondMoment_mono hau huv hvb
  change (∫ ω, J ω ^ 2 ∂mu) ≤ candidateLogWindowSecondMoment a b at hwin
  change _ ≤ 2 * candidateLogWindowSecondMoment a b + (b - a) ^ 2 / 2 * (∫ ω, _ ∂mu)
  linarith

/-- Uniform arithmetic coefficient replacement for arbitrary nonnegative
weighted samples within each logarithmic bin. For prime samples the mass
hypothesis is supplied by the logarithmic prime-bin estimate. -/
theorem candidate_sum_weighted_logProcess_difference_sq_le
    {ι : Type*} (s : ℕ → Finset ι) (weight u v : ℕ → ι → ℝ)
    {a L h C : ℝ} {n k : ℕ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hcover : a + ((n + k : ℕ) : ℝ) * h ≤ L)
    (hw : ∀ j ∈ Finset.range n, ∀ i ∈ s j, 0 ≤ weight j i)
    (hmass : ∀ j ∈ Finset.range n, (∑ i ∈ s j, weight j i) ≤ C * h)
    (hleft : ∀ j ∈ Finset.range n, ∀ i ∈ s j, a + (j : ℝ) * h ≤ u j i)
    (hordered : ∀ j ∈ Finset.range n, ∀ i ∈ s j, u j i ≤ v j i)
    (hright : ∀ j ∈ Finset.range n, ∀ i ∈ s j,
      v j i ≤ a + ((j + k : ℕ) : ℝ) * h) (hC : 0 ≤ C) :
    (∑ j ∈ Finset.range n, ∑ i ∈ s j, weight j i *
      (∫ ω, (harperCandidateLogProcess ω (v j i) -
        harperCandidateLogProcess ω (u j i)) ^ 2 ∂mu)) ≤
      C * (2 * (k : ℝ) * h * (1 + (n : ℝ) * h * Real.exp ((k : ℝ) * h)) * (1 + L) +
        ((k : ℝ) * h) ^ 2 / 2 * ((n : ℝ) * h) * (1 + L)) := by
  let I : ℕ → ℝ := fun j ↦ candidateLogWindowSecondMoment
    (a + (j : ℝ) * h) (a + ((j + k : ℕ) : ℝ) * h)
  let R := ((k : ℝ) * h) ^ 2 / 2 * (1 + L)
  have hR : 0 ≤ R := mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) (by linarith)
  have hpoint (j : ℕ) (hj : j ∈ Finset.range n) (i : ι) (hi : i ∈ s j) :
      (∫ ω, (harperCandidateLogProcess ω (v j i) -
        harperCandidateLogProcess ω (u j i)) ^ 2 ∂mu) ≤ 2 * I j + R := by
    have hp := candidate_logProcess_difference_sq_le_window
      (hleft j hj i hi) (hordered j hj i hi) (hright j hj i hi)
    have hlen : (a + ((j + k : ℕ) : ℝ) * h) - (a + (j : ℝ) * h) =
        (k : ℝ) * h := by push_cast; ring
    rw [hlen] at hp
    have hbound : candidateLogSecondMoment (u j i) ≤ 1 + L := by
      apply candidateLogSecondMoment_le_of_le hL
      have hjn : j + k ≤ n + k := by have := Finset.mem_range.mp hj; omega
      have hjnR : ((j + k : ℕ) : ℝ) ≤ (n + k : ℕ) := by exact_mod_cast hjn
      have hm := mul_le_mul_of_nonneg_right hjnR hh
      linarith [hordered j hj i hi, hright j hj i hi]
    have hm := mul_le_mul_of_nonneg_left hbound
      (div_nonneg (sq_nonneg ((k : ℝ) * h)) (by norm_num : (0 : ℝ) ≤ 2))
    dsimp only [I, R]
    linarith
  have hbin (j : ℕ) (hj : j ∈ Finset.range n) :
      (∑ i ∈ s j, weight j i * (∫ ω, (harperCandidateLogProcess ω (v j i) -
        harperCandidateLogProcess ω (u j i)) ^ 2 ∂mu)) ≤ C * h * (2 * I j + R) := by
    calc
      _ ≤ ∑ i ∈ s j, weight j i * (2 * I j + R) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hpoint j hj i hi) (hw j hj i hi)
      _ = (∑ i ∈ s j, weight j i) * (2 * I j + R) := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hmass j hj)
        (by have hI := candidateLogWindowSecondMoment_nonneg (a + (j : ℝ) * h)
              (a + ((j + k : ℕ) : ℝ) * h)
            change 0 ≤ 2 * I j + R
            change 0 ≤ I j at hI
            linarith)
  have hsum := Finset.sum_le_sum (s := Finset.range n) hbin
  have heq : (∑ j ∈ Finset.range n, C * h * (2 * I j + R)) =
      C * (2 * (h * ∑ j ∈ Finset.range n, I j) + R * ((n : ℝ) * h)) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [heq] at hsum
  have hd := candidate_sum_logWindowSecondMoment_le_mesh hh hL hcover
  change h * (∑ j ∈ Finset.range n, I j) ≤ _ at hd
  have hm := mul_le_mul_of_nonneg_left hd (mul_nonneg hC (by norm_num : (0 : ℝ) ≤ 2))
  dsimp only [R] at hsum
  nlinarith

end Erdos.Problem1144
