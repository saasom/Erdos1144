import Erdos.Problem1144.HarperCandidateTranslationPrimeCoefficients
import Erdos.Problem1144.HarperCandidateSpectralIntegrability

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# Squarefree coefficient errors under the complete interval envelope

Only interval sums with constant-sign coefficients are compared between
models. Normalization changes are bounded separately, so no unsupported
comparison between their signed translation errors is asserted.
-/

theorem candidate_integral_finset_gSquarefree_sq_le_f_sq (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) :
    (∫ ω, (∑ n ∈ s, gSquarefree ω n) ^ 2 ∂mu) ≤
      ∫ ω, (∑ n ∈ s, f ω n) ^ 2 ∂mu := by
  have hg := integral_squarefreeWeightedSum_sq_eq s (fun _ ↦ 1) hs
  simp only [squarefreeWeightedSum, one_mul] at hg
  rw [hg, candidate_integral_finset_f_sq s hs]
  apply Finset.sum_le_sum
  intro m _
  apply Finset.sum_le_sum
  intro n _
  split_ifs
  · exact le_rfl
  · exact squareIndicator_nonneg _

theorem candidate_GSquarefree_sub_eq_sum_Ioc (ω : Omega) {M N : ℕ} (hMN : M ≤ N) :
    GSquarefree ω N - GSquarefree ω M = ∑ n ∈ Finset.Ioc M N, gSquarefree ω n := by
  have hd : Finset.Icc 1 N \ Finset.Icc 1 M = Finset.Ioc M N := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hs := Finset.sum_sdiff (s₁ := Finset.Icc 1 M) (f := gSquarefree ω)
    (Finset.Icc_subset_Icc_right hMN)
  rw [hd] at hs
  unfold GSquarefree
  linarith

/-- Squarefree interval energies are bounded by the complete-model interval
energies, since only the squarefree diagonal survives in the first model. -/
theorem candidate_integral_GSquarefree_sub_sq_le_S_sub_sq {M N : ℕ} (hMN : M ≤ N) :
    (∫ ω, (GSquarefree ω N - GSquarefree ω M) ^ 2 ∂mu) ≤
      ∫ ω, (S ω N - S ω M) ^ 2 ∂mu := by
  simp_rw [candidate_GSquarefree_sub_eq_sum_Ioc _ hMN, candidate_S_sub_eq_sum_Ioc _ hMN]
  exact candidate_integral_finset_gSquarefree_sq_le_f_sq _
    (fun n hn ↦ by have := (Finset.mem_Ioc.mp hn).1; omega)

theorem candidate_integrable_GSquarefree_sub_sq {M N : ℕ} (hMN : M ≤ N) :
    Integrable (fun ω ↦ (GSquarefree ω N - GSquarefree ω M) ^ 2) mu := by
  simp_rw [candidate_GSquarefree_sub_eq_sum_Ioc _ hMN]
  simpa only [squarefreeWeightedSum, one_mul] using
    integrable_squarefreeWeightedSum_sq (Finset.Ioc M N) (fun _ ↦ 1)

theorem candidate_integrable_squarefreeLog (t : ℝ) :
    Integrable (fun ω ↦ harperCandidateSquarefreeLogProcess ω t) mu := by
  simpa only [pow_one] using candidate_integrable_squarefreeLog_pow t 1

theorem candidate_integrable_squarefreeLog_difference_sq (u v : ℝ) :
    Integrable (fun ω ↦ (harperCandidateSquarefreeLogProcess ω v -
      harperCandidateSquarefreeLogProcess ω u) ^ 2) mu := by
  have hu := (memLp_two_iff_integrable_sq
    (candidate_integrable_squarefreeLog u).aestronglyMeasurable).mpr
      (candidate_integrable_squarefreeLog_pow u 2)
  have hv := (memLp_two_iff_integrable_sq
    (candidate_integrable_squarefreeLog v).aestronglyMeasurable).mpr
      (candidate_integrable_squarefreeLog_pow v 2)
  exact (hv.sub hu).integrable_sq

/-- A squarefree translation is bounded by the same complete interval
energy; its separate normalization error uses the stronger variance bound one. -/
theorem candidate_squarefreeLog_difference_sq_le_window {a u v b : ℝ}
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    (∫ ω, (harperCandidateSquarefreeLogProcess ω v -
      harperCandidateSquarefreeLogProcess ω u) ^ 2 ∂mu) ≤
      2 * candidateLogWindowSecondMoment a b + (b - a) ^ 2 / 2 := by
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
    (GSquarefree ω ⌊Real.exp v⌋₊ - GSquarefree ω ⌊Real.exp u⌋₊) / Real.exp (u / 2)
  have hMN : ⌊Real.exp u⌋₊ ≤ ⌊Real.exp v⌋₊ := Nat.floor_mono (Real.exp_le_exp.mpr huv)
  have hid (ω : Omega) :
      harperCandidateSquarefreeLogProcess ω v - harperCandidateSquarefreeLogProcess ω u =
        r * J ω + (r - 1) * harperCandidateSquarefreeLogProcess ω u := by
    simp only [harperCandidateSquarefreeLogProcess_eq_quotient, J, r]
    have he : Real.exp (-(v - u) / 2) * Real.exp (v / 2) = Real.exp (u / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [neg_div] at he
    field_simp
    rw [← he]
    ring
  have hp (ω : Omega) :
      (harperCandidateSquarefreeLogProcess ω v - harperCandidateSquarefreeLogProcess ω u) ^ 2 ≤
        2 * J ω ^ 2 + (b - a) ^ 2 / 2 * harperCandidateSquarefreeLogProcess ω u ^ 2 := by
    rw [hid]
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    have hJ := mul_le_mul_of_nonneg_right hr2 (sq_nonneg (J ω))
    have hA := mul_le_mul_of_nonneg_right hsq
      (sq_nonneg (harperCandidateSquarefreeLogProcess ω u))
    nlinarith [sq_nonneg (r * J ω - (r - 1) * harperCandidateSquarefreeLogProcess ω u)]
  have hJi : Integrable (fun ω ↦ J ω ^ 2) mu := by
    simp only [J, div_pow]
    exact (candidate_integrable_GSquarefree_sub_sq hMN).div_const _
  have hAi := candidate_integrable_squarefreeLog_pow u 2
  have hi := integral_mono (candidate_integrable_squarefreeLog_difference_sq u v)
    ((hJi.const_mul 2).add (hAi.const_mul ((b - a) ^ 2 / 2))) hp
  change _ ≤ ∫ ω, 2 * J ω ^ 2 +
    (b - a) ^ 2 / 2 * harperCandidateSquarefreeLogProcess ω u ^ 2 ∂mu at hi
  rw [integral_add (hJi.const_mul 2) (hAi.const_mul ((b - a) ^ 2 / 2)),
    integral_const_mul, integral_const_mul] at hi
  have hJ : (∫ ω, J ω ^ 2 ∂mu) ≤ candidateLogWindowSecondMoment a b := by
    calc
      _ ≤ candidateLogWindowSecondMoment u v := by
        simp only [J, candidateLogWindowSecondMoment, div_pow, integral_div]
        exact div_le_div_of_nonneg_right (candidate_integral_GSquarefree_sub_sq_le_S_sub_sq hMN)
          (sq_nonneg _)
      _ ≤ _ := candidateLogWindowSecondMoment_mono hau huv hvb
  have hV := mul_le_mul_of_nonneg_left (candidate_integral_squarefreeLog_sq_le_one u)
    (div_nonneg (sq_nonneg (b - a)) (by norm_num : (0 : ℝ) ≤ 2))
  linarith

theorem candidate_integrable_squarefreeLogCoefficient_difference_sq (x y u v : ℝ) :
    Integrable (fun ω ↦ (harperCandidateSquarefreeLogProcess ω u / Real.sqrt x -
      harperCandidateSquarefreeLogProcess ω v / Real.sqrt y) ^ 2) mu := by
  have hu := (memLp_two_iff_integrable_sq
    (candidate_integrable_squarefreeLog u).aestronglyMeasurable).mpr
    (candidate_integrable_squarefreeLog_pow u 2)
  have hv := (memLp_two_iff_integrable_sq
    (candidate_integrable_squarefreeLog v).aestronglyMeasurable).mpr
    (candidate_integrable_squarefreeLog_pow v 2)
  simpa only [div_eq_mul_inv] using
    ((hu.mul_const (Real.sqrt x)⁻¹).sub (hv.mul_const (Real.sqrt y)⁻¹)).integrable_sq

/-- Coefficient replacement splits into the complete-process translation
error and the deterministic inverse-square-root variation. -/
theorem candidate_integral_squarefreeLogCoefficient_difference_sq_le
    {T x y : ℝ} (hT : 0 < T) (hTx : T ≤ x) (hxy : x ≤ y) (u v : ℝ) :
    (∫ ω, (harperCandidateSquarefreeLogProcess ω u / Real.sqrt x -
      harperCandidateSquarefreeLogProcess ω v / Real.sqrt y) ^ 2 ∂mu) ≤
      (2 / T) * (∫ ω, (harperCandidateSquarefreeLogProcess ω u -
        harperCandidateSquarefreeLogProcess ω v) ^ 2 ∂mu) +
          (2 * (y - x) ^ 2 / T ^ 3) * (∫ ω, harperCandidateSquarefreeLogProcess ω v ^ 2 ∂mu) := by
  have hx : 0 < x := hT.trans_le hTx
  have hy : 0 < y := hx.trans_le hxy
  have hb := candidate_inv_sqrt_sub_sq_le hT hTx hxy
  have hi : 1 / x ≤ 1 / T := one_div_le_one_div_of_le hT hTx
  have hp (ω : Omega) :
      (harperCandidateSquarefreeLogProcess ω u / Real.sqrt x -
        harperCandidateSquarefreeLogProcess ω v / Real.sqrt y) ^ 2 ≤
      (2 / T) * (harperCandidateSquarefreeLogProcess ω u -
        harperCandidateSquarefreeLogProcess ω v) ^ 2 +
        (2 * (y - x) ^ 2 / T ^ 3) * harperCandidateSquarefreeLogProcess ω v ^ 2 := by
    let A := harperCandidateSquarefreeLogProcess ω u - harperCandidateSquarefreeLogProcess ω v
    let B := harperCandidateSquarefreeLogProcess ω v
    have hid : harperCandidateSquarefreeLogProcess ω u / Real.sqrt x -
        harperCandidateSquarefreeLogProcess ω v / Real.sqrt y =
          A / Real.sqrt x + B * (1 / Real.sqrt x - 1 / Real.sqrt y) := by
      dsimp only [A, B]
      ring
    rw [hid]
    have hAB := sq_nonneg (A / Real.sqrt x - B * (1 / Real.sqrt x - 1 / Real.sqrt y))
    have hA := mul_le_mul_of_nonneg_right hi (sq_nonneg A)
    have hB := mul_le_mul_of_nonneg_right hb (sq_nonneg B)
    have hAsq : (A / Real.sqrt x) ^ 2 = (1 / x) * A ^ 2 := by
      rw [div_pow, Real.sq_sqrt hx.le]
      ring
    have hpre : (A / Real.sqrt x + B * (1 / Real.sqrt x - 1 / Real.sqrt y)) ^ 2 ≤
        2 * (A / Real.sqrt x) ^ 2 + 2 * (1 / Real.sqrt x - 1 / Real.sqrt y) ^ 2 * B ^ 2 := by
      nlinarith
    rw [hAsq] at hpre
    change _ ≤ (2 / T) * A ^ 2 + (2 * (y - x) ^ 2 / T ^ 3) * B ^ 2
    simp only [div_eq_mul_inv] at hA hB hpre ⊢
    nlinarith
  have hD : Integrable (fun ω ↦
      (harperCandidateSquarefreeLogProcess ω u -
        harperCandidateSquarefreeLogProcess ω v) ^ 2) mu := by
    exact candidate_integrable_squarefreeLog_difference_sq v u
  have hV := candidate_integrable_squarefreeLog_pow v 2
  have hcoeff := candidate_integrable_squarefreeLogCoefficient_difference_sq x y u v
  have hint := integral_mono hcoeff
    ((hD.const_mul (2 / T)).add (hV.const_mul (2 * (y - x) ^ 2 / T ^ 3))) hp
  change _ ≤ ∫ ω, (2 / T) * (harperCandidateSquarefreeLogProcess ω u -
    harperCandidateSquarefreeLogProcess ω v) ^ 2 +
    (2 * (y - x) ^ 2 / T ^ 3) * harperCandidateSquarefreeLogProcess ω v ^ 2 ∂mu at hint
  rw [integral_add (hD.const_mul (2 / T)) (hV.const_mul (2 * (y - x) ^ 2 / T ^ 3)),
    integral_const_mul, integral_const_mul] at hint
  exact hint

/-- The squarefree model satisfies the complete-model coefficient envelope.
The small normalization term uses `E m² ≤ 1`; its displayed enlargement by
`1+L` aligns exactly with the common prime/white-bin bounds. -/
theorem candidate_squarefreeLogCoefficient_difference_sq_le_window
    {T x y d a u v b L : ℝ} (hT : 0 < T) (hTx : T ≤ x) (hxy : x ≤ y)
    (hd : y - x ≤ d) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (_hbL : b ≤ L) (hL : 0 ≤ L) :
    (∫ ω, (harperCandidateSquarefreeLogProcess ω v / Real.sqrt x -
      harperCandidateSquarefreeLogProcess ω u / Real.sqrt y) ^ 2 ∂mu) ≤
      (4 / T) * candidateLogWindowSecondMoment a b +
        ((b - a) ^ 2 / T + 2 * d ^ 2 / T ^ 3) * (1 + L) := by
  have hcoeff := candidate_integral_squarefreeLogCoefficient_difference_sq_le hT hTx hxy v u
  have hdiff := candidate_squarefreeLog_difference_sq_le_window hau huv hvb
  have hV := candidate_integral_squarefreeLog_sq_le_one u
  have hV0 : 0 ≤ ∫ ω, harperCandidateSquarefreeLogProcess ω u ^ 2 ∂mu :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hlen2 : (y - x) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (sub_nonneg.mpr hxy) hd 2
  have hdm := mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ 2 / T)
  have hVm := mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ 2 * d ^ 2 / T ^ 3)
  have hlenm := mul_le_mul_of_nonneg_right hlen2
    (by positivity : 0 ≤ 2 / T ^ 3 * (∫ ω, harperCandidateSquarefreeLogProcess ω u ^ 2 ∂mu))
  have hmore : (b - a) ^ 2 / T + 2 * d ^ 2 / T ^ 3 ≤
      ((b - a) ^ 2 / T + 2 * d ^ 2 / T ^ 3) * (1 + L) := by
    exact le_mul_of_one_le_right (by positivity) (by linarith)
  simp only [div_eq_mul_inv] at hcoeff hdm hVm hlenm hmore ⊢
  nlinarith

theorem candidate_sum_weighted_squarefreeLogCoefficient_difference_sq_le
    {ι : Type*} (s : ℕ → Finset ι) (weight x y u v : ℕ → ι → ℝ)
    {a L h C T d : ℝ} {n k : ℕ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hT : 0 < T) (hC : 0 ≤ C)
    (hcover : a + ((n + k : ℕ) : ℝ) * h ≤ L)
    (hw : ∀ j ∈ Finset.range n, ∀ i ∈ s j, 0 ≤ weight j i)
    (hmass : ∀ j ∈ Finset.range n, (∑ i ∈ s j, weight j i) ≤ C * h)
    (hTx : ∀ j ∈ Finset.range n, ∀ i ∈ s j, T ≤ x j i)
    (hxy : ∀ j ∈ Finset.range n, ∀ i ∈ s j, x j i ≤ y j i)
    (hd : ∀ j ∈ Finset.range n, ∀ i ∈ s j, y j i - x j i ≤ d)
    (hleft : ∀ j ∈ Finset.range n, ∀ i ∈ s j, a + (j : ℝ) * h ≤ u j i)
    (hordered : ∀ j ∈ Finset.range n, ∀ i ∈ s j, u j i ≤ v j i)
    (hright : ∀ j ∈ Finset.range n, ∀ i ∈ s j,
      v j i ≤ a + ((j + k : ℕ) : ℝ) * h) :
    (∑ j ∈ Finset.range n, ∑ i ∈ s j, weight j i *
      (∫ ω, (harperCandidateSquarefreeLogProcess ω (v j i) / Real.sqrt (x j i) -
        harperCandidateSquarefreeLogProcess ω (u j i) / Real.sqrt (y j i)) ^ 2 ∂mu)) ≤
      C * ((4 / T) * (k : ℝ) * h *
        (1 + (n : ℝ) * h * Real.exp ((k : ℝ) * h)) * (1 + L) +
          (((k : ℝ) * h) ^ 2 / T + 2 * d ^ 2 / T ^ 3) * ((n : ℝ) * h) * (1 + L)) := by
  let I : ℕ → ℝ := fun j ↦ candidateLogWindowSecondMoment
    (a + (j : ℝ) * h) (a + ((j + k : ℕ) : ℝ) * h)
  let R := (((k : ℝ) * h) ^ 2 / T + 2 * d ^ 2 / T ^ 3) * (1 + L)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hpoint (j : ℕ) (hj : j ∈ Finset.range n) (i : ι) (hi : i ∈ s j) :
      (∫ ω, (harperCandidateSquarefreeLogProcess ω (v j i) / Real.sqrt (x j i) -
        harperCandidateSquarefreeLogProcess ω (u j i) / Real.sqrt (y j i)) ^ 2 ∂mu) ≤
          (4 / T) * I j + R := by
    have hbL : a + ((j + k : ℕ) : ℝ) * h ≤ L := by
      have hjn : j + k ≤ n + k := by have := Finset.mem_range.mp hj; omega
      have hjnR : ((j + k : ℕ) : ℝ) ≤ (n + k : ℕ) := by exact_mod_cast hjn
      have hm := mul_le_mul_of_nonneg_right hjnR hh
      linarith
    have hp := candidate_squarefreeLogCoefficient_difference_sq_le_window hT
      (hTx j hj i hi) (hxy j hj i hi) (hd j hj i hi)
      (hleft j hj i hi) (hordered j hj i hi) (hright j hj i hi) hbL hL
    have hlen : (a + ((j + k : ℕ) : ℝ) * h) - (a + (j : ℝ) * h) =
        (k : ℝ) * h := by push_cast; ring
    simpa only [hlen] using hp
  have hbin (j : ℕ) (hj : j ∈ Finset.range n) :
      (∑ i ∈ s j, weight j i * (∫ ω,
        (harperCandidateSquarefreeLogProcess ω (v j i) / Real.sqrt (x j i) -
          harperCandidateSquarefreeLogProcess ω (u j i) / Real.sqrt (y j i)) ^ 2 ∂mu)) ≤
            C * h * ((4 / T) * I j + R) := by
    calc
      _ ≤ ∑ i ∈ s j, weight j i * ((4 / T) * I j + R) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hpoint j hj i hi) (hw j hj i hi)
      _ = (∑ i ∈ s j, weight j i) * ((4 / T) * I j + R) := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hmass j hj)
        (add_nonneg (mul_nonneg (by positivity) (candidateLogWindowSecondMoment_nonneg _ _)) hR)
  have hsum := Finset.sum_le_sum (s := Finset.range n) hbin
  have heq : (∑ j ∈ Finset.range n, C * h * ((4 / T) * I j + R)) =
      C * ((4 / T) * (h * ∑ j ∈ Finset.range n, I j) + R * ((n : ℝ) * h)) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [heq] at hsum
  have hdisc := candidate_sum_logWindowSecondMoment_le_mesh hh hL hcover
  change h * (∑ j ∈ Finset.range n, I j) ≤ _ at hdisc
  have hm := mul_le_mul_of_nonneg_left hdisc (by positivity : 0 ≤ C * (4 / T))
  dsimp only [R] at hsum
  nlinarith

end Erdos.Problem1144
