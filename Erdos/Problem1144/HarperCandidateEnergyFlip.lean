import Erdos.Problem1144.HarperCandidateEnergyFlipArithmetic
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Set
open scoped ENNReal

namespace Erdos.Problem1144

/-- The actual squarefree log path, cut off only at the upper endpoint. -/
noncomputable def candidateSquarefreePrefixPath (ω : Omega) (B : ℝ) : ℝ → ℝ :=
  (Iic B).indicator (harperCandidateSquarefreeLogProcess ω)

theorem measurable_candidateSquarefreePrefixPath (ω : Omega) (B : ℝ) :
    Measurable (candidateSquarefreePrefixPath ω B) :=
  measurable_harperCandidateSquarefreeLogProcess.comp
    (measurable_const.prodMk measurable_id) |>.indicator measurableSet_Iic

theorem candidateSquarefreePrefixPath_memLp (ω : Omega) (B : ℝ) :
    MemLp (candidateSquarefreePrefixPath ω B) 2 := by
  apply (memLp_indicator_const (μ := volume) (s := Icc (0 : ℝ) B) 2 measurableSet_Icc (Real.exp (B / 2))
    (Or.inr isCompact_Icc.measure_lt_top.ne)).mono'
      (measurable_candidateSquarefreePrefixPath ω B).aestronglyMeasurable
  exact ae_of_all _ fun t => by
    by_cases htB : t ≤ B
    · by_cases ht : 0 ≤ t
      · simpa [candidateSquarefreePrefixPath, htB, ht, Real.norm_eq_abs]
          using candidate_squarefree_log_abs_le_exp_half ω htB
      · simp [candidateSquarefreePrefixPath, htB, harperCandidateSquarefreeLogProcess, ht]
    · simp [candidateSquarefreePrefixPath, htB]

private theorem candidate_norm_toLp_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ t, f t ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with t ht
  simp [ht, real_inner_self_eq_norm_sq]

/-- The L² norm of the literal cutoff path is exactly the established
squarefree coefficient-prefix energy. -/
theorem candidateSquarefreePrefixPath_norm_sq_eq
    (ω : Omega) {y : ℕ} (hy : 1 ≤ y) :
    ‖(candidateSquarefreePrefixPath_memLp ω (Real.log y)).toLp
      (candidateSquarefreePrefixPath ω (Real.log y))‖ ^ 2 =
        harperSquarefreeCoefficientPrefixEnergy y ω := by
  rw [candidate_norm_toLp_sq, ← candidate_squarefree_log_prefix_energy_eq ω hy,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  have h0 : ∀ᵐ t : ℝ, t ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [h0] with t ht0
  by_cases htB : t ≤ Real.log (y : ℝ)
  · by_cases ht : 0 < t
    · simp [candidateSquarefreePrefixPath, htB, ht]
    · have hneg : ¬0 ≤ t := by
        intro h
        exact ht0 (le_antisymm (le_of_not_gt ht) h)
      simp [candidateSquarefreePrefixPath, htB, ht,
        harperCandidateSquarefreeLogProcess, hneg]
  · simp [candidateSquarefreePrefixPath, htB]

private theorem candidate_cutoff_translation_eq (ω : Omega) (B d : ℝ) (hd : 0 ≤ d) :
    (Iic B).indicator (fun t => harperCandidateSquarefreeLogProcess ω (t - d)) =
      (Iic B).indicator (fun t => candidateSquarefreePrefixPath ω B (t - d)) := by
  funext t
  by_cases ht : t ≤ B
  · have htd : t - d ≤ B := by linarith
    simp [candidateSquarefreePrefixPath, ht, htd]
  · simp [ht]

private theorem candidate_cutoff_translation_memLp
    (ω : Omega) (B d : ℝ) (hd : 0 ≤ d) :
    MemLp ((Iic B).indicator
      (fun t => harperCandidateSquarefreeLogProcess ω (t - d))) 2 := by
  rw [candidate_cutoff_translation_eq ω B d hd]
  have h := (candidateSquarefreePrefixPath_memLp ω B).comp_measurePreserving
    (measurePreserving_add_right volume (-d))
  simpa only [Function.comp_apply, sub_eq_add_neg] using h.indicator measurableSet_Iic

private theorem candidate_cutoff_translation_norm_le
    (ω : Omega) (B d : ℝ) (hd : 0 ≤ d) :
    ‖(candidate_cutoff_translation_memLp ω B d hd).toLp
      ((Iic B).indicator (fun t => harperCandidateSquarefreeLogProcess ω (t - d)))‖ ≤
    ‖(candidateSquarefreePrefixPath_memLp ω B).toLp (candidateSquarefreePrefixPath ω B)‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  apply ENNReal.toReal_mono (candidateSquarefreePrefixPath_memLp ω B).2.ne
  rw [candidate_cutoff_translation_eq ω B d hd]
  apply (eLpNorm_indicator_le _).trans
  have h := eLpNorm_comp_measurePreserving
    (p := (2 : ℝ≥0∞)) (candidateSquarefreePrefixPath_memLp ω B).1
    (measurePreserving_add_right volume (-d))
  simpa only [Function.comp_apply, sub_eq_add_neg] using h.le

/-- Each single prime flip changes the literal coefficient-prefix energy
by a factor at most `49`, uniformly in the prefix cutoff and the sample. -/
theorem candidate_squarefree_prefix_energy_flip_singleton_le
    (ω : Omega) {p y : ℕ} (hp : p.Prime) (hy : 1 ≤ y) :
    harperSquarefreeCoefficientPrefixEnergy y (freshSignFlip {p} ω) ≤
      49 * harperSquarefreeCoefficientPrefixEnergy y ω := by
  let B := Real.log (y : ℝ)
  let d := Real.log (p : ℝ)
  have hd : 0 ≤ d := Real.log_nonneg (by exact_mod_cast hp.one_le)
  let a := eps ω p * Real.exp (-Real.log p / 2)
  let F := (candidateSquarefreePrefixPath_memLp ω B).toLp (candidateSquarefreePrefixPath ω B)
  let G := (candidateSquarefreePrefixPath_memLp (freshSignFlip {p} ω) B).toLp
    (candidateSquarefreePrefixPath (freshSignFlip {p} ω) B)
  let DF := (candidate_cutoff_translation_memLp ω B d hd).toLp
    ((Iic B).indicator (fun t => harperCandidateSquarefreeLogProcess ω (t - d)))
  let DG := (candidate_cutoff_translation_memLp (freshSignFlip {p} ω) B d hd).toLp
    ((Iic B).indicator (fun t =>
      harperCandidateSquarefreeLogProcess (freshSignFlip {p} ω) (t - d)))
  have heq : G + a • DG = F - a • DF := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add G (a • DG), Lp.coeFn_sub F (a • DF),
      Lp.coeFn_smul a DG, Lp.coeFn_smul a DF,
      (candidateSquarefreePrefixPath_memLp ω B).coeFn_toLp,
      (candidateSquarefreePrefixPath_memLp (freshSignFlip {p} ω) B).coeFn_toLp,
      (candidate_cutoff_translation_memLp ω B d hd).coeFn_toLp,
      (candidate_cutoff_translation_memLp (freshSignFlip {p} ω) B d hd).coeFn_toLp]
      with t hsum hsub hsmulG hsmulF hF hG hDF hDG
    rw [hsum, hsub]
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hsmulG, hsmulF]
    simp only [Pi.smul_apply]
    rw [hF, hG, hDF, hDG]
    by_cases ht : t ≤ B
    · simpa [candidateSquarefreePrefixPath, ht, smul_eq_mul, a, d]
        using candidate_squarefree_log_flip_recurrence ω hp t
    · simp [candidateSquarefreePrefixPath, ht]
  have hDF : ‖DF‖ ≤ ‖F‖ := candidate_cutoff_translation_norm_le ω B d hd
  have hDG : ‖DG‖ ≤ ‖G‖ :=
    candidate_cutoff_translation_norm_le (freshSignFlip {p} ω) B d hd
  have ha : ‖a‖ ≤ 3 / 4 := by
    simpa only [a, Real.norm_eq_abs, abs_mul, abs_eps,
      abs_of_pos (Real.exp_pos _), one_mul] using
        candidate_prime_log_translation_coefficient_le hp
  have hg : ‖G‖ ≤ ‖F‖ + ‖a‖ * ‖DF‖ + ‖a‖ * ‖DG‖ := by
    have he : G = (F - a • DF) - a • DG := by rw [← heq]; abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl) |>.trans_eq
      (by simp only [norm_smul])
  have h7 : ‖G‖ ≤ 7 * ‖F‖ := by
    have hF0 := norm_nonneg F
    have hG0 := norm_nonneg G
    have h1 := mul_le_mul ha hDF (norm_nonneg DF) (by norm_num : (0 : ℝ) ≤ 3 / 4)
    have h2 := mul_le_mul ha hDG (norm_nonneg DG) (by norm_num : (0 : ℝ) ≤ 3 / 4)
    linarith
  have hsq : ‖G‖ ^ 2 ≤ 49 * ‖F‖ ^ 2 := by nlinarith [norm_nonneg F, norm_nonneg G]
  simpa only [F, G, B, candidateSquarefreePrefixPath_norm_sq_eq _ hy] using hsq

/-- Non-prime coordinate flips leave the prefix energy unchanged. -/
theorem candidate_squarefree_prefix_energy_flip_nonprime
    (ω : Omega) {p y : ℕ} (hp : ¬p.Prime) (hy : 1 ≤ y) :
    harperSquarefreeCoefficientPrefixEnergy y (freshSignFlip {p} ω) =
      harperSquarefreeCoefficientPrefixEnergy y ω := by
  rw [← candidate_squarefree_log_prefix_energy_eq _ hy,
    ← candidate_squarefree_log_prefix_energy_eq _ hy]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  simp only [harperCandidateSquarefreeLogProcess_eq_quotient, GSquarefree]
  congr 2
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hsq : Squarefree n
  · simp only [gSquarefree_of_squarefree _ hsq]
    exact f_freshSignFlip_singleton_of_not_prime p hp ω n
  · simp [gSquarefree, hsq]

/-- Finite coordinate changes have a cutoff-independent multiplicative
energy cost. The constant is `49` per changed coordinate, including harmless
non-prime coordinates so it applies to arbitrary conditioning cylinders. -/
theorem candidate_squarefree_prefix_energy_flip_le
    (s : Finset ℕ) (ω : Omega) {y : ℕ} (hy : 1 ≤ y) :
    harperSquarefreeCoefficientPrefixEnergy y (freshSignFlip s ω) ≤
      (49 : ℝ) ^ s.card * harperSquarefreeCoefficientPrefixEnergy y ω := by
  classical
  induction s using Finset.induction_on generalizing ω with
  | empty =>
    have h : freshSignFlip ∅ ω = ω := by funext n; simp [freshSignFlip]
    simp only [h, Finset.card_empty, pow_zero, one_mul, le_refl]
  | @insert p s hp ih =>
    rw [freshSignFlip_insert_of_notMem p s hp, Finset.card_insert_of_notMem hp, pow_succ]
    have hone : harperSquarefreeCoefficientPrefixEnergy y
        (freshSignFlip {p} (freshSignFlip s ω)) ≤
        49 * harperSquarefreeCoefficientPrefixEnergy y (freshSignFlip s ω) := by
      by_cases hprime : p.Prime
      · exact candidate_squarefree_prefix_energy_flip_singleton_le _ hprime hy
      · rw [candidate_squarefree_prefix_energy_flip_nonprime _ hprime hy]
        nlinarith [harperSquarefreeCoefficientPrefixEnergy_nonneg y (freshSignFlip s ω)]
    exact hone.trans ((mul_le_mul_of_nonneg_left (ih ω) (by norm_num)).trans_eq (by ring))

/-- The reverse bound uses the same constant, because a finite flip is an
involution. This is the direction needed to transport a lower energy event. -/
theorem candidate_squarefree_prefix_energy_le_flip
    (s : Finset ℕ) (ω : Omega) {y : ℕ} (hy : 1 ≤ y) :
    harperSquarefreeCoefficientPrefixEnergy y ω ≤
      (49 : ℝ) ^ s.card * harperSquarefreeCoefficientPrefixEnergy y (freshSignFlip s ω) := by
  simpa only [freshSignFlip_freshSignFlip] using
    candidate_squarefree_prefix_energy_flip_le s (freshSignFlip s ω) hy

end Erdos.Problem1144
