import Erdos.Problem1144.HarperCandidateLaplaceIntegrability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set Filter
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# A quantitative mean-square translation estimate for the complete model

Nonnegative pair correlations imply a covariance lower bound for nested
partial sums. After exponential normalization, integrating the resulting
second-moment difference telescopes. This gives a sufficient polynomial-loss
version of the candidate's translation estimate without counting nearby
square pairs individually.
-/

theorem candidate_integral_S_mul_S (M N : ℕ) :
    (∫ ω, S ω M * S ω N ∂mu) =
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, squareIndicator (m * n) := by
  unfold S
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro n hn
      exact integral_f_mul_f_eq_squareIndicator
        (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1
    · intro n _
      exact integrable_f_mul_f m n
  · intro m _
    exact integrable_finset_sum _ fun n _ ↦ integrable_f_mul_f m n

/-- Every new complete-model pair correlation is nonnegative. -/
theorem candidate_integral_S_sq_le_cross {M N : ℕ} (hMN : M ≤ N) :
    (∫ ω, S ω M ^ 2 ∂mu) ≤ ∫ ω, S ω N * S ω M ∂mu := by
  simp_rw [pow_two]
  rw [candidate_integral_S_mul_S, candidate_integral_S_mul_S]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hMN)
  intro n _ _
  exact Finset.sum_nonneg fun m _ ↦ squareIndicator_nonneg _

/-- The zero extension at negative time agrees with the literal summatory
formula, because `floor(exp t)=0` there. -/
theorem candidate_logProcess_eq_S_div_exp (ω : Omega) (t : ℝ) :
    harperCandidateLogProcess ω t = S ω ⌊Real.exp t⌋₊ / Real.exp (t / 2) := by
  by_cases ht : 0 ≤ t
  · simp [harperCandidateLogProcess, ht]
  · have hfloor : ⌊Real.exp t⌋₊ = 0 :=
      Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr (lt_of_not_ge ht))
    simp [harperCandidateLogProcess, ht, hfloor, S]

noncomputable def candidateLogSecondMoment (t : ℝ) : ℝ :=
  ∫ ω, harperCandidateLogProcess ω t ^ 2 ∂mu

noncomputable def candidateLogTranslationSecondMoment (h t : ℝ) : ℝ :=
  ∫ ω, (harperCandidateLogProcess ω (t + h) - harperCandidateLogProcess ω t) ^ 2 ∂mu

theorem candidateLogSecondMoment_nonneg (t : ℝ) : 0 ≤ candidateLogSecondMoment t :=
  integral_nonneg fun _ ↦ sq_nonneg _

theorem candidateLogSecondMoment_eq_zero_of_neg {t : ℝ} (ht : t < 0) :
    candidateLogSecondMoment t = 0 := by
  simp [candidateLogSecondMoment, harperCandidateLogProcess, not_le.mpr ht]

theorem candidateLogSecondMoment_le_of_le {t L : ℝ} (hL : 0 ≤ L) (htL : t ≤ L) :
    candidateLogSecondMoment t ≤ 1 + L := by
  by_cases ht : 0 ≤ t
  · exact (candidate_integral_logProcess_sq_le ht).trans (by linarith)
  · rw [candidateLogSecondMoment_eq_zero_of_neg (lt_of_not_ge ht)]
    linarith

theorem candidate_integrable_logProcess_mul (u v : ℝ) :
    Integrable (fun ω ↦ harperCandidateLogProcess ω u * harperCandidateLogProcess ω v) mu := by
  simp_rw [candidate_logProcess_eq_S_div_exp, div_mul_div_comm]
  exact (integrable_S_mul_S _ _).div_const _

theorem candidate_integrable_logProcess_translation_sq (h t : ℝ) :
    Integrable (fun ω ↦ (harperCandidateLogProcess ω (t + h) -
      harperCandidateLogProcess ω t) ^ 2) mu := by
  have hu := (memLp_two_iff_integrable_sq
    (candidate_integrable_logProcess (t + h)).aestronglyMeasurable).mpr
      (candidate_integrable_logProcess_sq (t + h))
  have hv := (memLp_two_iff_integrable_sq
    (candidate_integrable_logProcess t).aestronglyMeasurable).mpr
      (candidate_integrable_logProcess_sq t)
  exact (hu.sub hv).integrable_sq

/-- Normalized nested-sum covariance is at least the old variance times the
deterministic exponential decay. -/
theorem candidate_log_covariance_lower {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    Real.exp (-h / 2) * candidateLogSecondMoment t ≤
      ∫ ω, harperCandidateLogProcess ω (t + h) * harperCandidateLogProcess ω t ∂mu := by
  have hMN : ⌊Real.exp t⌋₊ ≤ ⌊Real.exp (t + h)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr (le_add_of_nonneg_right hh))
  have hc := candidate_integral_S_sq_le_cross hMN
  unfold candidateLogSecondMoment
  simp_rw [candidate_logProcess_eq_S_div_exp, div_mul_div_comm, div_pow]
  rw [integral_div, integral_div]
  have hexp : Real.exp ((t + h) / 2) = Real.exp (t / 2) * Real.exp (h / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hd : 0 < Real.exp (t / 2) * Real.exp (h / 2) * Real.exp (t / 2) := by positivity
  apply (le_div_iff₀ hd).mpr
  calc
    Real.exp (-h / 2) * ((∫ ω, S ω ⌊Real.exp t⌋₊ ^ 2 ∂mu) /
        Real.exp (t / 2) ^ 2) *
        (Real.exp (t / 2) * Real.exp (h / 2) * Real.exp (t / 2)) =
        ∫ ω, S ω ⌊Real.exp t⌋₊ ^ 2 ∂mu := by
      rw [show -h / 2 = -(h / 2) by ring, Real.exp_neg]
      field_simp
    _ ≤ _ := hc

/-- The translation moment is bounded by a telescoping variance difference
plus `h` times the old variance. -/
theorem candidateLogTranslationSecondMoment_le {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    candidateLogTranslationSecondMoment h t ≤
      candidateLogSecondMoment (t + h) - candidateLogSecondMoment t +
        h * candidateLogSecondMoment t := by
  have heq : candidateLogTranslationSecondMoment h t =
      candidateLogSecondMoment (t + h) + candidateLogSecondMoment t -
        2 * ∫ ω, harperCandidateLogProcess ω (t + h) * harperCandidateLogProcess ω t ∂mu := by
    unfold candidateLogTranslationSecondMoment candidateLogSecondMoment
    rw [show (fun ω ↦ (harperCandidateLogProcess ω (t + h) - harperCandidateLogProcess ω t) ^ 2) =
        (fun ω ↦ harperCandidateLogProcess ω (t + h) ^ 2 + harperCandidateLogProcess ω t ^ 2 -
          2 * (harperCandidateLogProcess ω (t + h) * harperCandidateLogProcess ω t)) by
      funext ω; ring]
    have hiAdd : Integrable (fun ω ↦ harperCandidateLogProcess ω (t + h) ^ 2 +
        harperCandidateLogProcess ω t ^ 2) mu :=
      (candidate_integrable_logProcess_sq _).add (candidate_integrable_logProcess_sq _)
    rw [integral_sub hiAdd ((candidate_integrable_logProcess_mul (t + h) t).const_mul 2),
      integral_add (candidate_integrable_logProcess_sq _) (candidate_integrable_logProcess_sq _),
      integral_const_mul]
  rw [heq]
  have hc := candidate_log_covariance_lower hh t
  have hexp := Real.add_one_le_exp (-h / 2)
  have hV := candidateLogSecondMoment_nonneg t
  nlinarith

theorem measurable_candidateLogSecondMoment : Measurable candidateLogSecondMoment := by
  have h : Measurable (fun z : ℝ × Omega ↦ harperCandidateLogProcess z.2 z.1 ^ 2) :=
    (measurable_harperCandidateLogProcess.comp measurable_swap).pow_const 2
  exact h.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_candidateLogTranslationSecondMoment (h : ℝ) :
    Measurable (candidateLogTranslationSecondMoment h) := by
  have hfuture : Measurable
      (fun z : ℝ × Omega ↦ harperCandidateLogProcess z.2 (z.1 + h)) :=
    measurable_harperCandidateLogProcess.comp
      (measurable_snd.prodMk (measurable_fst.add_const h))
  have hpast : Measurable
      (fun z : ℝ × Omega ↦ harperCandidateLogProcess z.2 z.1) :=
    measurable_harperCandidateLogProcess.comp measurable_swap
  exact ((hfuture.sub hpast).pow_const 2).stronglyMeasurable.integral_prod_right.measurable

theorem intervalIntegrable_candidateLogSecondMoment
    (a b : ℝ) (hab : a ≤ b) : IntervalIntegrable candidateLogSecondMoment volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  refine (integrable_const (μ := volume.restrict (Ioc a b)) (1 + max b 0)).mono'
    measurable_candidateLogSecondMoment.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (candidateLogSecondMoment_nonneg t)]
  exact candidateLogSecondMoment_le_of_le (le_max_right _ _) (ht.2.trans (le_max_left _ _))

theorem intervalIntegrable_candidateLogTranslationSecondMoment
    {h : ℝ} (hh : 0 ≤ h) (a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable (candidateLogTranslationSecondMoment h) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  refine (integrable_const (μ := volume.restrict (Ioc a b))
    ((1 + h) * (1 + max (b + h) 0))).mono'
      (measurable_candidateLogTranslationSecondMoment h).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hnW : 0 ≤ candidateLogTranslationSecondMoment h t := integral_nonneg fun _ ↦ sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnW]
  have hfuture := candidateLogSecondMoment_le_of_le (le_max_right (b + h) 0)
    (show t + h ≤ max (b + h) 0 by linarith [ht.2, le_max_left (b + h) 0])
  have hpast := candidateLogSecondMoment_le_of_le (le_max_right (b + h) 0)
    (show t ≤ max (b + h) 0 by linarith [ht.2, le_max_left (b + h) 0])
  have hb := candidateLogTranslationSecondMoment_le hh t
  have hn := candidateLogSecondMoment_nonneg t
  nlinarith

/-- Quantitative integrated translation bound sufficient for exponentially
fine coupling bins. The factor `(L+1)^2` is derived from the checked first
moment of the variance and the terminal interval, with no off-diagonal
square-pair counting premise. -/
theorem candidate_integral_logTranslationSecondMoment_le
    {h L : ℝ} (hh : 0 < h) (hhone : h ≤ 1) (hL : 1 ≤ L) :
    (∫ v in Set.Ioc (-h) L, candidateLogTranslationSecondMoment h v) ≤
      2 * h * (L + 1) ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have haL : -h ≤ L := by linarith
  have hV := intervalIntegrable_candidateLogSecondMoment (-h) L haL
  have hV0 := intervalIntegrable_candidateLogSecondMoment 0 L hL0
  have hVT := intervalIntegrable_candidateLogSecondMoment L (L + h) (by linarith)
  have hVneg := intervalIntegrable_candidateLogSecondMoment (-h) 0 (by linarith)
  have hVall := intervalIntegrable_candidateLogSecondMoment 0 (L + h) (by linarith)
  have hshift : IntervalIntegrable (fun t ↦ candidateLogSecondMoment (t + h)) volume (-h) L := by
    simpa using hVall.comp_add_right h
  have hdom : (∫ v in (-h)..L, candidateLogTranslationSecondMoment h v) ≤
      ∫ v in (-h)..L, candidateLogSecondMoment (v + h) - candidateLogSecondMoment v +
        h * candidateLogSecondMoment v := by
    apply intervalIntegral.integral_mono_on haL
      (intervalIntegrable_candidateLogTranslationSecondMoment hh.le _ _ haL)
      ((hshift.sub hV).add (hV.const_mul h))
    intro v _
    exact candidateLogTranslationSecondMoment_le hh.le v
  have hneg : (∫ v in (-h)..0, candidateLogSecondMoment v) = 0 := by
    rw [intervalIntegral.integral_of_le (by linarith : -h ≤ 0)]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Ioc (-h) 0)).ae_ne (0 : ℝ)] with v hv hne
    exact candidateLogSecondMoment_eq_zero_of_neg (lt_of_le_of_ne hv.2 hne)
  have hleft : (∫ v in (-h)..L, candidateLogSecondMoment v) =
      ∫ v in (0 : ℝ)..L, candidateLogSecondMoment v := by
    have h := intervalIntegral.integral_add_adjacent_intervals hVneg hV0
    rw [hneg, zero_add] at h
    exact h.symm
  have hright : (∫ v in (-h)..L, candidateLogSecondMoment (v + h)) =
      (∫ v in (0 : ℝ)..L, candidateLogSecondMoment v) +
        ∫ v in L..(L + h), candidateLogSecondMoment v := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa using (intervalIntegral.integral_add_adjacent_intervals hV0 hVT).symm
  rw [intervalIntegral.integral_add (hshift.sub hV) (hV.const_mul h),
    intervalIntegral.integral_sub hshift hV, intervalIntegral.integral_const_mul,
    hleft, hright] at hdom
  have hbulk : (∫ v in (0 : ℝ)..L, candidateLogSecondMoment v) ≤ L * (L + 1) := by
    have h := intervalIntegral.integral_mono_on hL0 hV0
      (intervalIntegrable_const (c := L + 1))
      (fun v hv ↦ by simpa only [add_comm] using
        candidateLogSecondMoment_le_of_le hL0 hv.2)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, add_comm] using h
  have htail : (∫ v in L..(L + h), candidateLogSecondMoment v) ≤ h * (L + 2) := by
    have h := intervalIntegral.integral_mono_on (by linarith : L ≤ L + h) hVT
      (intervalIntegrable_const (c := L + 2))
      (fun v hv ↦ by
        have hb := candidateLogSecondMoment_le_of_le (t := v) (L := L + 1)
          (by linarith) (by linarith [hv.2])
        linarith)
    simpa only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul] using h
  rw [← intervalIntegral.integral_of_le haL]
  have hbulk_mul := mul_le_mul_of_nonneg_left hbulk hh.le
  nlinarith [mul_nonneg hh.le (sq_nonneg L), mul_nonneg hh.le hL0]

end Erdos.Problem1144
