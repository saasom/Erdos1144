import Erdos.Problem1144.HarperCandidateCovarianceGapEnvelope

open Finset Set MeasureTheory
open scoped BigOperators Classical

namespace Erdos.Problem1144

noncomputable section

/-- The ordinary or strong modulus cap at the selected prefix. -/
def candidateCovariancePrefixSaving (a : ℕ) (W : ℝ) (j : ℕ) : ℝ :=
  if a ≤ j then (W ^ 1000)⁻¹ else W ^ 6

/-- A one-gap upper bound retaining the strong saving on the entire
short-gap region where the selected prefix is necessarily long. -/
def candidateCovarianceGapSaving (a : ℕ) (W g : ℝ) : ℝ :=
  if g < Problem520.invLog (Problem520.harperBlockEndpoint (a - 1))
    then (W ^ 1000)⁻¹ else W ^ 6

/-- Survivor diagonal ratios and all extracted caps combine into one
factor per original gap. The formula also holds for full-prefix removal. -/
theorem candidate_prefixCaps_mul_survivor_ratios_eq
    {ι : Type*} [Fintype ι] (stop : ℕ) (j : ι → ℕ) (hj : ∀ i, j i ≤ stop)
    (alpha : ι → ℝ) :
    let s := Finset.univ.filter (fun i => j i < stop)
    (∏ i, (Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) * alpha i) ^ 2) *
      (∏ i : s, Real.log (Problem520.harperBlockEndpoint stop : ℝ) /
        Real.log (Problem520.harperBlockEndpoint (j i) : ℝ)) =
      ∏ i, Real.log (Problem520.harperBlockEndpoint stop : ℝ) *
        Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) * alpha i ^ 2 := by
  classical
  dsimp only
  rw [Finset.prod_coe_sort (Finset.univ.filter (fun i => j i < stop))
    (fun i => Real.log (Problem520.harperBlockEndpoint stop : ℝ) /
      Real.log (Problem520.harperBlockEndpoint (j i) : ℝ)), Finset.prod_filter,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : j i < stop
  · rw [if_pos hi]
    have hlog : Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_one (Problem520.one_le_log_harperBlockEndpoint (j i)))
    field_simp
  · have he : j i = stop := by have := hj i; omega
    rw [if_neg hi, he]
    ring

/-- Product envelope for arbitrary original gaps and arbitrary cap
multipliers, without residual survivor indicators in the product. -/
theorem candidate_gap_caps_mul_ratios_le_product_envelope
    {ι : Type*} [Fintype ι] (start stop : ℕ) (hss : start ≤ stop)
    (g alpha : ι → ℝ) :
    let j := fun i => candidateCovarianceGapCutoff start stop (g i)
    let s := Finset.univ.filter (fun i => j i < stop)
    (∏ i, (Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) * alpha i) ^ 2) *
      (∏ i : s, Real.log (Problem520.harperBlockEndpoint stop : ℝ) /
        Real.log (Problem520.harperBlockEndpoint (j i) : ℝ)) ≤
      ∏ i, Real.log (Problem520.harperBlockEndpoint stop : ℝ) *
        candidateCovarianceGapEnvelope start stop (g i) * alpha i ^ 2 := by
  classical
  dsimp only
  rw [candidate_prefixCaps_mul_survivor_ratios_eq stop _
    (fun i => (candidate_covarianceGapCutoff_spec start stop hss (g i)).2.1)]
  apply Finset.prod_le_prod
  · intro i _
    have h0 (k : ℕ) : 0 ≤ Real.log (Problem520.harperBlockEndpoint k : ℝ) :=
      (Problem520.one_le_log_harperBlockEndpoint k).trans' (by norm_num)
    exact mul_nonneg (mul_nonneg (h0 stop) (h0 _)) (sq_nonneg _)
  · intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left (candidate_log_gapCutoff_le_envelope start stop hss (g i))
      ((Problem520.one_le_log_harperBlockEndpoint stop).trans' (by norm_num))

/-- The strong cap survives as an explicit short-gap saving. On the
remaining gaps the ordinary cap bounds either possible selected cap. -/
theorem candidate_prefixSaving_gapCutoff_le_gapSaving
    (start stop a : ℕ) (hsa : start < a) (has : a ≤ stop)
    (W : ℝ) (hW : 1 ≤ W) (g : ℝ) :
    candidateCovariancePrefixSaving a W (candidateCovarianceGapCutoff start stop g) ≤
      candidateCovarianceGapSaving a W g := by
  by_cases hg : g < Problem520.invLog (Problem520.harperBlockEndpoint (a - 1))
  · simp only [candidateCovarianceGapSaving, if_pos hg, candidateCovariancePrefixSaving,
      if_pos (candidate_covarianceGapCutoff_ge_of_gap_lt start stop a hsa has g hg), le_refl]
  · rw [candidateCovarianceGapSaving, if_neg hg]
    unfold candidateCovariancePrefixSaving
    split_ifs
    · exact (inv_le_one_of_one_le₀ (one_le_pow₀ hW)).trans (one_le_pow₀ hW)
    · exact le_rfl

theorem candidate_prefixSaving_nonneg (a j : ℕ) (W : ℝ) :
    0 ≤ candidateCovariancePrefixSaving a W j := by
  unfold candidateCovariancePrefixSaving
  split_ifs <;> positivity

theorem candidate_gapSaving_nonneg (a : ℕ) (W g : ℝ) :
    0 ≤ candidateCovarianceGapSaving a W g := by
  unfold candidateCovarianceGapSaving
  split_ifs <;> positivity

/-- Final per-gap weights retain the full strong saving while giving the
ordinary reciprocal-gap envelope elsewhere. -/
theorem candidate_gap_caps_le_strong_product_envelope
    {ι : Type*} [Fintype ι] (start stop a : ℕ) (hsa : start < a) (has : a ≤ stop)
    (W : ℝ) (hW : 1 ≤ W) (g : ι → ℝ) :
    let j := fun i => candidateCovarianceGapCutoff start stop (g i)
    let s := Finset.univ.filter (fun i => j i < stop)
    (∏ i, (Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) *
      candidateCovariancePrefixSaving a W (j i)) ^ 2) *
      (∏ i : s, Real.log (Problem520.harperBlockEndpoint stop : ℝ) /
        Real.log (Problem520.harperBlockEndpoint (j i) : ℝ)) ≤
      ∏ i, Real.log (Problem520.harperBlockEndpoint stop : ℝ) *
        candidateCovarianceGapEnvelope start stop (g i) * candidateCovarianceGapSaving a W (g i) ^ 2 := by
  classical
  dsimp only
  apply (candidate_gap_caps_mul_ratios_le_product_envelope start stop (by omega) g _).trans
  apply Finset.prod_le_prod
  · intro i _
    exact mul_nonneg (mul_nonneg
      ((Problem520.one_le_log_harperBlockEndpoint stop).trans' (by norm_num))
      (candidate_gapEnvelope_nonneg start stop (g i))) (sq_nonneg _)
  · intro i _
    apply mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (candidate_prefixSaving_nonneg a _ W)
        (candidate_prefixSaving_gapCutoff_le_gapSaving start stop a hsa has W hW (g i)) 2)
    exact mul_nonneg
      ((Problem520.one_le_log_harperBlockEndpoint stop).trans' (by norm_num))
      (candidate_gapEnvelope_nonneg start stop (g i))

end

end Erdos.Problem1144
