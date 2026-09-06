import Erdos.Problem1144.HarperCandidateCovarianceGapProduct
import Mathlib.Logic.Equiv.Fin.Basic

open Finset Set MeasureTheory
open scoped BigOperators Classical

namespace Erdos.Problem1144

noncomputable section

/-- The fixed, height-independent loss for an original list of `m`
coordinates. The remaining expectation bound is a product of gap weights. -/
def candidateCovarianceGapMomentFactor (C D : ℝ) (start m : ℕ) : ℝ :=
  (max 1 D) ^ m * Real.exp ((4 * Real.log 4 + 8 / 3) * m +
    32 * m * Real.log ((m : ℝ) + 1) +
    2 * C * (m : ℝ) ^ 2 * Problem520.invLog (Problem520.harperBlockEndpoint start) ^ 2)

theorem candidate_gapMomentFactor_nonneg (C D : ℝ) (start m : ℕ) :
    0 ≤ candidateCovarianceGapMomentFactor C D start m := by
  unfold candidateCovarianceGapMomentFactor
  exact mul_nonneg (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)) _)
    (Real.exp_pos _).le

theorem candidate_gapMomentFactor_mono (C D : ℝ) (hC : 0 ≤ C) (start : ℕ) :
    Monotone (candidateCovarianceGapMomentFactor C D start) := by
  intro n m hnm
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by
    linarith [Nat.cast_nonneg n (α := ℝ)])
  have hlog : Real.log ((n : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hmlog := mul_le_mul hnmR hlog hlog0 (Nat.cast_nonneg m)
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hnmR 2
  unfold candidateCovarianceGapMomentFactor
  apply mul_le_mul (pow_le_pow_right₀ (le_max_left 1 D) hnm)
  · apply Real.exp_le_exp.mpr
    have hc0 : 0 ≤ 4 * Real.log 4 + 8 / 3 := by positivity
    have hlin := mul_le_mul_of_nonneg_left hnmR hc0
    have herr := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * C))
      (sq_nonneg (Problem520.invLog (Problem520.harperBlockEndpoint start)))
    linarith
  · exact (Real.exp_pos _).le
  · exact pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)) _

private def rootIndex (n : ℕ) : Option (Fin n) ≃ Fin (n + 1) :=
  (finSuccEquiv' (Fin.last n)).symm

private theorem rootIndex_none (n : ℕ) : rootIndex n none = Fin.last n := rfl

private theorem rootIndex_some (n : ℕ) (i : Fin n) : rootIndex n (some i) = i.castSucc :=
  finSuccEquiv'_symm_some_below (by exact i.isLt)

/-- Literal mixed expectation with one explicit envelope factor for each
original consecutive gap. Cutoffs are chosen canonically, the largest
height is the unremoved root, and all survivor geometry is discharged. -/
theorem candidate_exists_ordered_gap_product_moment_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ n start stop : ℕ, J ≤ start → start ≤ stop →
    ∀ t : Fin (n + 1) → ℝ, Monotone t →
      (∀ i, 0 ≤ t i ∧ t i ≤ candidateCovarianceHeightWindow start / 2) →
    ∀ alpha : Fin n → ℝ,
    let y := Problem520.harperBlockEndpoint stop
    let g := fun i : Fin n => t i.succ - t i.castSucc
    let j := fun i => candidateCovarianceGapCutoff start stop (g i)
    (∫ ω, {ω | ∀ i : Fin n, Problem520.harperEulerDensity
      (Problem520.harperBlockEndpoint (j i)) ω (t i.castSucc) ≤
        (Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) * alpha i) ^ 2}.indicator
      (fun ω => ∏ i : Fin (n + 1), Problem520.harperEulerDensity y ω (t i)) ω ∂Problem520.μ) ≤
      candidateCovarianceGapMomentFactor C D start (n + 1) *
        (Real.log (y : ℝ) / Real.log 3) *
        ∏ i : Fin n, Real.log (y : ℝ) * candidateCovarianceGapEnvelope start stop (g i) *
          alpha i ^ 2 := by
  classical
  obtain ⟨C, D, hC, hD, J, hbound⟩ := candidate_exists_fullPrefix_survivor_mixedEuler_bound
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro n start stop hstart hss t hmono ht alpha
  dsimp only
  let y := Problem520.harperBlockEndpoint stop
  let g : Fin n → ℝ := fun i => t i.succ - t i.castSucc
  let j : Fin n → ℕ := fun i => candidateCovarianceGapCutoff start stop (g i)
  let s := Finset.univ.filter (fun i => j i < stop)
  let tr : Option (Fin n) → ℝ := fun i => t (rootIndex n i)
  let ts : Option s → ℝ := fun i => tr (i.map Subtype.val)
  let js : s → ℕ := fun i => j i
  let m := Fintype.card (Option s)
  let A : Fin n → ℝ := fun i => (Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) * alpha i) ^ 2
  have hj (i : Fin n) := candidate_covarianceGapCutoff_spec start stop hss (g i)
  have hraw := hbound start stop hstart j (fun i => (hj i).1) (fun i => (hj i).2.1)
    tr A (fun i => sq_nonneg _)
  dsimp only at hraw
  have hsurv_strict (a b : Option s)
      (hab : rootIndex n (a.map Subtype.val) < rootIndex n (b.map Subtype.val)) : ts a < ts b := by
    cases a with
    | none =>
      simp only [Option.map_none, rootIndex_none] at hab
      exact (not_lt_of_ge (Fin.le_last _) hab).elim
    | some a =>
      have has : j a < stop := (Finset.mem_filter.mp a.property).2
      have hfit := (hj a).2.2.1 has
      have hgpos : 0 < g a :=
        (Problem520.invLog_harperBlockEndpoint_pos (j a)).trans_le hfit
      have hnext : t a.val.succ ≤ ts b := by
        apply hmono
        simp only [Option.map_some, rootIndex_some] at hab
        change a.val.val + 1 ≤ (rootIndex n (b.map Subtype.val)).val
        exact hab
      have hta : ts (some a) = t a.val.castSucc := by simp [ts, tr, rootIndex_some]
      rw [hta]
      dsimp only [g] at hgpos
      linarith
  have htsinj : Function.Injective ts := by
    intro a b he
    apply (Option.map_injective Subtype.val_injective)
    apply (rootIndex n).injective
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hba
    · exact (ne_of_lt (hsurv_strict a b hab)) he
    · exact (ne_of_gt (hsurv_strict b a hba)) he
  have htsrange (i : Option s) : 0 ≤ ts i ∧ ts i ≤ candidateCovarianceHeightWindow start / 2 :=
    ht _
  have htsgap (a b : Option s) (hab : ts a < ts b) :
      candidateMixedRootedScale js a ≤ ts b - ts a := by
    cases a with
    | none =>
      have hb : ts b ≤ ts none := by
        apply hmono
        simp only [Option.map_none, rootIndex_none]
        exact Fin.le_last _
      exact (not_lt_of_ge hb hab).elim
    | some a =>
      have has : j a < stop := (Finset.mem_filter.mp a.property).2
      have hfit := (hj a).2.2.1 has
      have hnext : t a.val.succ ≤ ts b := by
        apply hmono
        have hindex : rootIndex n (some a.val) < rootIndex n (b.map Subtype.val) :=
          lt_of_not_ge (fun hle => (not_lt_of_ge (hmono hle)) hab)
        rw [rootIndex_some] at hindex
        change a.val.val + 1 ≤ (rootIndex n (b.map Subtype.val)).val
        exact hindex
      change Problem520.invLog (Problem520.harperBlockEndpoint (j a)) ≤ _
      have hta : ts (some a) = t a.val.castSucc := by simp [ts, tr, rootIndex_some]
      rw [hta]
      dsimp only [g] at hfit
      linarith
  have hraw' := hraw htsinj htsrange htsgap
  have hleft :
      (∫ ω, {ω | ∀ i : Fin n, Problem520.harperEulerDensity
        (Problem520.harperBlockEndpoint (j i)) ω (tr (some i)) ≤ A i}.indicator
        (fun ω => ∏ i : Option (Fin n), Problem520.harperEulerDensity y ω (tr i)) ω ∂Problem520.μ) =
      ∫ ω, {ω | ∀ i : Fin n, Problem520.harperEulerDensity
        (Problem520.harperBlockEndpoint (j i)) ω (t i.castSucc) ≤ A i}.indicator
        (fun ω => ∏ i : Fin (n + 1), Problem520.harperEulerDensity y ω (t i)) ω ∂Problem520.μ := by
    apply integral_congr_ae
    filter_upwards [] with ω
    have hp := (rootIndex n).prod_comp (fun i => Problem520.harperEulerDensity y ω (t i))
    simp only [tr, rootIndex_some]
    simp only [Set.indicator_apply]
    split_ifs
    · exact hp
    · rfl
  rw [hleft] at hraw'
  have hm : m ≤ n + 1 := by
    dsimp only [m]
    rw [Fintype.card_option, Fintype.card_coe]
    have hs := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => j i < stop)
    simpa [s] using Nat.add_le_add_right hs 1
  have hfactor : D ^ m * Real.exp ((4 * Real.log 4 + 8 / 3) * m +
      32 * m * Real.log ((m : ℝ) + 1) + 2 * C * (m : ℝ) ^ 2 *
        Problem520.invLog (Problem520.harperBlockEndpoint start) ^ 2) ≤
      candidateCovarianceGapMomentFactor C D start (n + 1) := by
    apply le_trans _ (candidate_gapMomentFactor_mono C D hC.le start hm)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hD.le (le_max_right 1 D) m) (Real.exp_pos _).le
  have hweights := candidate_gap_caps_mul_ratios_le_product_envelope start stop hss g alpha
  dsimp only at hweights
  have hL : 0 ≤ Real.log (y : ℝ) / Real.log 3 := by
    apply div_nonneg
    · exact (Problem520.one_le_log_harperBlockEndpoint stop).trans' (by norm_num)
    · positivity
  have hprod0 : 0 ≤ (∏ i, A i) * (∏ i : s, Real.log (y : ℝ) /
      Real.log (Problem520.harperBlockEndpoint (j i) : ℝ)) := by
    apply mul_nonneg (Finset.prod_nonneg fun i _ => sq_nonneg _)
    apply Finset.prod_nonneg
    intro i _
    exact div_nonneg
      ((Problem520.one_le_log_harperBlockEndpoint stop).trans' (by norm_num))
      ((Problem520.one_le_log_harperBlockEndpoint (j i)).trans' (by norm_num))
  apply hraw'.trans
  calc
    _ = (D ^ m * Real.exp ((4 * Real.log 4 + 8 / 3) * m +
        32 * m * Real.log ((m : ℝ) + 1) + 2 * C * (m : ℝ) ^ 2 *
          Problem520.invLog (Problem520.harperBlockEndpoint start) ^ 2)) *
        (Real.log (y : ℝ) / Real.log 3) *
        ((∏ i, A i) * (∏ i : s, Real.log (y : ℝ) /
          Real.log (Problem520.harperBlockEndpoint (j i) : ℝ))) := by
            dsimp only [m, s, y]
            ring
    _ ≤ candidateCovarianceGapMomentFactor C D start (n + 1) *
        (Real.log (y : ℝ) / Real.log 3) *
        ((∏ i, A i) * (∏ i : s, Real.log (y : ℝ) /
          Real.log (Problem520.harperBlockEndpoint (j i) : ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor hL) hprod0
    _ ≤ _ := mul_le_mul_of_nonneg_left hweights
      (mul_nonneg (candidate_gapMomentFactor_nonneg C D start (n + 1)) hL)

/-- The usable one-dimensional gap-weight envelope retains the strong
barrier saving on `g < invLog B_(a-1)` and the ordinary cap elsewhere. -/
theorem candidate_exists_ordered_strong_gap_product_moment_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ n start stop a : ℕ, J ≤ start → start < a → a ≤ stop →
    ∀ W : ℝ, 1 ≤ W →
    ∀ t : Fin (n + 1) → ℝ, Monotone t →
      (∀ i, 0 ≤ t i ∧ t i ≤ candidateCovarianceHeightWindow start / 2) →
    let y := Problem520.harperBlockEndpoint stop
    let g := fun i : Fin n => t i.succ - t i.castSucc
    let j := fun i => candidateCovarianceGapCutoff start stop (g i)
    (∫ ω, {ω | ∀ i : Fin n, Problem520.harperEulerDensity
      (Problem520.harperBlockEndpoint (j i)) ω (t i.castSucc) ≤
        (Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) *
          candidateCovariancePrefixSaving a W (j i)) ^ 2}.indicator
      (fun ω => ∏ i : Fin (n + 1), Problem520.harperEulerDensity y ω (t i)) ω ∂Problem520.μ) ≤
      candidateCovarianceGapMomentFactor C D start (n + 1) *
        (Real.log (y : ℝ) / Real.log 3) *
        ∏ i : Fin n, Real.log (y : ℝ) * candidateCovarianceGapEnvelope start stop (g i) *
          candidateCovarianceGapSaving a W (g i) ^ 2 := by
  classical
  obtain ⟨C, D, hC, hD, J, hbound⟩ := candidate_exists_ordered_gap_product_moment_bound
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro n start stop a hstart hsa has W hW t hmono ht
  dsimp only
  have h := hbound n start stop hstart (by omega) t hmono ht
    (fun i => candidateCovariancePrefixSaving a W
      (candidateCovarianceGapCutoff start stop (t i.succ - t i.castSucc)))
  dsimp only at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left
  · apply Finset.prod_le_prod
    · intro i _
      exact mul_nonneg (mul_nonneg
        ((Problem520.one_le_log_harperBlockEndpoint stop).trans' (by norm_num))
        (candidate_gapEnvelope_nonneg start stop _)) (sq_nonneg _)
    · intro i _
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (candidate_prefixSaving_nonneg a _ W)
          (candidate_prefixSaving_gapCutoff_le_gapSaving start stop a hsa has W hW _) 2)
      exact mul_nonneg
        ((Problem520.one_le_log_harperBlockEndpoint stop).trans' (by norm_num))
        (candidate_gapEnvelope_nonneg start stop _)
  · exact mul_nonneg (candidate_gapMomentFactor_nonneg C D start (n + 1))
      (div_nonneg ((Problem520.one_le_log_harperBlockEndpoint stop).trans' (by norm_num))
        (by positivity))

/-- The literal common D-star and inclusive strong screen supply the
canonically selected weak or strong cap at every original gap. -/
theorem candidate_gap_screen_subset_prefixEvent
    (n start stop a : ℕ) (hsa : start < a) (has : a ≤ stop) (W : ℝ)
    (t : Fin (n + 1) → ℝ) :
    {ω | ∀ i : Fin n, ω ∈ candidateCovarianceDStarEvent start (stop - start) (t i.castSucc) W ∩
      candidateCovarianceStrongScreenEvent start (t i.castSucc) W (Finset.Icc (a - start) (stop - start))} ⊆
    {ω | ∀ i : Fin n,
      let j := candidateCovarianceGapCutoff start stop (t i.succ - t i.castSucc)
      Problem520.harperEulerDensity (Problem520.harperBlockEndpoint j) ω (t i.castSucc) ≤
        (Real.log (Problem520.harperBlockEndpoint j : ℝ) * candidateCovariancePrefixSaving a W j) ^ 2} := by
  classical
  intro ω hω
  let j := fun i : Fin n => candidateCovarianceGapCutoff start stop (t i.succ - t i.castSucc)
  have hspec (i : Fin n) := candidate_covarianceGapCutoff_spec start stop (by omega)
    (t i.succ - t i.castSucc)
  have hj (i : Fin n) : j i - start ≤ stop - start := by
    have hstop : j i ≤ stop := (hspec i).2.1
    omega
  have hcap := candidate_DStar_strongScreen_mixed_prefix_caps start (stop - start) W
    (Finset.Icc (a - start) (stop - start)) (fun i : Fin n => j i - start) hj
    (fun i => t i.castSucc) ω hω
  intro i
  have hstart : start ≤ j i := (hspec i).1
  have hstop : j i ≤ stop := (hspec i).2.1
  have hadd : start + (j i - start) = j i := Nat.add_sub_of_le hstart
  have hmem : j i - start ∈ Finset.Icc (a - start) (stop - start) ↔ a ≤ j i := by
    simp only [Finset.mem_Icc]
    omega
  have h := hcap i
  simp only [hadd, hmem] at h
  change Problem520.harperEulerDensity (Problem520.harperBlockEndpoint (j i)) ω (t i.castSucc) ≤
    (Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) * candidateCovariancePrefixSaving a W (j i)) ^ 2
  unfold candidateCovariancePrefixSaving
  split_ifs with hi <;> simpa only [hi, if_true, if_false, div_eq_mul_inv] using h

private theorem integrable_mixed_density {ι : Type*} [Fintype ι]
    (y : ℕ) (t : ι → ℝ) :
    Integrable (fun ω => ∏ i, Problem520.harperEulerDensity y ω (t i)) Problem520.μ := by
  have hm := Finset.measurable_prod univ (fun i _ =>
    (Problem520.stronglyMeasurable_harperEulerDensity y (t i)).measurable)
  apply Integrable.of_bound hm.aestronglyMeasurable
    (Problem520.harperEulerDensityUniformBound y ^ Fintype.card ι)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (prod_nonneg fun i _ =>
    Problem520.harperEulerDensity_nonneg y ω (t i))]
  simpa using Finset.prod_le_prod (s := univ)
    (g := fun _ : ι => Problem520.harperEulerDensityUniformBound y)
    (fun i _ => Problem520.harperEulerDensity_nonneg y ω (t i))
    (fun i _ => Problem520.harperEulerDensity_le_uniformBound y ω (t i))

/-- The actual inclusive D-star/strong-screen mixed expectation is bounded
by a product in the original consecutive gaps, ready for weighted gap
integration. No cutoff-selection or survivor-geometry input remains. -/
theorem candidate_exists_screened_gap_product_moment_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ n start stop a : ℕ, J ≤ start → start < a → a ≤ stop →
    ∀ W : ℝ, 1 ≤ W →
    ∀ t : Fin (n + 1) → ℝ, Monotone t →
      (∀ i, 0 ≤ t i ∧ t i ≤ candidateCovarianceHeightWindow start / 2) →
    let y := Problem520.harperBlockEndpoint stop
    let g := fun i : Fin n => t i.succ - t i.castSucc
    (∫ ω, {ω | ∀ i : Fin n, ω ∈
      candidateCovarianceDStarEvent start (stop - start) (t i.castSucc) W ∩
      candidateCovarianceStrongScreenEvent start (t i.castSucc) W
        (Finset.Icc (a - start) (stop - start))}.indicator
      (fun ω => ∏ i : Fin (n + 1), Problem520.harperEulerDensity y ω (t i)) ω ∂Problem520.μ) ≤
      candidateCovarianceGapMomentFactor C D start (n + 1) *
        (Real.log (y : ℝ) / Real.log 3) *
        ∏ i : Fin n, Real.log (y : ℝ) * candidateCovarianceGapEnvelope start stop (g i) *
          candidateCovarianceGapSaving a W (g i) ^ 2 := by
  classical
  obtain ⟨C, D, hC, hD, J, hbound⟩ := candidate_exists_ordered_strong_gap_product_moment_bound
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro n start stop a hstart hsa has W hW t hmono ht
  dsimp only
  let y := Problem520.harperBlockEndpoint stop
  let j := fun i : Fin n => candidateCovarianceGapCutoff start stop (t i.succ - t i.castSucc)
  let E := {ω | ∀ i : Fin n, Problem520.harperEulerDensity
    (Problem520.harperBlockEndpoint (j i)) ω (t i.castSucc) ≤
      (Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) * candidateCovariancePrefixSaving a W (j i)) ^ 2}
  have hE : MeasurableSet E := by
    rw [show E = ⋂ i : Fin n, {ω | Problem520.harperEulerDensity
      (Problem520.harperBlockEndpoint (j i)) ω (t i.castSucc) ≤
        (Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) * candidateCovariancePrefixSaving a W (j i)) ^ 2} by
      ext ω; simp [E]]
    exact MeasurableSet.iInter fun i => measurableSet_le
      (Problem520.stronglyMeasurable_harperEulerDensity _ _).measurable measurable_const
  apply le_trans _ (hbound n start stop a hstart hsa has W hW t hmono ht)
  apply integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => Set.indicator_nonneg
      (fun ω _ => Finset.prod_nonneg fun i _ => Problem520.harperEulerDensity_nonneg y ω (t i)) ω)
    ((integrable_mixed_density y t).indicator hE)
  filter_upwards [] with ω
  exact Set.indicator_le_indicator_of_subset
    (candidate_gap_screen_subset_prefixEvent n start stop a hsa has W t)
    (fun ω => Finset.prod_nonneg fun i _ => Problem520.harperEulerDensity_nonneg y ω (t i)) ω

end

end Erdos.Problem1144
