import Erdos.Problem1144.HarperCandidateOldTailGrid
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-! The candidate's exact logarithmic block schedule. -/
noncomputable def candidateScheduleW (κ T : ℝ) : ℝ := κ * Real.log (Real.log T)
noncomputable def candidateScheduleD (κ T : ℝ) : ℝ := T / candidateScheduleW κ T ^ 2
noncomputable def candidateScheduleM (κ T : ℝ) : ℕ := ⌊candidateScheduleD κ T / (2 * Real.pi)⌋₊
noncomputable def candidateScheduleL (κ T : ℝ) : ℝ := candidateScheduleM κ T * (2 * Real.pi)
noncomputable def candidateScheduleN (α β κ T : ℝ) : ℕ :=
  ⌊(β - α) * T / candidateScheduleL κ T⌋₊
noncomputable def candidateScheduleX (T : ℝ) : ℕ := ⌊Real.exp T⌋₊
noncomputable def candidateSchedulePoint (α κ T : ℝ) (k i : ℕ) (s : ℝ) : ℝ :=
  α * T + k * candidateScheduleL κ T + i * (2 * Real.pi) + s

theorem candidateScheduleW_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (candidateScheduleW κ) atTop atTop :=
  (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_mul_atTop hκ

theorem candidateScheduleW_sq_div_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun T => candidateScheduleW κ T ^ 2 / T) atTop (𝓝 0) := by
  have hl : Tendsto (fun T : ℝ => κ ^ 2 * (Real.log T ^ 2 / T)) atTop (𝓝 0) := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.const_mul (κ ^ 2)
  apply squeeze_zero' _ _ hl
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    positivity
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_gt_atTop (0 : ℝ)] with T hlog hT
    have hll : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlog
    have hle : Real.log (Real.log T) ≤ Real.log T := Real.log_le_self (by linarith)
    dsimp [candidateScheduleW]
    rw [mul_pow, ← mul_div_assoc]
    gcongr

theorem candidateScheduleD_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (candidateScheduleD κ) atTop atTop := by
  have hz : Tendsto (fun T => candidateScheduleW κ T ^ 2 / T) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨candidateScheduleW_sq_div_tendsto hκ, ?_⟩
    filter_upwards [(candidateScheduleW_tendsto hκ).eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℝ)] with T hw hT
    exact div_pos (sq_pos_of_pos hw) hT
  simpa [candidateScheduleD, Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp hz

theorem candidateScheduleM_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (candidateScheduleM κ) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    ((candidateScheduleD_tendsto hκ).atTop_div_const (by positivity))

theorem candidateScheduleL_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (candidateScheduleL κ) atTop atTop :=
  (tendsto_natCast_atTop_atTop.comp (candidateScheduleM_tendsto hκ)).atTop_mul_const
    (by positivity)

theorem candidateScheduleL_div_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun T => candidateScheduleL κ T / T) atTop (𝓝 0) := by
  have hw : Tendsto (fun T => (candidateScheduleW κ T ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (by simpa [pow_two] using
      (candidateScheduleW_tendsto hκ).atTop_mul_atTop₀ (candidateScheduleW_tendsto hκ))
  apply squeeze_zero' _ _ hw
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    dsimp [candidateScheduleL]
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hD : 0 ≤ candidateScheduleD κ T := by unfold candidateScheduleD; positivity
    have hf := Nat.floor_le (div_nonneg hD (by positivity : 0 ≤ 2 * Real.pi))
    have hp : 0 < 2 * Real.pi := by positivity
    have hm : candidateScheduleL κ T ≤ candidateScheduleD κ T := by
      apply (le_div_iff₀ hp).mp
      exact hf
    calc
      candidateScheduleL κ T / T ≤ candidateScheduleD κ T / T :=
        div_le_div_of_nonneg_right hm hT.le
      _ = (candidateScheduleW κ T ^ 2)⁻¹ := by
        unfold candidateScheduleD
        field_simp

theorem candidateSchedule_blockQuotient_tendsto
    {α β κ : ℝ} (hαβ : α < β) (hκ : 0 < κ) :
    Tendsto (fun T => (β - α) * T / candidateScheduleL κ T) atTop atTop := by
  have hz : Tendsto (fun T => candidateScheduleL κ T / T) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨candidateScheduleL_div_tendsto hκ, ?_⟩
    filter_upwards [(candidateScheduleL_tendsto hκ).eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℝ)] with T hL hT
    exact div_pos hL hT
  have hi := (tendsto_inv_nhdsGT_zero.comp hz).const_mul_atTop (sub_pos.mpr hαβ)
  simpa only [Function.comp_def, inv_div, mul_div_assoc] using hi

theorem candidateScheduleN_tendsto {α β κ : ℝ} (hαβ : α < β) (hκ : 0 < κ) :
    Tendsto (candidateScheduleN α β κ) atTop atTop :=
  tendsto_nat_floor_atTop.comp (candidateSchedule_blockQuotient_tendsto hαβ hκ)

/-- Covered length divided by time converges to the full window width. -/
theorem candidateSchedule_covered_div_tendsto
    {α β κ : ℝ} (hαβ : α < β) (hκ : 0 < κ) :
    Tendsto (fun T => candidateScheduleN α β κ T * candidateScheduleL κ T / T)
      atTop (𝓝 (β - α)) := by
  have hf := (tendsto_nat_floor_div_atTop.comp
    (candidateSchedule_blockQuotient_tendsto hαβ hκ)).mul_const (β - α)
  simp only [one_mul] at hf
  apply hf.congr'
  filter_upwards [(candidateScheduleL_tendsto hκ).eventually_gt_atTop 0,
    eventually_gt_atTop (0 : ℝ)] with T hL hT
  dsimp [candidateScheduleN]
  field_simp [sub_ne_zero.mpr (ne_of_gt hαβ)]

/-- Exact partition containment follows from the defining floor. -/
theorem candidateSchedule_cover {α β κ T : ℝ}
    (hαβ : α ≤ β) (hT : 0 ≤ T) :
    α * T + candidateScheduleN α β κ T * candidateScheduleL κ T ≤ β * T := by
  have hL : 0 ≤ candidateScheduleL κ T := by unfold candidateScheduleL; positivity
  have hf := Nat.floor_le (div_nonneg (mul_nonneg (sub_nonneg.mpr hαβ) hT) hL)
  by_cases hL0 : candidateScheduleL κ T = 0
  · simp only [hL0, mul_zero, add_zero]
    exact mul_le_mul_of_nonneg_right hαβ hT
  · have hh := (le_div_iff₀ (lt_of_le_of_ne hL (Ne.symm hL0))).mp hf
    dsimp [candidateScheduleN]
    linarith

/-- The fraction of the observation interval covered by whole blocks tends
to one; the discarded terminal interval causes no asymptotic loss. -/
theorem candidateSchedule_covered_ratio_tendsto
    {α β κ : ℝ} (hαβ : α < β) (hκ : 0 < κ) :
    Tendsto (fun T => candidateScheduleN α β κ T * candidateScheduleL κ T /
      ((β - α) * T)) atTop (𝓝 1) := by
  have h := (candidateSchedule_covered_div_tendsto hαβ hκ).div_const (β - α)
  simpa only [div_div, mul_comm _ (β - α),
    div_self (sub_pos.mpr hαβ).ne'] using h

/-- Finite floor errors disappear uniformly below every fixed exponent less
than two. Thus the candidate's beta < 4/3 window lies in the linear range. -/
theorem candidateSchedule_eventually_cutoff_square {β : ℝ} (hβ : β < 2) :
    ∀ᶠ T : ℝ in atTop, ∀ t ≤ β * T, ⌊Real.exp t⌋₊ < candidateScheduleX T ^ 2 := by
  have hf := tendsto_nat_floor_div_atTop.comp Real.tendsto_exp_atTop
  have he := Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (sub_pos.mpr hβ))
  filter_upwards [hf.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    he.eventually_gt_atTop 4] with T hfloor hgap
  intro t ht
  have hexp := Real.exp_pos T
  have hhalf : Real.exp T / 2 < (candidateScheduleX T : ℝ) := by
    dsimp [Function.comp_def] at hfloor
    have hh := (lt_div_iff₀ hexp).mp hfloor
    change Real.exp T / 2 < (⌊Real.exp T⌋₊ : ℝ)
    linarith
  have hprod : Real.exp ((2 - β) * T) * Real.exp (β * T) = Real.exp T ^ 2 := by
    rw [← Real.exp_add, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsmall : 4 * Real.exp (β * T) < Real.exp T ^ 2 := by
    rw [← hprod]
    exact mul_lt_mul_of_pos_right hgap (Real.exp_pos _)
  have hbig : Real.exp T ^ 2 < 4 * (candidateScheduleX T : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ candidateScheduleX T from Nat.cast_nonneg _]
  have htbound : (⌊Real.exp t⌋₊ : ℝ) ≤ Real.exp (β * T) :=
    (Nat.floor_le (Real.exp_pos t).le).trans (Real.exp_le_exp.mpr ht)
  have hfinal : (⌊Real.exp t⌋₊ : ℝ) < (candidateScheduleX T : ℝ) ^ 2 := by
    nlinarith
  exact_mod_cast hfinal

theorem candidateSchedule_eventually_prefix (s : Finset ℕ) :
    ∀ᶠ T : ℝ in atTop, ∀ p ∈ s, p ≤ candidateScheduleX T := by
  have hf := tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop
  filter_upwards [hf.eventually_ge_atTop (s.sup id)] with T hT
  intro p hp
  exact (Finset.le_sup (f := id) hp).trans hT

/-- Choosing the fixed negative threshold before choosing the time makes the
exact old-tail grid bound arbitrarily close to twice the envelope deficit. -/
theorem candidateSchedule_exists_threshold_tailBudget
    {α β κ : ℝ} (hαβ : α < β) (hκ : 0 < κ) (q M : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ T : ℝ in atTop,
      2 * ((1 - q) * (β - α) * T + Real.exp β * M * T / b) /
        (candidateScheduleN α β κ T * candidateScheduleL κ T) ≤
      2 * (1 - q) + ε := by
  let c : ℝ := β - α
  have hc : c ≠ 0 := (sub_pos.mpr hαβ).ne'
  have hbLimit : Tendsto (fun b : ℝ =>
      2 * ((1 - q) * c + Real.exp β * M / b) / c) atTop (𝓝 (2 * (1 - q))) := by
    have hz := (tendsto_id.const_div_atTop (Real.exp β * M)).const_add ((1 - q) * c)
    have hh := (hz.const_mul 2).div_const c
    simpa [hc, ← mul_assoc] using hh
  obtain ⟨b, hb, hblt⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hbLimit.eventually (gt_mem_nhds (show 2 * (1 - q) < 2 * (1 - q) + ε by linarith)))).exists
  refine ⟨b, hb, ?_⟩
  have htLimit : Tendsto (fun T =>
      2 * ((1 - q) * c + Real.exp β * M / b) /
        (candidateScheduleN α β κ T * candidateScheduleL κ T / T))
      atTop (𝓝 (2 * ((1 - q) * c + Real.exp β * M / b) / c)) :=
    tendsto_const_nhds.div (candidateSchedule_covered_div_tendsto hαβ hκ) hc
  filter_upwards [htLimit.eventually (gt_mem_nhds hblt),
    eventually_gt_atTop (0 : ℝ)] with T hbound hT
  have heq : 2 * ((1 - q) * (β - α) * T + Real.exp β * M * T / b) /
      (candidateScheduleN α β κ T * candidateScheduleL κ T) =
      2 * ((1 - q) * c + Real.exp β * M / b) /
        (candidateScheduleN α β κ T * candidateScheduleL κ T / T) := by
    dsimp [c]
    field_simp
  rw [heq]
  exact hbound.le

end Erdos.Problem1144

#print axioms Erdos.Problem1144.candidateScheduleM_tendsto
#print axioms Erdos.Problem1144.candidateScheduleN_tendsto
#print axioms Erdos.Problem1144.candidateSchedule_covered_ratio_tendsto
#print axioms Erdos.Problem1144.candidateSchedule_eventually_cutoff_square
#print axioms Erdos.Problem1144.candidateSchedule_exists_threshold_tailBudget
