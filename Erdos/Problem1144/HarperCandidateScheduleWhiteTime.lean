import Erdos.Problem1144.HarperCandidateScheduleThinning

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- Smaller stationary white time associated with the literal outer block. -/
def candidateScheduleWhiteTime (κ T : ℝ) : ℝ := T / candidateScheduleW κ T

private theorem eventually_weight_time {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, 0 < T ∧ 1 ≤ candidateScheduleW κ T :=
  (eventually_gt_atTop 0).and ((candidateScheduleW_tendsto hκ).eventually_ge_atTop 1)

/-- The smaller white time grows without bound. -/
theorem candidateScheduleWhiteTime_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (candidateScheduleWhiteTime κ) atTop atTop := by
  apply tendsto_atTop_mono' _ ?_ (candidateScheduleD_tendsto hκ)
  filter_upwards [eventually_weight_time hκ] with T h
  unfold candidateScheduleD candidateScheduleWhiteTime
  exact div_le_div_of_nonneg_left h.1.le (by linarith) (by nlinarith [sq_nonneg (candidateScheduleW κ T - 1)])

/-- Both positivity and the comparison with the outer time follow from
the actual slowly growing schedule weight. -/
theorem candidateScheduleWhiteTime_eventually_bounds {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, 0 < candidateScheduleWhiteTime κ T ∧
      candidateScheduleWhiteTime κ T ≤ T := by
  filter_upwards [eventually_weight_time hκ] with T h
  exact ⟨div_pos h.1 (by linarith), div_le_self h.1.le h.2⟩

/-- Exact ratio of the original block width to the smaller white time. -/
theorem candidateScheduleD_div_whiteTime {κ T : ℝ}
    (hT : T ≠ 0) (hW : candidateScheduleW κ T ≠ 0) :
    candidateScheduleD κ T / candidateScheduleWhiteTime κ T =
      1 / candidateScheduleW κ T := by
  unfold candidateScheduleD candidateScheduleWhiteTime
  field_simp

/-- The original rounded block occupies a vanishing fraction of the
smaller white time. -/
theorem candidateScheduleL_div_whiteTime_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun T => candidateScheduleL κ T / candidateScheduleWhiteTime κ T)
      atTop (𝓝 0) := by
  have hl := tendsto_inv_atTop_zero.comp (candidateScheduleW_tendsto hκ)
  apply squeeze_zero' _ _ hl
  · filter_upwards [candidateScheduleWhiteTime_eventually_bounds hκ] with T h
    exact div_nonneg (by unfold candidateScheduleL; positivity) h.1.le
  · filter_upwards [eventually_weight_time hκ] with T h
    have hW : 0 < candidateScheduleW κ T := by linarith [h.2]
    have hD : 0 ≤ candidateScheduleD κ T := div_nonneg h.1.le (sq_nonneg _)
    have hf := Nat.floor_le (show 0 ≤ candidateScheduleD κ T / (2 * Real.pi) by positivity)
    have hL : candidateScheduleL κ T ≤ candidateScheduleD κ T :=
      (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hf
    have hh := div_le_div_of_nonneg_right hL (div_pos h.1 hW).le
    change candidateScheduleL κ T / candidateScheduleWhiteTime κ T ≤
      candidateScheduleD κ T / candidateScheduleWhiteTime κ T at hh
    rw [candidateScheduleD_div_whiteTime h.1.ne' hW.ne'] at hh
    simpa only [one_div, Function.comp_def] using hh

/-- The original grid cardinality is negligible relative to the smaller
time, rather than being recomputed from that smaller time. -/
theorem candidateScheduleM_div_whiteTime_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun T => (candidateScheduleM κ T : ℝ) / candidateScheduleWhiteTime κ T)
      atTop (𝓝 0) := by
  have hh := (candidateScheduleL_div_whiteTime_tendsto hκ).div_const (2 * Real.pi)
  simp only [zero_div] at hh
  convert hh using 1
  funext T
  unfold candidateScheduleL
  field_simp

/-- The larger original grid still lies within the linear-cardinality
range of the proved smaller-time variance and crossing theorems. -/
theorem candidateScheduleM_eventually_le_whiteTime {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, (candidateScheduleM κ T : ℝ) ≤ candidateScheduleWhiteTime κ T := by
  filter_upwards [candidateScheduleWhiteTime_eventually_bounds hκ,
    (candidateScheduleM_div_whiteTime_tendsto hκ).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with T h hsmall
  exact le_of_lt ((div_lt_iff₀ h.1).mp hsmall |>.trans_eq (one_mul _))

/-- Every actual old-field selector retains at least twice the required
sublinear power of the smaller time, uniformly in the old field and world. -/
theorem candidateSchedule_retained_card_ge_whiteTime_rpow
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∀ᶠ T : ℝ in atTop,
      ∀ (A : Omega → Fin (candidateScheduleM κ T) → ℝ) (b : ℝ) (ω : Omega),
      2 * candidateScheduleWhiteTime κ T ^ ((9 : ℝ) / 10) ≤
        (candidateRetainedIndices A b ρ ω).card := by
  have hs := ((candidateScheduleM_div_rpow_tendsto (a := (9 : ℝ) / 10) hκ
    (by norm_num)).const_mul_atTop hρ).eventually_ge_atTop 2
  filter_upwards [hs, candidateScheduleWhiteTime_eventually_bounds hκ] with T hsize hV
  intro A b ω
  have hT : 0 < T := hV.1.trans_le hV.2
  have hh : 2 * T ^ ((9 : ℝ) / 10) ≤ ρ * (candidateScheduleM κ T : ℝ) := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hT _)).mp
    simpa only [mul_div_assoc] using hsize
  have hret := candidateRetainedIndices_card_lower A b ρ hρ1 ω
  simp only [Fintype.card_fin] at hret
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hV.1.le hV.2 (by norm_num : (0 : ℝ) ≤ 9 / 10))
    (by norm_num : (0 : ℝ) ≤ 2)).trans (hh.trans hret)

/-- Translating the original grid to start at `αV` keeps every coordinate
inside any fixed proportional smaller-time window `[αV,βV]`. -/
theorem candidateSchedule_translated_grid_mem_whiteTime_window
    {κ α β : ℝ} (hκ : 0 < κ) (hαβ : α < β) :
    ∀ᶠ T : ℝ in atTop, ∀ i : Fin (candidateScheduleM κ T),
      α * candidateScheduleWhiteTime κ T + (i : ℝ) * (2 * Real.pi) ∈
        Icc (α * candidateScheduleWhiteTime κ T) (β * candidateScheduleWhiteTime κ T) := by
  filter_upwards [candidateScheduleWhiteTime_eventually_bounds hκ,
    (candidateScheduleL_div_whiteTime_tendsto hκ).eventually
      (gt_mem_nhds (sub_pos.mpr hαβ))] with T hV hsmall
  intro i
  have hwidth := (div_lt_iff₀ hV.1).mp hsmall
  have hi : (i : ℝ) ≤ candidateScheduleM κ T := by exact_mod_cast i.isLt.le
  have hgap : (i : ℝ) * (2 * Real.pi) ≤ candidateScheduleL κ T :=
    mul_le_mul_of_nonneg_right hi (by positivity)
  have hgap0 : 0 ≤ (i : ℝ) * (2 * Real.pi) := by positivity
  constructor <;> linarith

end
end Erdos.Problem1144
