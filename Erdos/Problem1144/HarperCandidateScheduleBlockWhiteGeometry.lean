import Erdos.Problem1144.HarperCandidateScheduleWhiteTimeLogs

open Set Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- The literal original block is a translate of the original-cardinality
grid placed at the smaller white time. -/
theorem candidateSchedulePoint_eq_white_translate
    (α κ T : ℝ) (k i : ℕ) (shift : ℝ) :
    candidateSchedulePoint α κ T k i shift =
      (α * candidateScheduleWhiteTime κ T + (i : ℝ) * (2 * Real.pi)) +
        (α * T + (k : ℝ) * candidateScheduleL κ T + shift -
          α * candidateScheduleWhiteTime κ T) := by
  unfold candidateSchedulePoint
  ring

private theorem rounded_length_le_width {κ T : ℝ} (hT : 0 ≤ T) :
    candidateScheduleL κ T ≤ candidateScheduleD κ T := by
  have hD : 0 ≤ candidateScheduleD κ T := div_nonneg hT (sq_nonneg _)
  have hf := Nat.floor_le (div_nonneg hD (by positivity : 0 ≤ 2 * Real.pi))
  exact (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hf

/-- All original block points, their common translation, both proportional
windows, and the actual unrounded block width are available simultaneously.
The event in `T` is independent of the block, shift, and grid coordinate. -/
theorem candidateSchedule_eventually_block_white_geometry
    {α β κ : ℝ} (hκ : 0 < κ) (hαβ : α < β) :
    ∀ᶠ T : ℝ in atTop,
      ∀ k < candidateScheduleN α β κ T,
      ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi),
      let t0 := α * T + (k : ℝ) * candidateScheduleL κ T + shift
      let b := t0 - α * candidateScheduleWhiteTime κ T
      ∀ i : Fin (candidateScheduleM κ T),
        candidateSchedulePoint α κ T k i shift =
            (α * candidateScheduleWhiteTime κ T + (i : ℝ) * (2 * Real.pi)) + b ∧
        candidateSchedulePoint α κ T k i shift ∈ Icc t0 (t0 + candidateScheduleD κ T) ∧
        candidateSchedulePoint α κ T k i shift ∈ Icc (α * T) (β * T) ∧
        α * candidateScheduleWhiteTime κ T + (i : ℝ) * (2 * Real.pi) ∈
          Icc (α * candidateScheduleWhiteTime κ T) (β * candidateScheduleWhiteTime κ T) := by
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    candidateSchedule_translated_grid_mem_whiteTime_window hκ hαβ] with T hT hv
  intro k hk shift hs t0 b i
  refine ⟨candidateSchedulePoint_eq_white_translate α κ T k i shift, ?_, ?_, hv i⟩
  · have hstep0 : 0 ≤ (i : ℝ) * (2 * Real.pi) := by positivity
    have hi : (i : ℝ) ≤ (candidateScheduleM κ T : ℝ) := by
      exact_mod_cast i.isLt.le
    have hstep : (i : ℝ) * (2 * Real.pi) ≤ candidateScheduleD κ T :=
      (mul_le_mul_of_nonneg_right hi (by positivity)).trans (rounded_length_le_width hT)
    dsimp [candidateSchedulePoint, t0]
    constructor <;> linarith
  · exact Ioc_subset_Icc_self (candidate_grid_point_mem_window (by positivity)
      (candidateSchedule_cover hαβ.le hT) hk i.isLt hs)

end
end Erdos.Problem1144
