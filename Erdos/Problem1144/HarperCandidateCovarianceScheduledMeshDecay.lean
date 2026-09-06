import Erdos.Problem1144.HarperCandidateCovarianceScheduledRetainedError

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- The actual common upper-mesh failure has an inverse-seventh-log bound
on the rounded frequency and path schedule. The constant is absolute. -/
theorem candidate_exists_scheduledCommonMesh_failure_le :
    ∃ K > 0, ∀ J : ℕ, ∀ᶠ T : ℝ in atTop,
      mu.real (candidateCovarianceCommonMeshEvent (candidateCovarianceScheduleStart J T)
        (candidateCovarianceScheduleLength J T) (candidateCovarianceScheduleHeight T)
        (Real.log T))ᶜ ≤ K / Real.log T ^ 7 := by
  obtain ⟨C, hC, hm⟩ := candidate_exists_covarianceCommonMesh_failure_le
  let U := 1 / Real.log 2 + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hU : 0 < U := by dsimp only [U]; positivity
  refine ⟨7 * C * U, by positivity, ?_⟩
  intro J
  filter_upwards [candidate_eventually_covarianceSchedule_length_log_bounds J,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hNlog hq1
  let q := Real.log T
  let N := candidateCovarianceScheduleLength J T
  let M := candidateCovarianceScheduleHeight T
  change 1 ≤ q at hq1
  have hq : 0 < q := by linarith
  have hNp : (N + 1 : ℕ) ≤ U * q := by
    have hh := (le_div_iff₀ hlog2).mpr hNlog.2
    change (N : ℝ) ≤ q / Real.log 2 at hh
    rw [Nat.cast_add, Nat.cast_one]
    dsimp only [U]
    simp only [div_eq_mul_inv, one_mul] at hh ⊢
    nlinarith
  have hM : 2 * (M : ℝ) + 3 ≤ 7 * q ^ 2 := by
    have hh := (candidate_covarianceSchedule_height_bounds T).2
    change (M : ℝ) < q ^ 2 + 1 at hh
    nlinarith
  have hb := hm (candidateCovarianceScheduleStart J T) N M q (Nat.cast_nonneg _) hq
  apply hb.trans
  calc
    _ ≤ C * (7 * q ^ 2) * (U * q) / q ^ 10 := by gcongr
    _ = (7 * C * U) / q ^ 7 := by field_simp <;> ring

/-- The literal common mesh is asymptotically full probability. -/
theorem candidate_scheduledCommonMesh_failure_tendsto_zero (J : ℕ) :
    Tendsto (fun T : ℝ =>
      mu.real (candidateCovarianceCommonMeshEvent (candidateCovarianceScheduleStart J T)
        (candidateCovarianceScheduleLength J T) (candidateCovarianceScheduleHeight T)
        (Real.log T))ᶜ) atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := candidate_exists_scheduledCommonMesh_failure_le
  have hl := (tendsto_inv_atTop_zero.comp
    ((tendsto_pow_atTop (by norm_num : (7 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop)).const_mul K
  simp only [mul_zero, Function.comp_def] at hl
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hl
  filter_upwards [hb J] with T hT
  simpa only [div_eq_mul_inv] using hT

/-- Every fixed cylinder inherits the actual common-mesh probability
limit. Conditioning incurs only its fixed reciprocal cylinder mass. -/
theorem candidate_cylinder_scheduledCommonMesh_failure_tendsto_zero (J : ℕ)
    (s : Finset ℕ) (η : s → Bool) :
    Tendsto (fun T : ℝ =>
      (candidateCylinderLaw s η).real
        (candidateCovarianceCommonMeshEvent (candidateCovarianceScheduleStart J T)
          (candidateCovarianceScheduleLength J T) (candidateCovarianceScheduleHeight T)
          (Real.log T))ᶜ) atTop (𝓝 0) := by
  have hl := (candidate_scheduledCommonMesh_failure_tendsto_zero J).div_const
    (mu.real (candidateCylinder s η))
  simp only [zero_div] at hl
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hl
  apply Eventually.of_forall
  intro T
  rw [candidateCylinderLaw_real]
  exact div_le_div_of_nonneg_right (measureReal_mono inter_subset_right) measureReal_nonneg

end
end Erdos.Problem1144
