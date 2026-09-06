import Erdos.Problem1144.HarperCandidateCovarianceTopCutoff
import Erdos.Problem1144.HarperCandidateCovariancePerronScheduled

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Erdos.Problem1144
open Erdos.Problem520

/-- The exact complete Euler endpoint has the same uniform Gaussian distance
budget as the exponential cutoff. -/
theorem candidate_exists_topEulerBandWhiteTotalError_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (u : ι → ℝ) (T H B : ℝ),
      Real.log (harperBlockEndpoint 0 : ℝ) ≤ T → 0 < H →
      (∀ i, u i ≤ 3 / 2 * T) → (∀ i, u i ≤ B) →
      (∫ ω, candidateEulerBandWhiteTotalError (candidateEulerTopCutoff T) u H T B ω ∂mu) ≤
        C * Fintype.card ι / H := by
  obtain ⟨C, hC, hb⟩ := candidate_exists_whiteEulerCutoffError_uniform_bound
  refine ⟨C, hC, ?_⟩
  intro ι _ u T H B hTlog hH hu huB
  have hT : 0 < T := (Real.log_pos (by
    exact_mod_cast (harperBlockEndpoint_ge_sixteen 0).trans_lt'
      (by norm_num : 1 < 16))).trans_le hTlog
  have hY (i : ι) := candidateEulerTopCutoff_covers_prefix hTlog (hu i)
  have hY2 : 2 ≤ candidateEulerTopCutoff T :=
    (by norm_num : 2 ≤ 16).trans (harperBlockEndpoint_ge_sixteen _)
  unfold candidateEulerBandWhiteTotalError
  rw [integral_finset_sum _ (fun i _ =>
    candidate_integrable_eulerBandWhiteKernel_error _ hH hT B (u i) (huB i) (hY i))]
  calc
    _ ≤ ∑ i : ι, C / H := by
      apply Finset.sum_le_sum
      intro i _
      simp_rw [candidate_eulerBandWhiteKernel_error_eq _ _ H B (u i) hT (huB i)]
      exact hb _ H T B (u i) hY2 hH hT (candidateEulerTopCutoff_log_bounds hTlog).2 (hY i)
    _ = _ := by simp; ring

/-- Selected crossing comparison at an exact complete Euler endpoint, with
the literal finite-dimensional Gram error and fixed-cylinder loss. -/
theorem candidate_exists_topEulerBand_white_selected_crossing_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (s : Finset ℕ) (η : s → Bool) (u : ι → ℝ) (T H B : ℝ),
      Real.log (harperBlockEndpoint 0 : ℝ) ≤ T → 0 < H →
      (∀ i, u i ≤ 3 / 2 * T) → (∀ i, u i ≤ B) →
      ∀ (J : Omega → Finset ι), (∀ i, MeasurableSet {ω | i ∈ J ω}) →
      ∀ K ε : ℝ, 0 < ε →
      (∫ ω, candidateEulerBandWhiteCrossing (candidateEulerTopCutoff T)
        u H T B J (K + ε) ω ∂candidateCylinderLaw s η) ≤
      (∫ ω, candidateComparisonWhiteCrossing true u T J K ω ∂candidateCylinderLaw s η) +
        C * Fintype.card ι / (H * mu.real (candidateCylinder s η) * ε ^ 2) := by
  obtain ⟨C, hC, hb⟩ := candidate_exists_topEulerBandWhiteTotalError_bound
  refine ⟨C, hC, ?_⟩
  intro ι _ _ s η u T H B hTlog hH hu huB J hJ K ε hε
  have hT : 0 < T := (Real.log_pos (by
    exact_mod_cast (harperBlockEndpoint_ge_sixteen 0).trans_lt'
      (by norm_num : 1 < 16))).trans_le hTlog
  have hY (i : ι) := candidateEulerTopCutoff_covers_prefix hTlog (hu i)
  refine (candidate_eulerBand_white_selected_crossing_le s η _ u hH hT B huB hY J hJ K hε).trans ?_
  apply add_le_add_right
  have he := div_le_div_of_nonneg_right (hb u T H B hTlog hH hu huB)
    (show 0 ≤ mu.real (candidateCylinder s η) * ε ^ 2 by positivity)
  simpa only [div_div, mul_assoc] using he

/-- Replacing the auxiliary Euler cutoff by the complete endpoint preserves
the vanishing comparison error uniformly on every scheduled block and shift. -/
theorem candidateSchedule_topEulerBand_white_selected_crossing
    {α β κ q r : ℝ} (hαβ : α ≤ β) (hβ : β < 4 / 3) (hκ : 0 < κ)
    (hqr : 1 + 2 * r < q)
    (s : Finset ℕ) (η : s → Bool) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ k < candidateScheduleN α β κ T,
      ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ (J : Omega → Finset (Fin (candidateScheduleM κ T))),
        (∀ i, MeasurableSet {ω | i ∈ J ω}) → ∀ K : ℝ,
      (∫ ω, candidateEulerBandWhiteCrossing (candidateEulerTopCutoff T)
        (fun i : Fin (candidateScheduleM κ T) => candidateSchedulePoint α κ T k i shift)
        (T ^ q) T (β * T) J (K + T ^ (-r)) ω ∂candidateCylinderLaw s η) ≤
      (∫ ω, candidateComparisonWhiteCrossing true
        (fun i : Fin (candidateScheduleM κ T) => candidateSchedulePoint α κ T k i shift)
        T J K ω ∂candidateCylinderLaw s η) + δ := by
  obtain ⟨C, hC, hb⟩ := candidate_exists_topEulerBand_white_selected_crossing_bound
  have herr := (candidateSchedule_eulerBand_error_tendsto_zero hκ hqr s η hC.le).eventually
    (gt_mem_nhds hδ)
  filter_upwards [herr, eventually_ge_atTop (Real.log (harperBlockEndpoint 0 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with T he hTlog hT
  intro k hk shift hshift J hJ K
  have hu (i : Fin (candidateScheduleM κ T)) :
      candidateSchedulePoint α κ T k i shift ≤ β * T :=
    (candidate_grid_point_mem_window (by positivity)
      (candidateSchedule_cover hαβ hT.le) hk i.isLt hshift).2
  have hu2 (i : Fin (candidateScheduleM κ T)) :
      candidateSchedulePoint α κ T k i shift ≤ 3 / 2 * T :=
    (hu i).trans (mul_le_mul_of_nonneg_right (by linarith : β ≤ 3 / 2) hT.le)
  have h := hb s η
    (fun i : Fin (candidateScheduleM κ T) => candidateSchedulePoint α κ T k i shift)
    T (T ^ q) (β * T) hTlog (Real.rpow_pos_of_pos hT _) hu2 hu J hJ
    K (T ^ (-r)) (Real.rpow_pos_of_pos hT _)
  simp only [Fintype.card_fin] at h
  exact h.trans (add_le_add_right he.le _)

/-- The actual old-negative selector still uses its original integer cutoff;
only the auxiliary Euler approximation uses the exact block endpoint. -/
theorem candidateSchedule_topEulerBand_white_retained_crossing
    {α β κ q r : ℝ} (hαβ : α ≤ β) (hβ : β < 4 / 3) (hκ : 0 < κ)
    (hqr : 1 + 2 * r < q)
    (s : Finset ℕ) (η : s → Bool) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ k < candidateScheduleN α β κ T,
      ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi), ∀ b ρ K : ℝ,
      let u := fun i : Fin (candidateScheduleM κ T) =>
        candidateSchedulePoint α κ T k i shift
      let J := candidateRetainedIndices
        (fun ω i => harperCandidateLogOld ω (candidateScheduleX T) (u i)) b ρ
      (∫ ω, candidateEulerBandWhiteCrossing (candidateEulerTopCutoff T)
        u (T ^ q) T (β * T) J (K + T ^ (-r)) ω ∂candidateCylinderLaw s η) ≤
      (∫ ω, candidateComparisonWhiteCrossing true u T J K ω
        ∂candidateCylinderLaw s η) + δ := by
  filter_upwards [candidateSchedule_topEulerBand_white_selected_crossing
    hαβ hβ hκ hqr s η hδ] with T hT
  intro k hk shift hshift b ρ K
  exact hT k hk shift hshift _ (fun i =>
    measurableSet_mem_candidateRetainedIndices _
      (fun j : Fin (candidateScheduleM κ T) => measurable_harperCandidateLogOld _
        (candidateSchedulePoint α κ T k j shift)) b ρ i) K

end Erdos.Problem1144
