import Erdos.Problem1144.HarperCandidateCovariancePerronComparison
import Erdos.Problem1144.HarperCandidateGaussianAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- The auxiliary covariance cutoff `T^q` absorbs the linear grid size and a
comparison gap `T^(-r)` exactly when `q>1+2r`. This cutoff is independent of
any stationary spectral cutoff. -/
theorem candidateSchedule_eulerBand_error_tendsto_zero
    {κ q r : ℝ} (hκ : 0 < κ) (hqr : 1 + 2 * r < q)
    (s : Finset ℕ) (η : s → Bool) {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (fun T : ℝ => C * (candidateScheduleM κ T : ℝ) /
      (T ^ q * mu.real (candidateCylinder s η) * (T ^ (-r)) ^ 2)) atTop (𝓝 0) := by
  let d := mu.real (candidateCylinder s η)
  have hd : 0 ≤ d := measureReal_nonneg
  have hz : Tendsto (fun T : ℝ => (C / d) * T ^ (1 - q + 2 * r)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < q - 1 - 2 * r by linarith)).const_mul (C / d)
    simpa only [show -(q - 1 - 2 * r) = 1 - q + 2 * r by ring, mul_zero] using h
  apply squeeze_zero' _ _ hz
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact div_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (by positivity)
  · filter_upwards [candidateScheduleM_eventually_le_time hκ,
      eventually_gt_atTop (0 : ℝ)] with T hm hT
    refine (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm hC) (by positivity)).trans_eq ?_
    have hp : T ^ q * (T ^ (-r)) ^ 2 = T ^ (q - 2 * r) := by
      rw [← Real.rpow_natCast (T ^ (-r)) 2, ← Real.rpow_mul hT.le,
        ← Real.rpow_add hT]
      congr 1
      norm_num
      ring
    have he : T / T ^ (q - 2 * r) = T ^ (1 - q + 2 * r) := by
      calc
        _ = T ^ (1 : ℝ) / T ^ (q - 2 * r) := by rw [Real.rpow_one]
        _ = T ^ ((1 : ℝ) - (q - 2 * r)) := (Real.rpow_sub hT _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = (C / d) * (T / (T ^ q * (T ^ (-r)) ^ 2)) := by
        simp only [d, div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [hp, he]

/-- The threshold gap also vanishes whenever its prescribed power is positive. -/
theorem candidate_eulerBand_power_gap_tendsto_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun T : ℝ => T ^ (-r)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hr

/-- Actual selected-crossing transfer on every deterministic scheduled block
and shift, under every fixed cylinder. The derived condition `q>1+2r` makes
the total comparison error vanish, while `r>0` makes the threshold gap vanish.
No lower-variance, covariance-screen, or Gaussian-comparison premise is used. -/
theorem candidateSchedule_eulerBand_white_selected_crossing
    {α β κ q r : ℝ} (hαβ : α ≤ β) (hβ : β < 4 / 3) (hκ : 0 < κ)
    (hr : 0 < r) (hqr : 1 + 2 * r < q)
    (s : Finset ℕ) (η : s → Bool) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ k < candidateScheduleN α β κ T,
      ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ (J : Omega → Finset (Fin (candidateScheduleM κ T))),
        (∀ i, MeasurableSet {ω | i ∈ J ω}) → ∀ K : ℝ,
      (∫ ω, candidateEulerBandWhiteCrossing (candidateScheduleX T)
        (fun i : Fin (candidateScheduleM κ T) => candidateSchedulePoint α κ T k i shift)
        (T ^ q) T (β * T) J (K + T ^ (-r)) ω ∂candidateCylinderLaw s η) ≤
      (∫ ω, candidateComparisonWhiteCrossing true
        (fun i : Fin (candidateScheduleM κ T) => candidateSchedulePoint α κ T k i shift)
        T J K ω ∂candidateCylinderLaw s η) + δ := by
  obtain ⟨C, hC, hb⟩ := candidate_exists_eulerBand_white_selected_crossing_bound
  have herr := (candidateSchedule_eulerBand_error_tendsto_zero hκ hqr s η hC.le).eventually
    (gt_mem_nhds hδ)
  filter_upwards [herr, eventually_ge_atTop (Real.log 2),
    eventually_gt_atTop (0 : ℝ)] with T he hTlog hT
  intro k hk shift hshift J hJ K
  have hu (i : Fin (candidateScheduleM κ T)) :
      candidateSchedulePoint α κ T k i shift ≤ β * T :=
    (candidate_grid_point_mem_window (by positivity)
      (candidateSchedule_cover hαβ hT.le) hk i.isLt hshift).2
  have hu2 (i : Fin (candidateScheduleM κ T)) :
      candidateSchedulePoint α κ T k i shift ≤ 2 * T :=
    (hu i).trans (mul_le_mul_of_nonneg_right (by linarith : β ≤ 2) hT.le)
  have h := hb s η
    (fun i : Fin (candidateScheduleM κ T) => candidateSchedulePoint α κ T k i shift)
    T (T ^ q) (β * T) hTlog (Real.rpow_pos_of_pos hT _) hu2 hu J hJ
    K (T ^ (-r)) (Real.rpow_pos_of_pos hT _)
  simp only [Fintype.card_fin] at h
  exact h.trans (add_le_add_right he.le _)

/-- The same transfer with the literal old-negative selector from the final
scheduled Gaussian crossing statement. Its measurability is discharged. -/
theorem candidateSchedule_eulerBand_white_retained_crossing
    {α β κ q r : ℝ} (hαβ : α ≤ β) (hβ : β < 4 / 3) (hκ : 0 < κ)
    (hr : 0 < r) (hqr : 1 + 2 * r < q)
    (s : Finset ℕ) (η : s → Bool) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ k < candidateScheduleN α β κ T,
      ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi), ∀ b ρ K : ℝ,
      let u := fun i : Fin (candidateScheduleM κ T) =>
        candidateSchedulePoint α κ T k i shift
      let J := candidateRetainedIndices
        (fun ω i => harperCandidateLogOld ω (candidateScheduleX T) (u i)) b ρ
      (∫ ω, candidateEulerBandWhiteCrossing (candidateScheduleX T)
        u (T ^ q) T (β * T) J (K + T ^ (-r)) ω ∂candidateCylinderLaw s η) ≤
      (∫ ω, candidateComparisonWhiteCrossing true u T J K ω
        ∂candidateCylinderLaw s η) + δ := by
  filter_upwards [candidateSchedule_eulerBand_white_selected_crossing
    hαβ hβ hκ hr hqr s η hδ] with T hT
  intro k hk shift hshift b ρ K
  exact hT k hk shift hshift _ (fun i =>
    measurableSet_mem_candidateRetainedIndices _
      (fun j : Fin (candidateScheduleM κ T) => measurable_harperCandidateLogOld _
        (candidateSchedulePoint α κ T k j shift)) b ρ i) K

end Erdos.Problem1144
