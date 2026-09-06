import Erdos.Problem520.External.PNT.ZetaBounds

open Complex Filter Set Topology

namespace Erdos.Problem1144

/-!
# A uniform reciprocal-zeta window for the stationary candidate

The imported seventh-logarithm estimate only covers heights above `3`.
Removing the reciprocal's value at the pole and using compactness closes the
bounded-height gap. The shift `H + 4` places the logarithm above `1` even at
`H = 0`, and hence also absorbs the bounded-height constant.
-/

/-- The reciprocal zeta function with its removable value at the pole. -/
noncomputable def harperPoleRemovedZetaInv : ℂ → ℂ :=
  Function.update (fun s ↦ (riemannZeta s)⁻¹) 1 0

/-- The zeta residue implies continuity of the pole-removed reciprocal at `1`. -/
theorem continuousAt_harperPoleRemovedZetaInv_one :
    ContinuousAt harperPoleRemovedZetaInv 1 := by
  classical
  rw [harperPoleRemovedZetaInv, continuousAt_update_same]
  have hnum : Tendsto (fun s : ℂ ↦ s - 1) (𝓝[≠] 1) (𝓝 0) := by
    simpa using (tendsto_id.sub_const (1 : ℂ)).mono_left
      (show 𝓝[≠] (1 : ℂ) ≤ 𝓝 1 from inf_le_left)
  have h := hnum.div riemannZeta_residue_one (by norm_num : (1 : ℂ) ≠ 0)
  simp only [zero_div] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  simp [div_eq_mul_inv, mul_inv_rev, hs', mul_comm, mul_left_comm]

/-- The pole-removed reciprocal is continuous on the closed right half-plane. -/
theorem continuousOn_harperPoleRemovedZetaInv :
    ContinuousOn harperPoleRemovedZetaInv {s : ℂ | 1 ≤ s.re} := by
  classical
  intro s hs
  by_cases h : s = 1
  · subst s
    exact continuousAt_harperPoleRemovedZetaInv_one.continuousWithinAt
  · apply ContinuousAt.continuousWithinAt
    rw [harperPoleRemovedZetaInv, continuousAt_update_of_ne h]
    exact (differentiableAt_riemannZeta h).continuousAt.inv₀
      (riemannZeta_ne_zero_of_one_le_re hs)

/-- The actual Lean reciprocal, including the finite junk value at the pole,
is uniformly bounded on the bounded-height rectangle. -/
theorem exists_harperZetaInv_boundedHeight :
    ∃ C : ℝ, 0 < C ∧ ∀ (v u : ℝ), v ∈ Icc 1 2 → |u| ≤ 3 →
      1 / ‖riemannZeta (v + u * I)‖ ≤ C := by
  classical
  let K : Set ℂ := Icc (1 : ℝ) 2 ×ℂ Icc (-3 : ℝ) 3
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn (fun s ↦ ‖harperPoleRemovedZetaInv s‖) K :=
    (continuousOn_harperPoleRemovedZetaInv.mono fun s hs ↦ hs.1.1).norm
  obtain ⟨B, hB⟩ := hK.bddAbove_image hc
  refine ⟨max B (1 / ‖riemannZeta 1‖) + 1, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos
      ((show 0 ≤ 1 / ‖riemannZeta 1‖ by positivity).trans (le_max_right _ _)) zero_lt_one
  · intro v u hv hu
    by_cases h : (v : ℂ) + u * I = 1
    · rw [h]
      exact (le_max_right B (1 / ‖riemannZeta 1‖)).trans (le_add_of_nonneg_right zero_le_one)
    · have hs : (v : ℂ) + u * I ∈ K := by
        simpa [K, Complex.mem_reProdIm, abs_le] using And.intro hv (abs_le.mp hu)
      have hbound := hB (mem_image_of_mem (fun s ↦ ‖harperPoleRemovedZetaInv s‖) hs)
      have hbound' : 1 / ‖riemannZeta (v + u * I)‖ ≤ B := by
        simpa [harperPoleRemovedZetaInv, Function.update_of_ne h, norm_inv] using hbound
      calc
        _ ≤ B := hbound'
        _ ≤ max B (1 / ‖riemannZeta 1‖) := le_max_left _ _
        _ ≤ max B (1 / ‖riemannZeta 1‖) + 1 := by linarith

/-- A single reciprocal-zeta bound throughout every sufficiently thin spectral
window, with the seventh logarithmic power already available in the project. -/
theorem exists_harperZetaInv_spectralWindow :
    ∃ A : ℝ, A ∈ Ioc 0 (1 / 2) ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (H η : ℝ), 0 ≤ H → 0 ≤ η → η < A / Real.log (H + 4) ^ 9 →
      ∀ (v u : ℝ), v ∈ Icc 1 (1 + η) → |u| ≤ H →
        1 / ‖riemannZeta (v + u * I)‖ ≤ C * Real.log (H + 4) ^ 7 := by
  obtain ⟨A, hA, C, hC, hlarge⟩ := ZetaInvBnd
  obtain ⟨B, hB, hsmall⟩ := exists_harperZetaInv_boundedHeight
  refine ⟨A, hA, max B C, lt_max_of_lt_left hB, ?_⟩
  intro H η hH hη hwidth v u hv hu
  have hApos : 0 < A := hA.1
  have hlog : 1 < Real.log (H + 4) := by
    have := logt_gt_one (t := H + 4) (by linarith)
    simpa [abs_of_nonneg (show 0 ≤ H + 4 by linarith)] using this
  have hlog9 : 1 ≤ Real.log (H + 4) ^ 9 := one_le_pow₀ hlog.le
  have hlog7 : 1 ≤ Real.log (H + 4) ^ 7 := one_le_pow₀ hlog.le
  have hwidth_one : η ≤ 1 := by
    have hdiv : A / Real.log (H + 4) ^ 9 ≤ A := by
      exact div_le_self hA.1.le hlog9
    linarith [hA.2]
  by_cases ht : 3 < |u|
  · have hlogu : 0 < Real.log |u| := Real.log_pos (by linarith)
    have hlog_le : Real.log |u| ≤ Real.log (H + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    have hwidth_u : A / Real.log (H + 4) ^ 9 ≤ A / Real.log |u| ^ 9 := by
      gcongr
    have hv' : v ∈ Ico (1 - A / Real.log |u| ^ 9)
        (1 + A / Real.log |u| ^ 9) := by
      constructor
      · have : 0 ≤ A / Real.log |u| ^ 9 := by positivity
        linarith [hv.1]
      · linarith [hv.2]
    have hbound := hlarge v u ht hv'
    rw [show (7 : ℝ) = (7 : ℕ) by norm_num, Real.rpow_natCast] at hbound
    calc
      _ ≤ C * Real.log |u| ^ 7 := hbound
      _ ≤ max B C * Real.log (H + 4) ^ 7 := by gcongr; exact le_max_right _ _
  · calc
      _ ≤ B := hsmall v u ⟨hv.1, by linarith [hv.2]⟩ (le_of_not_gt ht)
      _ ≤ max B C := le_max_left _ _
      _ ≤ max B C * Real.log (H + 4) ^ 7 :=
        le_mul_of_one_le_right (le_trans hB.le (le_max_left _ _)) hlog7

/-- The candidate's logarithmic spectral height and inverse-time real shift
eventually fit every positive window constant. -/
theorem eventually_harperCandidate_zetaWindow_width
    {A κ : ℝ} (hA : 0 < A) (hκ : 0 ≤ κ) :
    ∀ᶠ T : ℝ in atTop,
      0 ≤ 2 * κ * Real.log (Real.log T) / T ∧
      2 * κ * Real.log (Real.log T) / T <
        A / Real.log (2 * Real.log T ^ 2 + 4) ^ 9 := by
  have hvanish : Tendsto (fun T : ℝ ↦
      (2 * κ * 3 ^ 9) * (Real.log T ^ 10 / T)) atTop (𝓝 0) := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := 10)).tendsto_div_nhds_zero
    simpa only [id_eq, mul_zero] using h.const_mul (2 * κ * 3 ^ 9)
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, hvanish.eventually (gt_mem_nhds hA)]
    with T hT hlogT hbound
  have hTpos : 0 < T := by linarith
  have hlogTnonneg : 0 ≤ Real.log T := by linarith
  have hloglog : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlogT
  have hargpos : 1 < 2 * Real.log T ^ 2 + 4 := by nlinarith [sq_nonneg (Real.log T)]
  have harglog : 0 < Real.log (2 * Real.log T ^ 2 + 4) := Real.log_pos hargpos
  have hpoly : 2 * T ^ 2 + 4 ≤ T ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg T) (show 0 ≤ T - 3 by linarith)]
  have harg : 2 * Real.log T ^ 2 + 4 ≤ T ^ 3 := by
    calc
      _ ≤ 2 * T ^ 2 + 4 := by gcongr; exact Real.log_le_self hTpos.le
      _ ≤ T ^ 3 := hpoly
  have hlogarg : Real.log (2 * Real.log T ^ 2 + 4) ≤ 3 * Real.log T := by
    calc
      _ ≤ Real.log (T ^ 3) := Real.log_le_log (by positivity) harg
      _ = 3 * Real.log T := by rw [Real.log_pow]; norm_num
  constructor
  · positivity
  · apply (lt_div_iff₀ (pow_pos harglog 9)).2
    calc
      _ ≤ 2 * κ * Real.log T / T * (3 * Real.log T) ^ 9 := by
        gcongr
        exact Real.log_le_self hTpos.le
      _ = (2 * κ * 3 ^ 9) * (Real.log T ^ 10 / T) := by ring
      _ < A := hbound

/-- The reciprocal-zeta estimate on the literal stationary candidate window,
uniform in both spectral coordinates for all sufficiently large `T`. -/
theorem exists_harperZetaInv_candidateWindow :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : ℝ), 0 ≤ κ →
      ∀ᶠ T : ℝ in atTop, ∀ (v u : ℝ),
        v ∈ Icc 1 (1 + 2 * κ * Real.log (Real.log T) / T) →
        |u| ≤ 2 * Real.log T ^ 2 →
        1 / ‖riemannZeta (v + u * I)‖ ≤
          C * Real.log (2 * Real.log T ^ 2 + 4) ^ 7 := by
  obtain ⟨A, hA, C, hC, hwindow⟩ := exists_harperZetaInv_spectralWindow
  refine ⟨C, hC, fun κ hκ ↦ ?_⟩
  filter_upwards [eventually_harperCandidate_zetaWindow_width hA.1 hκ] with T hT
  exact hwindow (2 * Real.log T ^ 2) (2 * κ * Real.log (Real.log T) / T)
    (by positivity) hT.1 hT.2

end Erdos.Problem1144
