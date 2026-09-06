import Erdos.Problem1144.HarperCandidateGaussianAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter MeasureTheory
open scoped Topology

namespace Erdos.Problem1144

/-- The actual schedule weight loses less than every positive power of
logarithmic time. -/
theorem candidateScheduleW_sq_div_rpow_tendsto (κ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T : ℝ => candidateScheduleW κ T ^ 2 / T ^ ε) atTop (nhds 0) := by
  have hh := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) hε).tendsto_div_nhds_zero).const_mul
    (κ ^ 2)
  simp only [Real.rpow_ofNat, mul_zero] at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    positivity
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_gt_atTop (0 : ℝ)] with T hlog hT
    have hll := Real.log_nonneg hlog
    have hle := Real.log_le_self (by linarith : 0 ≤ Real.log T)
    dsimp only [candidateScheduleW]
    rw [mul_pow, ← mul_div_assoc]
    gcongr

/-- The literal integer grid contains more than every sublinear power of
time. The floor error is included, with no cardinality assumption. -/
theorem candidateScheduleM_div_rpow_tendsto {κ a : ℝ} (hκ : 0 < κ) (ha : a < 1) :
    Tendsto (fun T : ℝ => (candidateScheduleM κ T : ℝ) / T ^ a) atTop atTop := by
  let L : ℝ → ℝ := fun T => candidateScheduleD κ T / (2 * Real.pi)
  have hL : Tendsto L atTop atTop :=
    (candidateScheduleD_tendsto hκ).atTop_div_const (by positivity)
  have hsmall : Tendsto (fun T : ℝ => candidateScheduleW κ T ^ 2 / T ^ (1 - a))
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨candidateScheduleW_sq_div_rpow_tendsto κ (by linarith), ?_⟩
    filter_upwards [(candidateScheduleW_tendsto hκ).eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℝ)] with T hW hT
    exact div_pos (sq_pos_of_pos hW) (Real.rpow_pos_of_pos hT _)
  have hquot : Tendsto (fun T : ℝ => L T / T ^ a) atTop atTop := by
    have hh := (tendsto_inv_nhdsGT_zero.comp hsmall).atTop_div_const
      (by positivity : 0 < 2 * Real.pi)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    dsimp only [L, candidateScheduleD, Function.comp_def]
    rw [inv_div, Real.rpow_sub hT, Real.rpow_one]
    ring
  have hf := tendsto_nat_floor_div_atTop.comp hL
  have hh := hf.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hquot
  apply hh.congr'
  filter_upwards [hL.eventually_gt_atTop 0] with T hLT
  dsimp only [Function.comp_def]
  change (⌊L T⌋₊ : ℝ) / L T * (L T / T ^ a) = _
  rw [div_mul_div_cancel₀ hLT.ne']
  rfl

/-- The actual retained-set factory leaves a polynomially large thinner
family for every sublinear degree bound. The result holds for every old
field and threshold, including the literal scheduled old-negative selector. -/
theorem candidateSchedule_retained_card_div_degree_ge_rpow
    {κ ρ a γ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (ha : 0 ≤ a) (haγ : a + γ < 1) :
    ∀ᶠ T : ℝ in atTop,
      ∀ (A : Omega → Fin (candidateScheduleM κ T) → ℝ) (b : ℝ) (ω : Omega) (d : ℕ),
      (d : ℝ) ≤ T ^ a →
      T ^ γ ≤ (candidateRetainedIndices A b ρ ω).card / (d + 1 : ℝ) := by
  have hM := ((candidateScheduleM_div_rpow_tendsto hκ haγ).const_mul_atTop hρ).eventually_ge_atTop 2
  filter_upwards [hM, eventually_ge_atTop (1 : ℝ)] with T hM hT1
  intro A b ω d hd
  have hT : 0 < T := by linarith
  have hTa : 1 ≤ T ^ a := Real.one_le_rpow hT1 ha
  have hdeg : (d : ℝ) + 1 ≤ 2 * T ^ a := by linarith
  have hsize : 2 * T ^ (a + γ) ≤ ρ * (candidateScheduleM κ T : ℝ) := by
    rw [← mul_div_assoc] at hM
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hT _)).mp hM
  have hret := candidateRetainedIndices_card_lower A b ρ hρ1 ω
  simp only [Fintype.card_fin] at hret
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < d + 1)).mpr
  calc
    _ ≤ T ^ γ * (2 * T ^ a) :=
      mul_le_mul_of_nonneg_left hdeg (Real.rpow_pos_of_pos hT _).le
    _ = 2 * T ^ (a + γ) := by rw [Real.rpow_add hT]; ring
    _ ≤ _ := hsize.trans hret

end Erdos.Problem1144
