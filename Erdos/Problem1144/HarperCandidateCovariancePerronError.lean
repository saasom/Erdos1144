import Erdos.Problem1144.HarperCandidateCovariancePerronTail

open MeasureTheory Set
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- Reciprocal-time weighting and translation cost at most `1/T` in `L¹`.
Both the weighted integral's existence and its bound are proved. -/
theorem candidate_reciprocal_translate_integral_le {f : ℝ → ℝ}
    (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x) {T : ℝ} (hT : 0 < T) (B u : ℝ) :
    IntegrableOn (fun r => (1 / r) * f (u - r)) (Icc T B) ∧
      (∫ r in Icc T B, (1 / r) * f (u - r)) ≤ (1 / T) * ∫ x, f x := by
  have hi : IntegrableOn (fun r => (1 / T) * f (u - r)) (Icc T B) :=
    ((hf.comp_sub_left u).restrict).const_mul _
  have hm : AEStronglyMeasurable (fun r => (1 / r) * f (u - r))
      (volume.restrict (Icc T B)) :=
    (measurable_const.div measurable_id).aestronglyMeasurable.mul
      (hf.comp_sub_left u).aestronglyMeasurable.restrict
  have hb : ∀ᵐ r ∂volume.restrict (Icc T B),
      (1 / r) * f (u - r) ≤ (1 / T) * f (u - r) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact mul_le_mul_of_nonneg_right
      (one_div_le_one_div_of_le hT hr.1) (hf0 _)
  have h0 : ∀ᵐ r ∂volume.restrict (Icc T B), 0 ≤ (1 / r) * f (u - r) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact mul_nonneg (one_div_nonneg.mpr (hT.le.trans hr.1)) (hf0 _)
  have hfi : IntegrableOn (fun r => (1 / r) * f (u - r)) (Icc T B) := by
    apply hi.mono' hm
    filter_upwards [hb, h0] with r hr hr0
    simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr
  refine ⟨hfi, (integral_mono_ae hfi hi hb).trans ?_⟩
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hT.le)
  calc
    _ ≤ ∫ r, f (u - r) := integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ fun r => hf0 _) (hf.comp_sub_left u)
    _ = _ := integral_sub_left_eq_self f volume u

/-- The actual white coefficient error at time `u`, with the reciprocal-time
weight from the literal white covariance. -/
def candidateWhiteEulerCutoffError (Y : ℕ) (ω : Omega) (H T B u : ℝ) : ℝ :=
  ∫ r in Icc T B, (1 / r) *
    ‖candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H (u - r) -
      (harperCandidateSquarefreeLogProcess ω (u - r) : ℂ)‖ ^ 2

/-- The actual squarefree process may replace the finite smooth process on
the whole coefficient window as soon as its left endpoint lies below `Y`. -/
theorem candidate_whiteEulerCutoffError_le_time_error (Y : ℕ) (ω : Omega)
    (H B u : ℝ) {T : ℝ} (hT : 0 < T) (hY : ⌊Real.exp (u - T)⌋₊ ≤ Y) :
    candidateWhiteEulerCutoffError Y ω H T B u ≤
      (1 / T) * ∫ x,
        ‖candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H x -
          candidateEulerLogProcess Y ω x‖ ^ 2 := by
  have he : candidateWhiteEulerCutoffError Y ω H T B u =
      ∫ r in Icc T B, (1 / r) *
        ‖candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H (u - r) -
          candidateEulerLogProcess Y ω (u - r)‖ ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    dsimp only
    rw [candidate_eulerLogProcess_eq_squarefree Y ω
      ((Nat.floor_le_floor (Real.exp_le_exp.mpr (sub_le_sub_left hr.1 u))).trans hY)]
  rw [he]
  exact (candidate_reciprocal_translate_integral_le
    (candidate_integrable_finiteEuler_cutoff_error_sq Y ω H)
    (fun _ => sq_nonneg _) hT B u).2

theorem candidateWhiteEulerCutoffError_nonneg (Y : ℕ) (ω : Omega) (H B u : ℝ)
    {T : ℝ} (hT : 0 ≤ T) : 0 ≤ candidateWhiteEulerCutoffError Y ω H T B u := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  exact mul_nonneg (one_div_nonneg.mpr (hT.trans hr.1)) (sq_nonneg _)

theorem candidate_measurable_whiteEulerCutoffError (Y : ℕ) (H T B u : ℝ) :
    Measurable (fun ω => candidateWhiteEulerCutoffError Y ω H T B u) := by
  have hP : Measurable (fun z : Omega × ℝ => (z.1, u - z.2)) :=
    measurable_fst.prodMk (measurable_const.sub measurable_snd)
  have hA : Measurable (fun z : Omega × ℝ =>
      candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 z.1) H (u - z.2)) :=
    (candidate_measurable_finiteEuler_bandInverse Y H).comp hP
  have hM : Measurable (fun z : Omega × ℝ =>
      (harperCandidateSquarefreeLogProcess z.1 (u - z.2) : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_harperCandidateSquarefreeLogProcess.comp hP)
  have hF : Measurable (fun z : Omega × ℝ => (1 / z.2) *
      ‖candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 z.1) H (u - z.2) -
        (harperCandidateSquarefreeLogProcess z.1 (u - z.2) : ℂ)‖ ^ 2) :=
    (measurable_const.div measurable_snd).mul ((hA.sub hM).norm.pow_const 2)
  exact (StronglyMeasurable.integral_prod_right
    (f := fun ω r => (1 / r) *
      ‖candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H (u - r) -
        (harperCandidateSquarefreeLogProcess ω (u - r) : ℂ)‖ ^ 2)
    (ν := volume.restrict (Icc T B)) hF.stronglyMeasurable).measurable

/-- The literal white coefficient error is integrable over the original
prime signs; no finite-cube regularity assumption is required. -/
theorem candidate_integrable_whiteEulerCutoffError (Y : ℕ) {H T : ℝ}
    (hH : 0 < H) (hT : 0 < T) (B u : ℝ) (hY : ⌊Real.exp (u - T)⌋₊ ≤ Y) :
    Integrable (fun ω => candidateWhiteEulerCutoffError Y ω H T B u) mu := by
  apply ((candidate_integrable_mean_finiteEuler_cutoff_error Y hH).const_mul (1 / T)).mono'
    (candidate_measurable_whiteEulerCutoffError Y H T B u).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (candidateWhiteEulerCutoffError_nonneg Y ω H B u hT.le)]
    exact candidate_whiteEulerCutoffError_le_time_error Y ω H B u hT hY

/-- The actual white-field coefficient has expected spectral-cutoff error at
most `N_Y(0)/(πTH)`, uniformly over its permitted time window. -/
theorem candidate_integral_whiteEulerCutoffError_le (Y : ℕ) {H T : ℝ}
    (hH : 0 < H) (hT : 0 < T) (B u : ℝ) (hY : ⌊Real.exp (u - T)⌋₊ ≤ Y) :
    (∫ ω, candidateWhiteEulerCutoffError Y ω H T B u ∂mu) ≤
      harperRankinPrimeEnergyNormalizer Y 0 / (Real.pi * T * H) := by
  have h := integral_mono (candidate_integrable_whiteEulerCutoffError Y hH hT B u hY)
    ((candidate_integrable_mean_finiteEuler_cutoff_error Y hH).const_mul (1 / T))
    (fun ω => candidate_whiteEulerCutoffError_le_time_error Y ω H B u hT hY)
  rw [integral_const_mul] at h
  refine h.trans ?_
  have hb := mul_le_mul_of_nonneg_left (candidate_integral_finiteEuler_cutoff_error_le Y hH)
    (one_div_nonneg.mpr hT.le)
  convert hb using 1 <;> ring

/-- The Mertens theorem cancels the logarithmic prime-cutoff scale: the
literal white coefficient error is bounded by an absolute constant over `H`.
All cutoff and endpoint conditions here are deterministic geometry. -/
theorem candidate_exists_whiteEulerCutoffError_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℕ) (H T B u : ℝ),
      2 ≤ Y → 0 < H → 0 < T → Real.log (Y : ℝ) ≤ T →
      ⌊Real.exp (u - T)⌋₊ ≤ Y →
      (∫ ω, candidateWhiteEulerCutoffError Y ω H T B u ∂mu) ≤ C / H := by
  let C₀ := Real.exp (1 - Real.log (Real.log 2) +
    2 * (Real.log 4 + 4) / Real.log 2)
  refine ⟨C₀ / Real.pi, div_pos (Real.exp_pos _) Real.pi_pos, ?_⟩
  intro Y H T B u hY hH hT hlog hcut
  have hN : harperRankinPrimeEnergyNormalizer Y 0 ≤ C₀ * T := by
    rw [candidate_critical_rankinNormalizer_eq]
    exact (Problem520.primeEnergyNormalizer_le_mertensConstant_mul_log hY).trans
      (mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le)
  refine (candidate_integral_whiteEulerCutoffError_le Y hH hT B u hcut).trans ?_
  refine (div_le_div_of_nonneg_right hN (by positivity)).trans_eq ?_
  field_simp

/-- At the literal prime cutoff `floor(exp T)`, every time up to `2T` has
white coefficient error `O(1/H)`, uniformly in the right integration endpoint. -/
theorem candidate_exists_exponential_whiteEulerCutoffError_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (T H B u : ℝ), Real.log 2 ≤ T → 0 < H → u ≤ 2 * T →
      (∫ ω, candidateWhiteEulerCutoffError ⌊Real.exp T⌋₊ ω H T B u ∂mu) ≤ C / H := by
  obtain ⟨C, hC, hb⟩ := candidate_exists_whiteEulerCutoffError_uniform_bound
  refine ⟨C, hC, ?_⟩
  intro T H B u hTlog hH hu
  have hT : 0 < T := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hTlog
  have hY : 2 ≤ ⌊Real.exp T⌋₊ := by
    apply (Nat.le_floor_iff (Real.exp_pos T).le).mpr
    exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).mp hTlog
  have hlog : Real.log (⌊Real.exp T⌋₊ : ℝ) ≤ T := by
    apply (Real.log_le_iff_le_exp (by exact_mod_cast (show 0 < ⌊Real.exp T⌋₊ by omega))).mpr
    exact Nat.floor_le (Real.exp_pos T).le
  exact hb _ H T B u hY hH hT hlog
    (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith)))

end
end Erdos.Problem1144
