import Erdos.Problem1144.HarperCandidateCovarianceKernelRow

open MeasureTheory Set
open scoped Interval

namespace Erdos.Problem1144
noncomputable section

/-- The literal local absolute mass of the reciprocal-time covariance kernel. -/
def candidateCovarianceLocalKernelMass (T B d : ℝ) : ℝ :=
  ∫ h in Icc (-d) d, ‖candidateCovarianceWhiteKernel T B h‖

/-- A continuous reciprocal majorant combines both previously proved
pointwise kernel estimates without a singularity at zero frequency. -/
theorem candidate_whiteKernel_norm_le_reciprocal
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (h : ℝ) :
    ‖candidateCovarianceWhiteKernel T B h‖ ≤
      (Real.log (B / T) + 2) / (1 + T * |h|) := by
  have h₁ := candidate_whiteKernel_norm_le_log hT hTB h
  have h₂ : ‖candidateCovarianceWhiteKernel T B h‖ * (T * |h|) ≤ 2 := by
    by_cases hh : h = 0
    · simp [hh]
    · exact (le_div_iff₀ (mul_pos hT (abs_pos.mpr hh))).mp
        (candidate_whiteKernel_norm_le_inverse_gap hT hTB hh)
  apply (le_div_iff₀ (by positivity : 0 < 1 + T * |h|)).mpr
  nlinarith

private theorem reciprocal_integral {T d : ℝ} (hT : 0 < T) (hd : 0 ≤ d) :
    (∫ h in Icc (-d) d, (1 + T * |h|)⁻¹) = 2 * Real.log (1 + T * d) / T := by
  let f := fun h : ℝ => (1 + T * |h|)⁻¹
  have hc : Continuous f := by
    apply Continuous.inv₀
    · fun_prop
    · intro h
      positivity
  have hp : (∫ h in (0 : ℝ)..d, (1 + T * h)⁻¹) = Real.log (1 + T * d) / T := by
    have hder (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) d) :
        HasDerivAt (fun t => Real.log (1 + T * t) / T) ((1 + T * x)⁻¹) x := by
      have hx0 : 0 ≤ x := (uIcc_of_le hd ▸ hx).1
      have hxpos : 0 < 1 + T * x := by positivity
      convert (((hasDerivAt_const x (1 : ℝ)).add
        ((hasDerivAt_id x).const_mul T)).log hxpos.ne').div_const T using 1 <;>
        dsimp <;> field_simp <;> ring
    have hi : IntervalIntegrable (fun x : ℝ => (1 + T * x)⁻¹) volume 0 d := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.inv₀
      · fun_prop
      · intro x hx
        have hx0 : 0 ≤ x := (uIcc_of_le hd ▸ hx).1
        positivity
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi
    simpa using he
  have hp' : (∫ h in (0 : ℝ)..d, f h) = Real.log (1 + T * d) / T := by
    rw [← hp]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 ≤ x := (uIcc_of_le hd ▸ hx).1
    simp only [f, abs_of_nonneg hx0]
  have hn : (∫ h in (-d)..(0 : ℝ), f h) = ∫ h in (0 : ℝ)..d, f h := by
    have he := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := d)
    simpa only [f, abs_neg, neg_zero] using he.symm
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -d ≤ d)]
  change (∫ h in (-d)..d, f h) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-d) 0) (hc.intervalIntegrable 0 d), hn, hp']
  ring

theorem candidate_integrable_local_whiteKernel_norm {T B : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (d : ℝ) :
    IntegrableOn (fun h => ‖candidateCovarianceWhiteKernel T B h‖) (Icc (-d) d) := by
  apply (integrable_const (Real.log (B / T))).mono'
    (candidate_measurable_whiteKernel T B).norm.aestronglyMeasurable
  exact ae_of_all _ fun h => by
    rw [Real.norm_eq_abs, abs_norm]
    exact candidate_whiteKernel_norm_le_log hT hTB h

theorem candidateCovarianceLocalKernelMass_nonneg (T B d : ℝ) :
    0 ≤ candidateCovarianceLocalKernelMass T B d := integral_nonneg fun _ => norm_nonneg _

/-- Sharp logarithmic local mass, uniform in the near-diagonal width. For
fixed `B/T` its only dependence on the width is `log(1+T*d)/T`. -/
theorem candidate_local_whiteKernel_mass_le {T B d : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (hd : 0 ≤ d) :
    candidateCovarianceLocalKernelMass T B d ≤
      2 * (Real.log (B / T) + 2) * Real.log (1 + T * d) / T := by
  have hi : IntegrableOn (fun h : ℝ => (Real.log (B / T) + 2) / (1 + T * |h|))
      (Icc (-d) d) := by
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      positivity
  calc
    _ ≤ ∫ h in Icc (-d) d, (Real.log (B / T) + 2) / (1 + T * |h|) :=
      integral_mono (candidate_integrable_local_whiteKernel_norm hT hTB d) hi
        (candidate_whiteKernel_norm_le_reciprocal hT hTB)
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [integral_const_mul, reciprocal_integral hT hd]
      ring

/-- Translation preserves the whole local kernel mass, so arbitrary finite
frequency windows and scalar screens can only decrease a kernel row. -/
theorem candidate_integral_local_whiteKernel_row_le {T B : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (d t : ℝ) (S : Set ℝ) :
    (∫ v in S, (Icc (-d) d).indicator
      (fun h => ‖candidateCovarianceWhiteKernel T B h‖) (t - v)) ≤
      candidateCovarianceLocalKernelMass T B d := by
  have hi : Integrable ((Icc (-d) d).indicator
      (fun h => ‖candidateCovarianceWhiteKernel T B h‖)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (candidate_integrable_local_whiteKernel_norm hT hTB d)
  calc
    _ ≤ ∫ v, (Icc (-d) d).indicator
        (fun h => ‖candidateCovarianceWhiteKernel T B h‖) (t - v) :=
      setIntegral_le_integral (hi.comp_sub_left t)
        (ae_of_all _ fun _ => indicator_nonneg (fun h _ => norm_nonneg _) _)
    _ = _ := by
      rw [integral_sub_left_eq_self, integral_indicator measurableSet_Icc]
      rfl

end
end Erdos.Problem1144
