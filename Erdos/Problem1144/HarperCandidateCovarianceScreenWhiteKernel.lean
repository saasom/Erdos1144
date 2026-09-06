import Erdos.Problem1144.HarperCandidateCovarianceScreenInverse

open MeasureTheory Set

namespace Erdos.Problem1144
noncomputable section

/-- Literal real white kernel after deleting a common measurable frequency
screen. Its reciprocal-time weight and integration window are unchanged. -/
def candidateEulerScreenWhiteKernel (Y : ℕ) (ω : Omega) (S : Set ℝ) (T B u : ℝ) : ℝ → ℝ :=
  (Ioc T B).indicator (fun r =>
    (candidateCovarianceScreenInverse (candidateEulerAngularApprox Y 0 ω) S (u - r)).re / Real.sqrt r)

/-- A symmetric frequency screen retains the real-valued Euler inverse. -/
theorem candidate_eulerScreenInverse_ofReal_re (Y : ℕ) (ω : Omega) {S : Set ℝ}
    (hS : MeasurableSet S) (hSym : ∀ τ, τ ∈ S ↔ -τ ∈ S) (u : ℝ) :
    ((candidateCovarianceScreenInverse (candidateEulerAngularApprox Y 0 ω) S u).re : ℂ) =
      candidateCovarianceScreenInverse (candidateEulerAngularApprox Y 0 ω) S u := by
  have hc := candidate_screenInverse_conj (candidate_criticalEuler_conj Y ω) hS hSym u
  have hi := congrArg Complex.im hc
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    simp only [Complex.conj_im] at hi
    linarith

private theorem real_white_sq_le (f : ℝ → ℂ) {T : ℝ} (hT : 0 < T) (B u r : ℝ) :
    ((Ioc T B).indicator (fun r => (f (u - r)).re / Real.sqrt r) r) ^ 2 ≤
      (Ioc T B).indicator (fun r => (1 / r) * ‖f (u - r)‖ ^ 2) r := by
  by_cases hr : r ∈ Ioc T B
  · have hr0 : 0 < r := hT.trans hr.1
    rw [indicator_of_mem hr, indicator_of_mem hr, div_pow, Real.sq_sqrt hr0.le]
    have he : (f (u - r)).re ^ 2 ≤ ‖f (u - r)‖ ^ 2 := by
      have hh := pow_le_pow_left₀ (abs_nonneg (f (u - r)).re) (Complex.abs_re_le_norm _) 2
      simpa only [sq_abs] using hh
    exact (div_le_div_of_nonneg_right he hr0.le).trans_eq (by ring)
  · simp [hr]

/-- Each actual screened white kernel is measurable. -/
theorem candidate_measurable_eulerScreenWhiteKernel (Y : ℕ) (ω : Omega)
    (S : Set ℝ) (T B u : ℝ) : Measurable (candidateEulerScreenWhiteKernel Y ω S T B u) := by
  have hi := candidate_measurable_screenInverse
    (candidate_continuous_criticalEulerAngularApprox Y ω).measurable S
  apply Measurable.indicator _ measurableSet_Ioc
  exact ((hi.comp (measurable_const.sub measurable_id)).re).div Real.continuous_sqrt.measurable

/-- Arbitrary measurable sub-band screens give actual `L²` white kernels.
Symmetry is unnecessary for this regularity assertion. -/
theorem candidate_memLp_eulerScreenWhiteKernel (Y : ℕ) (ω : Omega) {S : Set ℝ}
    (hS : MeasurableSet S) (H : ℝ) (hsub : S ⊆ Icc (-H) H) (B u : ℝ)
    {T : ℝ} (hT : 0 < T) : MemLp (candidateEulerScreenWhiteKernel Y ω S T B u) 2 := by
  have hf := candidate_memLp_two_screenInverse (candidate_continuous_criticalEulerAngularApprox Y ω)
    hS H hsub
  have hi := (candidate_reciprocal_translate_integral_le
    (hf.integrable_norm_pow (by decide : 2 ≠ 0)) (fun _ => sq_nonneg _) hT B u).1
  have hj := (hi.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hm := candidate_measurable_eulerScreenWhiteKernel Y ω S T B u
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply hj.mono' (hm.pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun r => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact real_white_sq_le _ hT B u r

/-- Uniform squared coefficient distance to the full `H`-band kernel.
Parseval pays exactly the deleted angular energy, and reciprocal translation
costs exactly `1/T`. There is no grid-size factor or analytic premise. -/
theorem candidate_eulerScreenWhiteKernel_distance_le (Y : ℕ) (ω : Omega) {S : Set ℝ}
    (hS : MeasurableSet S) (H : ℝ) (hsub : S ⊆ Icc (-H) H) (B u : ℝ)
    {T : ℝ} (hT : 0 < T) :
    (∫ r, (candidateEulerScreenWhiteKernel Y ω S T B u r -
      candidateEulerBandWhiteKernel Y ω H T B u r) ^ 2) ≤
        (1 / (2 * Real.pi * T)) * ∫ τ in Icc (-H) H \ S,
          ‖candidateEulerAngularApprox Y 0 ω τ‖ ^ 2 := by
  let A := candidateEulerAngularApprox Y 0 ω
  let f : ℝ → ℂ := fun x => candidateCovarianceBandInverse A H x - candidateCovarianceScreenInverse A S x
  have hf : MemLp f 2 := (candidate_memLp_two_finiteEuler_bandInverse Y ω H).sub
    (candidate_memLp_two_screenInverse (candidate_continuous_criticalEulerAngularApprox Y ω) hS H hsub)
  have hrec := candidate_reciprocal_translate_integral_le
    (hf.integrable_norm_pow (by decide : 2 ≠ 0)) (fun _ => sq_nonneg _) hT B u
  have hj := (hrec.1.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hleft : Integrable (fun r => (candidateEulerScreenWhiteKernel Y ω S T B u r -
      candidateEulerBandWhiteKernel Y ω H T B u r) ^ 2) := by
    exact ((candidate_memLp_eulerScreenWhiteKernel Y ω hS H hsub B u hT).sub
      (candidate_memLp_eulerBandWhiteKernel Y ω H B u hT)).integrable_sq
  have he (r : ℝ) : (candidateEulerScreenWhiteKernel Y ω S T B u r -
      candidateEulerBandWhiteKernel Y ω H T B u r) ^ 2 =
        ((Ioc T B).indicator (fun r => (f (u - r)).re / Real.sqrt r) r) ^ 2 := by
    by_cases hr : r ∈ Ioc T B
    · simp only [candidateEulerScreenWhiteKernel, candidateEulerBandWhiteKernel,
        indicator_of_mem hr, f, Complex.sub_re, sub_div, A]
      ring
    · simp [candidateEulerScreenWhiteKernel, candidateEulerBandWhiteKernel, hr]
  calc
    _ ≤ ∫ r, (Ioc T B).indicator (fun r => (1 / r) * ‖f (u - r)‖ ^ 2) r := by
      apply integral_mono hleft hj
      intro r
      dsimp only
      rw [he]
      exact real_white_sq_le f hT B u r
    _ = ∫ r in Icc T B, (1 / r) * ‖f (u - r)‖ ^ 2 := by
      rw [integral_indicator measurableSet_Ioc, integral_Icc_eq_integral_Ioc]
    _ ≤ (1 / T) * ∫ x, ‖f x‖ ^ 2 := hrec.2
    _ = _ := by
      rw [show (∫ x, ‖f x‖ ^ 2) = (2 * Real.pi)⁻¹ *
        ∫ τ in Icc (-H) H \ S, ‖A τ‖ ^ 2 from
          candidate_screenInverse_deletion_energy_eq
            (candidate_continuous_criticalEulerAngularApprox Y ω) hS H hsub]
      dsimp only [A]
      ring

end
end Erdos.Problem1144
