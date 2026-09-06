import Erdos.Problem1144.HarperCandidateCovariancePerronError
import Erdos.Problem1144.HarperCandidateTranslationWhiteKernel

open MeasureTheory Set FourierTransform
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- Real signs give the exact conjugation symmetry of the finite Euler
transform on the critical line. -/
theorem candidate_criticalEuler_conj (Y : ℕ) (ω : Omega) (τ : ℝ) :
    starRingEnd ℂ (candidateEulerAngularApprox Y 0 ω τ) =
      candidateEulerAngularApprox Y 0 ω (-τ) := by
  simp only [candidateEulerAngularApprox, harperRankinDirichletPolynomial, map_div₀,
    map_sum, map_mul, map_add, map_inv₀, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I, ← Complex.exp_conj, Complex.ofReal_mul, Complex.ofReal_neg,
    map_neg, neg_neg, neg_mul, mul_neg, zero_add, mul_zero]

private theorem symmetric_band_integral_neg (f : ℝ → ℂ) (H : ℝ) :
    (∫ τ in Icc (-H) H, f (-τ)) = ∫ τ in Icc (-H) H, f τ := by
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
  have he (τ : ℝ) : (Icc (-H) H).indicator (fun τ => f (-τ)) τ =
      (Icc (-H) H).indicator f (-τ) := by
    have hm : τ ∈ Icc (-H) H ↔ -τ ∈ Icc (-H) H := by
      simp only [mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    by_cases h : τ ∈ Icc (-H) H
    · simp [h, hm.mp h]
    · simp [h, hm.not.mp h]
  simp_rw [he]
  exact integral_neg_eq_self _ volume

/-- Symmetric finite frequency truncation preserves the real-valued Euler
partial-sum process exactly, not merely almost everywhere. -/
theorem candidate_finiteEuler_bandInverse_conj (Y : ℕ) (ω : Omega) (H u : ℝ) :
    starRingEnd ℂ (candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H u) =
      candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H u := by
  unfold candidateCovarianceBandInverse
  rw [map_mul]
  have hc : starRingEnd ℂ (2 * Real.pi : ℂ)⁻¹ = (2 * Real.pi : ℂ)⁻¹ := by
    rw [map_inv₀, map_mul,
      (show starRingEnd ℂ (2 : ℂ) = 2 from Complex.conj_ofReal 2), Complex.conj_ofReal]
  rw [hc]
  have he (τ : ℝ) : starRingEnd ℂ
      (candidateEulerAngularApprox Y 0 ω τ * candidateCovariancePhase (u * τ)) =
      candidateEulerAngularApprox Y 0 ω (-τ) * candidateCovariancePhase (u * (-τ)) := by
    rw [map_mul, candidate_criticalEuler_conj]
    congr 1
    simp [candidateCovariancePhase, ← Complex.exp_conj]
  have hi : starRingEnd ℂ (∫ τ in Icc (-H) H,
      candidateEulerAngularApprox Y 0 ω τ * candidateCovariancePhase (u * τ)) =
      ∫ τ in Icc (-H) H,
        candidateEulerAngularApprox Y 0 ω τ * candidateCovariancePhase (u * τ) := by
    calc
      _ = ∫ τ in Icc (-H) H, starRingEnd ℂ
          (candidateEulerAngularApprox Y 0 ω τ * candidateCovariancePhase (u * τ)) :=
        integral_conj.symm
      _ = ∫ τ in Icc (-H) H,
          candidateEulerAngularApprox Y 0 ω (-τ) * candidateCovariancePhase (u * (-τ)) := by
        simp_rw [he]
      _ = _ := symmetric_band_integral_neg
        (fun τ => candidateEulerAngularApprox Y 0 ω τ * candidateCovariancePhase (u * τ)) H
  rw [hi]

/-- The real coordinate of the finite band inverse represents the full
complex value; this identifies the Gaussian kernel's real Gram matrix. -/
theorem candidate_finiteEuler_bandInverse_ofReal_re (Y : ℕ) (ω : Omega) (H u : ℝ) :
    ((candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H u).re : ℂ) =
      candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H u := by
  have h := candidate_finiteEuler_bandInverse_conj Y ω H u
  have hi := congrArg Complex.im h
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    simpa only [Complex.conj_im] using (show
      (candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H u).im = 0 by
        simp only [Complex.conj_im] at hi
        linarith).symm

/-- A common-window real white kernel formed from the literal finite Euler
frequency truncation. The time window remains identical for all coordinates. -/
def candidateEulerBandWhiteKernel (Y : ℕ) (ω : Omega) (H T B u : ℝ) : ℝ → ℝ :=
  (Ioc T B).indicator (fun r =>
    (candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H (u - r)).re /
      Real.sqrt r)

/-- The real spectral kernel is jointly measurable in signs and white-noise time. -/
theorem candidate_measurable_eulerBandWhiteKernel (Y : ℕ) (H T B u : ℝ) :
    Measurable (fun z : Omega × ℝ => candidateEulerBandWhiteKernel Y z.1 H T B u z.2) := by
  have hP : Measurable (fun z : Omega × ℝ => (z.1, u - z.2)) :=
    measurable_fst.prodMk (measurable_const.sub measurable_snd)
  have hA : Measurable (fun z : Omega × ℝ =>
      candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 z.1) H (u - z.2)) :=
    (candidate_measurable_finiteEuler_bandInverse Y H).comp hP
  simp only [candidateEulerBandWhiteKernel, Set.indicator_apply]
  exact Measurable.ite (measurableSet_Ioc.preimage measurable_snd)
    (hA.re.div (Real.continuous_sqrt.measurable.comp measurable_snd)) measurable_const

/-- Each actual real Euler-band white kernel belongs to `L²`. -/
theorem candidate_memLp_eulerBandWhiteKernel (Y : ℕ) (ω : Omega) (H B u : ℝ)
    {T : ℝ} (hT : 0 < T) : MemLp (candidateEulerBandWhiteKernel Y ω H T B u) 2 := by
  have hm : Measurable (candidateEulerBandWhiteKernel Y ω H T B u) :=
    Measurable.of_uncurry_left
      (f := fun ω r => candidateEulerBandWhiteKernel Y ω H T B u r)
      (candidate_measurable_eulerBandWhiteKernel Y H T B u)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hi := (candidate_reciprocal_translate_integral_le
    ((candidate_memLp_two_finiteEuler_bandInverse Y ω H).integrable_norm_pow (by decide : 2 ≠ 0))
    (fun _ => sq_nonneg _) hT B u).1.mono_set Ioc_subset_Icc_self
  have hj := (integrable_indicator_iff measurableSet_Ioc).mpr hi
  apply hj.congr
  exact ae_of_all _ fun r => by
    by_cases hr : r ∈ Ioc T B
    · have hr0 : 0 ≤ r := (hT.trans hr.1).le
      simp only [candidateEulerBandWhiteKernel, indicator_of_mem hr]
      rw [← candidate_finiteEuler_bandInverse_ofReal_re Y ω H (u - r),
        Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hr0,
        Complex.ofReal_re]
      ring
    · simp [candidateEulerBandWhiteKernel, hr]

/-- Exact coefficient distance between the common-window real Euler kernel
and the actual white kernel. The right endpoint covers the actual support. -/
theorem candidate_eulerBandWhiteKernel_error_eq (Y : ℕ) (ω : Omega)
    (H B u : ℝ) {T : ℝ} (hT : 0 < T) (hu : u ≤ B) :
    (∫ r, (candidateEulerBandWhiteKernel Y ω H T B u r -
      candidateSquarefreeWhiteKernel ω u T r) ^ 2) =
      candidateWhiteEulerCutoffError Y ω H T B u := by
  have he (r : ℝ) : (candidateEulerBandWhiteKernel Y ω H T B u r -
      candidateSquarefreeWhiteKernel ω u T r) ^ 2 =
      (Ioc T B).indicator (fun r => (1 / r) *
        ‖candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H (u - r) -
          (harperCandidateSquarefreeLogProcess ω (u - r) : ℂ)‖ ^ 2) r := by
    by_cases hr : r ∈ Ioc T B
    · have hrT : r ∈ Ioi T := hr.1
      have hr0 : 0 ≤ r := (hT.trans hr.1).le
      rw [candidateEulerBandWhiteKernel, candidateSquarefreeWhiteKernel,
        indicator_of_mem hr, indicator_of_mem hrT, indicator_of_mem hr,
        ← candidate_finiteEuler_bandInverse_ofReal_re Y ω H (u - r),
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        ← sub_div, div_pow, Real.sq_sqrt hr0]
      simp only [Complex.ofReal_re]
      ring
    · have ha : candidateSquarefreeWhiteKernel ω u T r = 0 := by
        by_cases hrT : T < r
        · have hrB : B < r := by
            have := hr
            simp only [mem_Ioc, not_and, not_le] at this
            exact this hrT
          have hneg : ¬0 ≤ u - r := by linarith
          simp only [candidateSquarefreeWhiteKernel, indicator_of_mem (show r ∈ Ioi T from hrT),
            harperCandidateSquarefreeLogProcess, if_neg hneg, zero_div]
        · simp [candidateSquarefreeWhiteKernel, hrT]
      simp [candidateEulerBandWhiteKernel, hr, ha]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioc]
  exact (integral_Icc_eq_integral_Ioc (μ := volume)).symm

/-- The squared distance of the actual Gaussian kernels is integrable. -/
theorem candidate_integrable_eulerBandWhiteKernel_error (Y : ℕ) {H T : ℝ}
    (hH : 0 < H) (hT : 0 < T) (B u : ℝ) (hu : u ≤ B)
    (hY : ⌊Real.exp (u - T)⌋₊ ≤ Y) :
    Integrable (fun ω => ∫ r, (candidateEulerBandWhiteKernel Y ω H T B u r -
      candidateSquarefreeWhiteKernel ω u T r) ^ 2) mu := by
  simp_rw [candidate_eulerBandWhiteKernel_error_eq Y _ H B u hT hu]
  exact candidate_integrable_whiteEulerCutoffError Y hH hT B u hY

/-- The actual Gaussian kernel distance has the fully proved arithmetic
bound, with the exact spectral and logarithmic-time normalizations. -/
theorem candidate_integral_eulerBandWhiteKernel_error_le (Y : ℕ) {H T : ℝ}
    (hH : 0 < H) (hT : 0 < T) (B u : ℝ) (hu : u ≤ B)
    (hY : ⌊Real.exp (u - T)⌋₊ ≤ Y) :
    (∫ ω, (∫ r, (candidateEulerBandWhiteKernel Y ω H T B u r -
      candidateSquarefreeWhiteKernel ω u T r) ^ 2) ∂mu) ≤
      harperRankinPrimeEnergyNormalizer Y 0 / (Real.pi * T * H) := by
  simp_rw [candidate_eulerBandWhiteKernel_error_eq Y _ H B u hT hu]
  exact candidate_integral_whiteEulerCutoffError_le Y hH hT B u hY

/-- At `Y=floor(exp T)`, the literal real Gaussian kernels have expected
squared distance `O(1/H)`, uniformly over the entire common time window. -/
theorem candidate_exists_eulerBandWhiteKernel_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (T H B u : ℝ), Real.log 2 ≤ T → 0 < H →
      u ≤ 2 * T → u ≤ B →
      (∫ ω, (∫ r, (candidateEulerBandWhiteKernel ⌊Real.exp T⌋₊ ω H T B u r -
        candidateSquarefreeWhiteKernel ω u T r) ^ 2) ∂mu) ≤ C / H := by
  obtain ⟨C, hC, hb⟩ := candidate_exists_exponential_whiteEulerCutoffError_bound
  refine ⟨C, hC, ?_⟩
  intro T H B u hTlog hH hu huB
  have hT : 0 < T := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hTlog
  simp_rw [candidate_eulerBandWhiteKernel_error_eq _ _ H B u hT huB]
  exact hb T H B u hTlog hH hu

/-- The real Gaussian Gram entry equals the literal finite Euler double
integral with the exact common-window kernel and `(2π)⁻²` normalization. -/
theorem candidate_eulerBandWhiteKernel_covariance_eq (Y : ℕ) (ω : Omega)
    (H B u v : ℝ) {T : ℝ} (hT : 0 < T) :
    ((∫ r, candidateEulerBandWhiteKernel Y ω H T B u r *
      candidateEulerBandWhiteKernel Y ω H T B v r : ℝ) : ℂ) =
    (2 * Real.pi : ℂ)⁻¹ ^ 2 * ∫ z : ℝ × ℝ,
      candidateEulerAngularApprox Y 0 ω z.1 *
        starRingEnd ℂ (candidateEulerAngularApprox Y 0 ω z.2) *
        candidateCovariancePhase (u * z.1 - v * z.2) *
        candidateCovarianceWhiteKernel T B (z.1 - z.2)
        ∂(volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H)) := by
  have he : ((∫ r, candidateEulerBandWhiteKernel Y ω H T B u r *
      candidateEulerBandWhiteKernel Y ω H T B v r : ℝ) : ℂ) =
      ∫ r in Icc T B, ((1 / r : ℝ) : ℂ) *
        candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H (u - r) *
        starRingEnd ℂ
          (candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H (v - r)) := by
    rw [← integral_complex_ofReal, integral_Icc_eq_integral_Ioc,
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact ae_of_all _ fun r => by
      by_cases hr : r ∈ Ioc T B
      · have hr0 : 0 ≤ r := (hT.trans hr.1).le
        simp only [candidateEulerBandWhiteKernel, indicator_of_mem hr]
        have ha :
            (candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H (u - r)).re /
              Real.sqrt r *
              ((candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H (v - r)).re /
                Real.sqrt r) =
            (1 / r) *
              (candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H (u - r)).re *
              (candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H (v - r)).re := by
          rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hr0]
          ring
        rw [ha]
        simp only [Complex.ofReal_mul, candidate_finiteEuler_bandInverse_ofReal_re,
          candidate_finiteEuler_bandInverse_conj]
      · simp [candidateEulerBandWhiteKernel, hr]
  exact he.trans (candidate_finiteEuler_white_band_covariance_eq Y ω H u v B hT)

end
end Erdos.Problem1144
