import Erdos.Problem1144.HarperCandidateCovarianceRowFourier
import Erdos.Problem1144.HarperCandidateCovariancePerronErrorWhite
import Erdos.Problem1144.HarperCandidateCovarianceKernelRow

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- The literal Fourier amplitude of a fixed row of the finite Euler-band
Gram matrix; the second endpoint enters only through its Fourier phase. -/
def candidateEulerBandRowAmplitude (Y : ℕ) (ω : Omega) (T B u : ℝ) (z : ℝ × ℝ) : ℂ :=
  candidateEulerAngularApprox Y 0 ω z.1 * starRingEnd ℂ (candidateEulerAngularApprox Y 0 ω z.2) *
    candidateCovariancePhase (u * z.1) * candidateCovarianceWhiteKernel T B (z.1 - z.2)

/-- The actual paired Euler amplitudes and reciprocal-time kernel weight. -/
def candidateEulerBandRowWeight (Y : ℕ) (ω : Omega) (T B : ℝ) (z : ℝ × ℝ) : ℝ :=
  ‖candidateEulerAngularApprox Y 0 ω z.1‖ * ‖candidateEulerAngularApprox Y 0 ω z.2‖ *
    ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖

/-- Removing the row endpoint costs nothing because its phase has unit norm. -/
theorem candidate_eulerBandRowAmplitude_norm (Y : ℕ) (ω : Omega) (T B u : ℝ) (z : ℝ × ℝ) :
    ‖candidateEulerBandRowAmplitude Y ω T B u z‖ = candidateEulerBandRowWeight Y ω T B z := by
  have hp : ‖candidateCovariancePhase (u * z.1)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  simp only [candidateEulerBandRowAmplitude, candidateEulerBandRowWeight, norm_mul,
    Complex.norm_conj, hp, mul_one]

theorem candidate_measurable_eulerBandRowAmplitude (Y : ℕ) (ω : Omega) (T B u : ℝ) :
    Measurable (candidateEulerBandRowAmplitude Y ω T B u) := by
  have hA := (candidate_continuous_criticalEulerAngularApprox Y ω).measurable
  have hK := candidate_measurable_whiteKernel T B
  unfold candidateEulerBandRowAmplitude candidateCovariancePhase
  fun_prop

/-- Every literal row amplitude is integrable over the finite frequency
square, including an arbitrary further restriction used by a screen. -/
theorem candidate_integrable_eulerBandRowAmplitude (Y : ℕ) (ω : Omega)
    (H u : ℝ) {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (E : Set (ℝ × ℝ)) :
    Integrable (candidateEulerBandRowAmplitude Y ω T B u)
      (((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict E) := by
  have hA : Integrable (candidateEulerAngularApprox Y 0 ω)
      (volume.restrict (Icc (-H) H)) :=
    (candidate_continuous_criticalEulerAngularApprox Y ω).integrableOn_Icc
  have hm := (hA.norm.mul_prod hA.norm).mul_const (Real.log (B / T))
  apply (hm.mono' (candidate_measurable_eulerBandRowAmplitude Y ω T B u).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)).mono_measure Measure.restrict_le_self
  rw [candidate_eulerBandRowAmplitude_norm]
  exact mul_le_mul_of_nonneg_left (candidate_whiteKernel_norm_le_log hT hTB _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

private theorem row_phase (Y : ℕ) (ω : Omega) (T B u v : ℝ) (z : ℝ × ℝ) :
    candidateEulerAngularApprox Y 0 ω z.1 * starRingEnd ℂ (candidateEulerAngularApprox Y 0 ω z.2) *
      candidateCovariancePhase (u * z.1 - v * z.2) * candidateCovarianceWhiteKernel T B (z.1 - z.2) =
      candidateEulerBandRowAmplitude Y ω T B u z * candidateCovariancePhase (-v * z.2) := by
  have he : candidateCovariancePhase (u * z.1 - v * z.2) =
      candidateCovariancePhase (u * z.1) * candidateCovariancePhase (-v * z.2) := by
    simp only [candidateCovariancePhase, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  unfold candidateEulerBandRowAmplitude
  ring

/-- Exact `2k`-power expansion of a restricted literal Euler covariance row
summed on an affine grid. The restrictions may be the actual joint frequency
screen and a near-diagonal set. Every Fubini premise is discharged. -/
theorem candidate_eulerBand_restricted_row_power_sum_eq (Y : ℕ) (ω : Omega)
    (H u v h : ℝ) {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B)
    (E : Set (ℝ × ℝ)) (n k : ℕ) :
    let ν := ((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict E
    ((∑ j ∈ range n, ‖∫ z, candidateEulerAngularApprox Y 0 ω z.1 *
      starRingEnd ℂ (candidateEulerAngularApprox Y 0 ω z.2) *
      candidateCovariancePhase (u * z.1 - (v + j * h) * z.2) *
      candidateCovarianceWhiteKernel T B (z.1 - z.2) ∂ν‖ ^ (2 * k) : ℝ) : ℂ) =
    ∫ z, candidateRowPowerAmplitude (candidateEulerBandRowAmplitude Y ω T B u) z *
      candidateCovariancePhase (-v * candidateRowPowerFrequency Prod.snd z) *
      candidateRowFourierSum n (-h) (candidateRowPowerFrequency Prod.snd z)
      ∂candidateRowPowerMeasure ν k := by
  dsimp only
  simp_rw [row_phase, show ∀ j : ℕ, -(v + j * h) = -v + j * (-h) by intro j; ring]
  exact candidate_fourier_row_power_sum_eq _
    (candidate_measurable_eulerBandRowAmplitude Y ω T B u)
    (candidate_integrable_eulerBandRowAmplitude Y ω H u hT hTB E) measurable_snd (-v) (-h) n k

/-- The literal discrete row mean value, with its resonance weight retained.
The bound is independent of both the fixed row endpoint and the grid origin. -/
theorem candidate_eulerBand_restricted_row_power_sum_le (Y : ℕ) (ω : Omega)
    (H u v h : ℝ) {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B)
    (E : Set (ℝ × ℝ)) (n k : ℕ) :
    let ν := ((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))).restrict E
    (∑ j ∈ range n, ‖∫ z, candidateEulerAngularApprox Y 0 ω z.1 *
      starRingEnd ℂ (candidateEulerAngularApprox Y 0 ω z.2) *
      candidateCovariancePhase (u * z.1 - (v + j * h) * z.2) *
      candidateCovarianceWhiteKernel T B (z.1 - z.2) ∂ν‖ ^ (2 * k)) ≤
    ∫ z, ((∏ i, candidateEulerBandRowWeight Y ω T B (z.1 i)) *
      ∏ i, candidateEulerBandRowWeight Y ω T B (z.2 i)) *
      ‖candidateRowFourierSum n (-h) (candidateRowPowerFrequency Prod.snd z)‖
      ∂candidateRowPowerMeasure ν k := by
  dsimp only
  simp_rw [row_phase, show ∀ j : ℕ, -(v + j * h) = -v + j * (-h) by intro j; ring]
  have he := candidate_fourier_row_power_sum_le _
    (candidate_measurable_eulerBandRowAmplitude Y ω T B u)
    (candidate_integrable_eulerBandRowAmplitude Y ω H u hT hTB E) measurable_snd (-v) (-h) n k
  simpa only [candidateRowPowerAmplitude, norm_mul, Complex.norm_conj, norm_prod,
    candidate_eulerBandRowAmplitude_norm] using he

/-- High row powers of the actual real Gaussian Gram matrix satisfy the
literal Fourier bound, with the exact `(2π)^(-4k)` normalization. -/
theorem candidate_eulerBandWhiteKernel_row_power_sum_le (Y : ℕ) (ω : Omega)
    (H u v h : ℝ) {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (n k : ℕ) :
    (∑ j ∈ range n, |∫ r, candidateEulerBandWhiteKernel Y ω H T B u r *
      candidateEulerBandWhiteKernel Y ω H T B (v + j * h) r| ^ (2 * k)) ≤
    (2 * Real.pi)⁻¹ ^ (4 * k) *
      ∫ z, ((∏ i, candidateEulerBandRowWeight Y ω T B (z.1 i)) *
        ∏ i, candidateEulerBandRowWeight Y ω T B (z.2 i)) *
        ‖candidateRowFourierSum n (-h) (candidateRowPowerFrequency Prod.snd z)‖
        ∂candidateRowPowerMeasure
          ((volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H))) k := by
  have hc : 0 ≤ (2 * Real.pi)⁻¹ ^ (4 * k) := by positivity
  have he := mul_le_mul_of_nonneg_left
    (candidate_eulerBand_restricted_row_power_sum_le Y ω H u v h hT hTB univ n k) hc
  simp only [Measure.restrict_univ] at he
  refine le_trans ?_ he
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hg := congrArg norm (candidate_eulerBandWhiteKernel_covariance_eq
    Y ω H B u (v + j * h) hT)
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_pow, norm_inv] at hg
  norm_num [abs_of_pos Real.pi_pos] at hg
  rw [hg, mul_pow, ← pow_mul, show 2 * (2 * k) = 4 * k by omega]
  norm_num [mul_inv_rev]

end
end Erdos.Problem1144
