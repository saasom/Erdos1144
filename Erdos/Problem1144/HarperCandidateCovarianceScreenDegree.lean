import Erdos.Problem1144.HarperCandidateCovarianceNormalizedDegree
import Erdos.Problem1144.HarperCandidateCovarianceScreenGram

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144

/-- The actual screened real white covariance is the normalized real part
of the literal raw Fourier covariance. -/
theorem candidate_screenWhiteKernel_covariance_eq_normalized_raw
    (Y : ℕ) (ω : Problem520.Omega) {S : Set ℝ} (hS : MeasurableSet S)
    (hSym : ∀ t, t ∈ S ↔ -t ∈ S) (M : ℝ) (hsub : S ⊆ Icc (-M) M)
    (B u v : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ r, candidateEulerScreenWhiteKernel Y ω S T B u r *
      candidateEulerScreenWhiteKernel Y ω S T B v r) =
      (2 * Real.pi)⁻¹ ^ 2 * (candidateEulerBandRawCovariance Y ω T B u v S).re := by
  have h := candidate_eulerScreenWhiteKernel_covariance_eq Y ω hS hSym M hsub B u v hT
  change ((_ : ℝ) : ℂ) =
    (2 * Real.pi : ℂ)⁻¹ ^ 2 * candidateEulerBandRawCovariance Y ω T B u v S at h
  have hc : (2 * Real.pi : ℂ)⁻¹ ^ 2 = (((2 * Real.pi)⁻¹ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] using hr

/-- The one common near/far event controls the actual screened white Gram
bad degree, including its exact Fourier normalization. The result holds
simultaneously for all measurable symmetric retained sets and all rows. -/
theorem candidate_screenWhiteKernel_bad_degree_le_of_control
    (start stop a : ℕ) (W h M d : ℝ) {T B θ b : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (hθ : 0 < θ) (N k : ℕ)
    {ω : Problem520.Omega}
    (hω : ω ∈ candidateCovarianceDegreeControlEvent start stop a W h M T B d k N
      ((2 * Real.pi) ^ 2 * θ) b)
    (u v : ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (hSym : ∀ t, t ∈ S ↔ -t ∈ S)
    (hret : S ⊆ candidateCovarianceScreenedHeightSet
      start (stop - start) W M (Finset.Icc (a - start) (stop - start)) ω)
    (hann : ∀ t ∈ S, h ≤ |t|) :
    (((range N).filter fun j : ℕ => θ ≤ |∫ r,
      candidateEulerScreenWhiteKernel (Problem520.harperBlockEndpoint stop) ω S T B u r *
        candidateEulerScreenWhiteKernel (Problem520.harperBlockEndpoint stop) ω S T B
          (v + j * (2 * Real.pi)) r|).card : ℝ) ≤ b := by
  have hsub : S ⊆ Icc (-M) M := fun t ht => abs_le.mp (hret ht).1
  simp_rw [candidate_screenWhiteKernel_covariance_eq_normalized_raw
    (Problem520.harperBlockEndpoint stop) ω hS hSym M hsub B u _ hT]
  exact candidate_normalized_rawCovariance_bad_degree_le_of_control start stop a W h M d
    hT hTB hθ N k hω u v hS hret hann

end Erdos.Problem1144
