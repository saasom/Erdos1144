import Erdos.Problem1144.HarperCandidateCovarianceDegreeControl

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144

/-- The literal `(2π)⁻²` normalization is retained when passing from the raw
complex covariance to its real covariance. The same common event controls
all rows, with the raw threshold exactly `(2π)² θ`. -/
theorem candidate_normalized_rawCovariance_bad_degree_le_of_control
    (start stop a : ℕ) (W h M d : ℝ) {T B θ b : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (hθ : 0 < θ) (N k : ℕ)
    {ω : Problem520.Omega}
    (hω : ω ∈ candidateCovarianceDegreeControlEvent start stop a W h M T B d k N
      ((2 * Real.pi) ^ 2 * θ) b)
    (u v : ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (hret : S ⊆ candidateCovarianceScreenedHeightSet
      start (stop - start) W M (Finset.Icc (a - start) (stop - start)) ω)
    (hann : ∀ t ∈ S, h ≤ |t|) :
    (((range N).filter fun j : ℕ => θ ≤ |(2 * Real.pi)⁻¹ ^ 2 *
      (candidateEulerBandRawCovariance (Problem520.harperBlockEndpoint stop) ω
        T B u (v + j * (2 * Real.pi)) S).re|).card : ℝ) ≤ b := by
  classical
  have hs : 0 < (2 * Real.pi) ^ 2 := by positivity
  have hb := candidate_rawCovariance_bad_degree_le_of_control start stop a W h M d
    hT hTB (by positivity : 0 < (2 * Real.pi) ^ 2 * θ) N k hω u v hS hret hann
  apply le_trans _ hb
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro j hj
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, ?_⟩
  have hp := (Finset.mem_filter.mp hj).2
  let z := candidateEulerBandRawCovariance (Problem520.harperBlockEndpoint stop) ω
    T B u (v + j * (2 * Real.pi)) S
  have hc : |(2 * Real.pi)⁻¹ ^ 2 * z.re| ≤ ‖z‖ / (2 * Real.pi) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹ ^ 2)]
    have h := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z)
      (by positivity : 0 ≤ (2 * Real.pi)⁻¹ ^ 2)
    simpa only [inv_pow, div_eq_mul_inv, mul_comm] using h
  have ht := (le_div_iff₀ hs).mp (hp.trans hc)
  simpa only [z, mul_comm] using ht

end Erdos.Problem1144
