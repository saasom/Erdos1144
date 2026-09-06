import Erdos.Problem1144.HarperTrackBFiniteBlock

open MeasureTheory
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# The stationary candidate's squarefree approximation error

The square-kernel convolution and its floor-square-root coefficient estimate
are already proved in `HarperTrackBFiniteBlock`. This file exports their
unconditional, single-endpoint consequences without a grid certificate.
The cutoff is `N + 1`, as in `normSum` and `squarefreeCriticalSum`.
-/

/-- The complete normalized sum has its exact squarefree-kernel expansion. -/
theorem normSum_eq_canonicalWeightedSum (omega : Omega) (N : ℕ) :
    normSum omega N =
      squarefreeWeightedSum (trackBGridErrorCanonicalSupport N)
        (trackBCompleteCanonicalWeight N) omega := by
  apply normSum_eq_canonicalWeightedSum_of_S_eq_unnormalized
  exact S_eq_canonicalUnnormalized_of_squareSmoothing omega (N + 1)

/-- The complete-to-squarefree error is the finite sum with the literal
floor-square-root discrepancy as coefficient. -/
theorem trackBError_eq_canonicalWeightedSum (omega : Omega) (N : ℕ) :
    trackBError omega N =
      squarefreeWeightedSum (trackBGridErrorCanonicalSupport N)
        (trackBGridErrorCanonicalWeight N) omega :=
  trackBError_eq_canonicalWeightedSum_of_normSum_eq omega N
    (normSum_eq_canonicalWeightedSum omega N)

/-- The squared squarefree approximation error is integrable at every cutoff. -/
theorem integrable_trackBError_sq (N : ℕ) :
    Integrable (fun omega : Omega ↦ trackBError omega N ^ 2) mu := by
  simp_rw [trackBError_eq_canonicalWeightedSum]
  exact integrable_squarefreeWeightedSum_sq _ _

/-- Orthogonality gives the exact deterministic diagonal second moment. -/
theorem integral_trackBError_sq_eq (N : ℕ) :
    (∫ omega, trackBError omega N ^ 2 ∂mu) =
      ∑ d ∈ trackBGridErrorCanonicalSupport N,
        trackBGridErrorCanonicalWeight N d ^ 2 := by
  simp_rw [trackBError_eq_canonicalWeightedSum]
  exact integral_squarefreeWeightedSum_sq_eq_diag _ _
    (fun _ hd ↦ trackBGridErrorCanonicalSupport_pos hd)
    (fun _ hd ↦ trackBGridErrorCanonicalSupport_squarefree hd)

/-- The stationary candidate's complete-to-squarefree approximation has
second moment at most one, uniformly over every natural cutoff. -/
theorem integral_trackBError_sq_le_one (N : ℕ) :
    (∫ omega, trackBError omega N ^ 2 ∂mu) ≤ 1 := by
  rw [integral_trackBError_sq_eq]
  have hN : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
  calc
    _ ≤ ∑ _d ∈ trackBGridErrorCanonicalSupport N,
        (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      have h := trackBGridErrorCanonicalWeight_abs_le
        (N := N) (trackBGridErrorCanonicalSupport_pos hd)
      exact sq_le_sq.mpr (by simpa only [abs_of_nonneg (by positivity :
        0 ≤ (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹)] using h)
    _ = (trackBGridErrorCanonicalSupport N).card *
        (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ ^ 2 := by simp
    _ ≤ ((N + 1 : ℕ) : ℝ) * (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right (trackBGridErrorCanonicalSupport_card_le N) (sq_nonneg _)
    _ = 1 := by rw [inv_pow, Real.sq_sqrt hN.le, mul_inv_cancel₀ hN.ne']

end Erdos.Problem1144
