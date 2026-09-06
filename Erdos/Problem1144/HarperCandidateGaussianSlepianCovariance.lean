import Erdos.Problem1144.HarperCandidateGaussianSlepianInterpolation
import Mathlib.Algebra.BigOperators.Pi

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos.Problem1144

noncomputable section

/-- A bilinear form on a finite real coordinate space expands in the
standard coordinate basis. -/
theorem candidate_bilinear_coordinate_expansion {m : ℕ}
    (H : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] ℝ) (v w : Fin m → ℝ) :
    H v w = ∑ i, ∑ j, v i * w j * H (Pi.single i 1) (Pi.single j 1) := by
  classical
  conv_lhs => rw [pi_eq_sum_univ' v, pi_eq_sum_univ' w]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Hessian column trace is its contraction with the actual covariance
Gram matrix of the linear Gaussian vector. -/
theorem candidate_hessian_trace_eq_covariance {n m : ℕ}
    (H : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] ℝ)
    (a : Fin n → Fin m → ℝ) :
    (∑ p, H (a p) (a p)) = ∑ i, ∑ j,
      (∑ p, a p i * a p j) * H (Pi.single i 1) (Pi.single j 1) := by
  calc
    (∑ p, H (a p) (a p)) = ∑ p, ∑ i, ∑ j,
        a p i * a p j * H (Pi.single i 1) (Pi.single j 1) :=
      Finset.sum_congr rfl fun p _ => candidate_bilinear_coordinate_expansion H _ _
    _ = _ := ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]

/-- The ordinary smooth Slepian inequality: equal diagonal covariances and
ordered off-diagonal covariances compare tests whose mixed Hessian entries
are nonnegative. Both sides use actual finite product Gaussian laws. -/
theorem candidate_gaussianSlepian_covariance_smooth {n m : ℕ}
    {f : (Fin m → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {C₀ C₁ C₂ : ℝ}
    (hC₀ : ∀ x, ‖f x‖ ≤ C₀) (hC₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (hC₂ : ∀ x, ‖candidateGaussianHessian f x‖ ≤ C₂)
    (a b : Fin (n + 1) → Fin m → ℝ)
    (hdiag : ∀ i, (∑ p, a p i * a p i) = ∑ p, b p i * b p i)
    (hcov : ∀ i j, i ≠ j → (∑ p, a p i * a p j) ≤ ∑ p, b p i * b p j)
    (hmixed : ∀ x i j, i ≠ j →
      0 ≤ candidateGaussianHessian f x (Pi.single i 1) (Pi.single j 1)) :
    (∫ z, f (candidateGaussianColumns a z) ∂candidatePiGaussian (n + 1)) ≤
      ∫ z, f (candidateGaussianColumns b z) ∂candidatePiGaussian (n + 1) := by
  apply candidate_gaussianSlepian_smoothComparison hf hC₀ hC₁ hC₂ a b
  intro x
  rw [candidate_hessian_trace_eq_covariance, candidate_hessian_trace_eq_covariance]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases h : i = j
  · subst j
    rw [hdiag]
  · exact mul_le_mul_of_nonneg_right (hcov i j h) (hmixed x i j h)

end

end Erdos.Problem1144
