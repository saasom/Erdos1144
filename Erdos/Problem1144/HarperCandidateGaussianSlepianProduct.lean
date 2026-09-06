import Erdos.Problem1144.HarperCandidateGaussianSlepianCovariance
import Mathlib.Analysis.Calculus.FDeriv.Mul

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos.Problem1144

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact second-derivative product rule in operator form. -/
theorem candidate_gaussianHessian_mul {f g : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    candidateGaussianHessian (fun y => f y * g y) x =
      (f x • candidateGaussianHessian g x + (fderiv ℝ f x).smulRight (fderiv ℝ g x)) +
      (g x • candidateGaussianHessian f x + (fderiv ℝ g x).smulRight (fderiv ℝ f x)) := by
  have hdF : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hdG : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have he : fderiv ℝ (fun y => f y * g y) =
      fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y := by
    funext y
    exact fderiv_fun_mul (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y)
  unfold candidateGaussianHessian
  rw [he]
  exact (((hf.differentiable (by norm_num) x).hasFDerivAt.smul
    (hdG.differentiable (by norm_num) x).hasFDerivAt).add
    ((hg.differentiable (by norm_num) x).hasFDerivAt.smul
      (hdF.differentiable (by norm_num) x).hasFDerivAt)).fderiv

/-- Products preserve uniform bounds through two derivatives. A single
common constant is sufficient for the qualitative Slepian smoothing limit. -/
theorem candidate_bounded_gaussian_derivatives_mul {f g : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ x, ‖f x‖ ≤ A ∧ ‖fderiv ℝ f x‖ ≤ A ∧ ‖candidateGaussianHessian f x‖ ≤ A)
    (hb : ∀ x, ‖g x‖ ≤ B ∧ ‖fderiv ℝ g x‖ ≤ B ∧ ‖candidateGaussianHessian g x‖ ≤ B) :
    ∀ x, ‖f x * g x‖ ≤ 4 * A * B ∧
      ‖fderiv ℝ (fun y => f y * g y) x‖ ≤ 4 * A * B ∧
      ‖candidateGaussianHessian (fun y => f y * g y) x‖ ≤ 4 * A * B := by
  intro x
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul]
    have h := mul_le_mul (ha x).1 (hb x).1 (norm_nonneg _) hA
    nlinarith
  · rw [fderiv_fun_mul (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x)]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_smul]
    have h1 := mul_le_mul (ha x).1 (hb x).2.1 (norm_nonneg _) hA
    have h2 := mul_le_mul (hb x).1 (ha x).2.1 (norm_nonneg _) hB
    nlinarith
  · rw [candidate_gaussianHessian_mul hf hg]
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans ?_)
    simp only [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
    have h1 := mul_le_mul (ha x).1 (hb x).2.2 (norm_nonneg _) hA
    have h2 := mul_le_mul (ha x).2.1 (hb x).2.1 (norm_nonneg _) hA
    have h3 := mul_le_mul (hb x).1 (ha x).2.2 (norm_nonneg _) hB
    have h4 := mul_le_mul (hb x).2.1 (ha x).2.1 (norm_nonneg _) hB
    nlinarith

/-- The signs needed for Slepian are stable under multiplication of
nonnegative coordinate-decreasing tests. -/
theorem candidate_gaussian_slepian_product_signs {m : ℕ}
    {f g : (Fin m → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf1 : ∀ x i, fderiv ℝ f x (Pi.single i 1) ≤ 0)
    (hg1 : ∀ x i, fderiv ℝ g x (Pi.single i 1) ≤ 0)
    (hf2 : ∀ x i j, i ≠ j → 0 ≤ candidateGaussianHessian f x (Pi.single i 1) (Pi.single j 1))
    (hg2 : ∀ x i j, i ≠ j → 0 ≤ candidateGaussianHessian g x (Pi.single i 1) (Pi.single j 1)) :
    (∀ x i, fderiv ℝ (fun y => f y * g y) x (Pi.single i 1) ≤ 0) ∧
    (∀ x i j, i ≠ j → 0 ≤ candidateGaussianHessian (fun y => f y * g y) x
      (Pi.single i 1) (Pi.single j 1)) := by
  constructor
  · intro x i
    rw [fderiv_fun_mul (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x)]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (hf0 x) (hg1 x i))
      (mul_nonpos_of_nonneg_of_nonpos (hg0 x) (hf1 x i))
  · intro x i j hij
    rw [candidate_gaussianHessian_mul hf hg]
    exact add_nonneg
      (add_nonneg (mul_nonneg (hf0 x) (hg2 x i j hij))
        (mul_nonneg_of_nonpos_of_nonpos (hf1 x i) (hg1 x j)))
      (add_nonneg (mul_nonneg (hg0 x) (hf2 x i j hij))
        (mul_nonneg_of_nonpos_of_nonpos (hg1 x i) (hf1 x j)))

/-- First derivative of a scalar test applied to one coordinate. -/
theorem candidate_fderiv_coordinate_test {m : ℕ} {φ : ℝ → ℝ}
    (hφ : Differentiable ℝ φ) (i : Fin m) (x : Fin m → ℝ) :
    fderiv ℝ (fun y : Fin m → ℝ => φ (y i)) x =
      deriv φ (x i) • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) := by
  exact ((hφ _).hasDerivAt.comp_hasFDerivAt x
    (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).hasFDerivAt).fderiv

/-- Second derivative of a scalar coordinate test. -/
theorem candidate_gaussianHessian_coordinate_test {m : ℕ} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (i : Fin m) (x : Fin m → ℝ) :
    candidateGaussianHessian (fun y : Fin m → ℝ => φ (y i)) x =
      (deriv (deriv φ) (x i) •
        (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)).smulRight
          (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) := by
  have hd : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have he : fderiv ℝ (fun y : Fin m → ℝ => φ (y i)) =
      fun y => deriv φ (y i) • (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) :=
    funext (candidate_fderiv_coordinate_test (hφ.differentiable (by norm_num)) i)
  unfold candidateGaussianHessian
  rw [he]
  exact ((((hd.differentiable (by norm_num) _).hasDerivAt.comp_hasFDerivAt x
    (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).hasFDerivAt).smul_const
      (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ))).fderiv

/-- A scalar bounded decreasing smooth cutoff gives a bounded smooth
coordinate test with the required Hessian signs. -/
theorem candidate_gaussian_coordinate_test {m : ℕ} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (h0 : ∀ x, 0 ≤ φ x) (h1 : ∀ x, φ x ≤ 1)
    (hd : ∀ x, deriv φ x ≤ 0) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, ‖deriv φ x‖ ≤ B ∧ ‖deriv (deriv φ) x‖ ≤ B) (k : Fin m) :
    (∀ x i, fderiv ℝ (fun y : Fin m → ℝ => φ (y k)) x (Pi.single i 1) ≤ 0) ∧
    (∀ x i j, i ≠ j → 0 ≤ candidateGaussianHessian
      (fun y : Fin m → ℝ => φ (y k)) x (Pi.single i 1) (Pi.single j 1)) ∧
    (∀ x, ‖φ (x k)‖ ≤ 1 + B ∧
      ‖fderiv ℝ (fun y : Fin m → ℝ => φ (y k)) x‖ ≤ 1 + B ∧
      ‖candidateGaussianHessian (fun y : Fin m → ℝ => φ (y k)) x‖ ≤ 1 + B) := by
  classical
  let L : (Fin m → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one fun x => by
    simpa [L] using norm_le_pi_norm x k
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    rw [candidate_fderiv_coordinate_test (hφ.differentiable (by norm_num))]
    by_cases h : i = k
    · subst i; simpa using hd (x k)
    · simp [Pi.single_eq_of_ne (Ne.symm h)]
  · intro x i j hij
    rw [candidate_gaussianHessian_coordinate_test hφ]
    by_cases h : i = k
    · subst i; simp [Pi.single_eq_of_ne hij]
    · simp [Pi.single_eq_of_ne (Ne.symm h)]
  · intro x
    refine ⟨?_, ?_, ?_⟩
    · rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
      linarith [h1 (x k)]
    · rw [candidate_fderiv_coordinate_test (hφ.differentiable (by norm_num)), norm_smul]
      have h := mul_le_mul (hbound (x k)).1 hL (norm_nonneg _) hB
      change ‖deriv φ (x k)‖ * ‖L‖ ≤ _
      nlinarith
    · rw [candidate_gaussianHessian_coordinate_test hφ,
        ContinuousLinearMap.norm_smulRight_apply, norm_smul]
      have hl0 := norm_nonneg L
      have h := mul_le_mul (hbound (x k)).2 hL hl0 hB
      simp only [mul_one] at h
      have h' := mul_le_mul h hL hl0 hB
      change (‖deriv (deriv φ) (x k)‖ * ‖L‖) * ‖L‖ ≤ _
      nlinarith

/-- The actual finite product of scalar cutoffs has the mixed Hessian signs
and the global operator bounds required by smooth Slepian comparison. -/
theorem candidate_gaussian_product_test {m : ℕ} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (h0 : ∀ x, 0 ≤ φ x) (h1 : ∀ x, φ x ≤ 1)
    (hd : ∀ x, deriv φ x ≤ 0) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, ‖deriv φ x‖ ≤ B ∧ ‖deriv (deriv φ) x‖ ≤ B)
    (s : Finset (Fin m)) :
    (∀ x i, fderiv ℝ (fun y : Fin m → ℝ => ∏ k ∈ s, φ (y k)) x (Pi.single i 1) ≤ 0) ∧
    (∀ x i j, i ≠ j → 0 ≤ candidateGaussianHessian
      (fun y : Fin m → ℝ => ∏ k ∈ s, φ (y k)) x (Pi.single i 1) (Pi.single j 1)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖∏ k ∈ s, φ (x k)‖ ≤ C ∧
      ‖fderiv ℝ (fun y : Fin m → ℝ => ∏ k ∈ s, φ (y k)) x‖ ≤ C ∧
      ‖candidateGaussianHessian (fun y : Fin m → ℝ => ∏ k ∈ s, φ (y k)) x‖ ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨?_, ?_, 1, zero_le_one, ?_⟩ <;>
        simp [candidateGaussianHessian]
  | @insert k s hk ih =>
      rcases ih with ⟨ih1, ih2, C, hC, hbC⟩
      have hkcont : ContDiff ℝ 2 (fun y : Fin m → ℝ => φ (y k)) := by fun_prop
      have hscont : ContDiff ℝ 2 (fun y : Fin m → ℝ => ∏ j ∈ s, φ (y j)) := by fun_prop
      have hs0 (x : Fin m → ℝ) : 0 ≤ ∏ j ∈ s, φ (x j) :=
        Finset.prod_nonneg fun j _ => h0 _
      obtain ⟨hk1, hk2, hkb⟩ := candidate_gaussian_coordinate_test hφ h0 h1 hd hB hbound k
      obtain ⟨hh1, hh2⟩ := candidate_gaussian_slepian_product_signs hkcont hscont
        (fun x => h0 (x k)) hs0 hk1 ih1 hk2 ih2
      simp only [Finset.prod_insert hk]
      refine ⟨hh1, hh2, 4 * (1 + B) * C, mul_nonneg (by positivity) hC, ?_⟩
      exact candidate_bounded_gaussian_derivatives_mul hkcont hscont (by positivity) hC hkb hbC

end

end Erdos.Problem1144
