import Erdos.Problem1144.HarperCandidateGaussianSlepianFinite
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace Erdos.Problem1144

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite Gaussian linear combination, in an arbitrary real normed space. -/
def candidateGaussianColumns {n : ℕ} (a : Fin n → E) (x : Fin n → ℝ) : E :=
  ∑ i, x i • a i

@[fun_prop]
theorem candidate_continuous_gaussianColumns {n : ℕ} (a : Fin n → E) :
    Continuous (candidateGaussianColumns a) := by
  unfold candidateGaussianColumns
  fun_prop

/-- The exact derivative of a split Gaussian coordinate. -/
theorem candidate_hasDerivAt_splitCoordinate {n : ℕ} (i j : Fin (n + 1))
    (t : ℝ) (y : Fin n → ℝ) : HasDerivAt
    (fun s => (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
      (s, y) j) (if j = i then 1 else 0) t := by
  classical
  by_cases h : j = i
  · subst j
    simpa using hasDerivAt_id t
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h
    subst j
    simpa [MeasurableEquiv.piFinSuccAbove_symm_apply] using hasDerivAt_const t (y k)

/-- Varying one coefficient differentiates the linear combination in its
corresponding column. -/
theorem candidate_hasDerivAt_gaussianColumns_split {n : ℕ}
    (a : Fin (n + 1) → E) (i : Fin (n + 1)) (t : ℝ) (y : Fin n → ℝ) :
    HasDerivAt (fun s => candidateGaussianColumns a
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm (s, y)))
      (a i) t := by
  classical
  have h := HasDerivAt.sum (u := Finset.univ)
    (fun j _ => (candidate_hasDerivAt_splitCoordinate i j t y).smul_const (a j))
  convert h using 1
  · ext s; simp [candidateGaussianColumns]
  · simp

/-- The second derivative in its iterated continuous-linear-map form. -/
abbrev candidateGaussianHessian (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) x

/-- Uniform operator bounds imply the required directional Hessian bound. -/
theorem candidate_gaussianHessian_norm_le {f : E → ℝ} {C : ℝ}
    (hC : ∀ x, ‖candidateGaussianHessian f x‖ ≤ C) (x v w : E) :
    ‖candidateGaussianHessian f x v w‖ ≤ C * ‖v‖ * ‖w‖ := by
  calc
    _ ≤ ‖candidateGaussianHessian f x v‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖candidateGaussianHessian f x‖ * ‖v‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ C * ‖v‖ * ‖w‖ := by gcongr; exact hC x

/-- Coordinate chain rule for a directional derivative along a Gaussian
linear combination. -/
theorem candidate_gaussianColumns_directional_deriv {n : ℕ}
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (a : Fin (n + 1) → E)
    (h : E) (c : ℝ) (i : Fin (n + 1)) : CandidateHasCoordinateDeriv i
    (fun x => fderiv ℝ f (h + c • candidateGaussianColumns a x) (a i))
    (fun x => c * candidateGaussianHessian f
      (h + c • candidateGaussianColumns a x) (a i) (a i)) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  intro t y
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let x := h + c • candidateGaussianColumns a (e.symm (t, y))
  have hx : HasDerivAt (fun s => h + c • candidateGaussianColumns a (e.symm (s, y)))
      (c • a i) t := by
    convert (hasDerivAt_const t h).add
      ((candidate_hasDerivAt_gaussianColumns_split a i t y).const_smul c) using 1
    simp only [zero_add]
  have hD := (hd.differentiable (by norm_num) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const (a i) x)
  have hh := hD.comp_hasDerivAt t hx
  simpa [x, ContinuousLinearMap.flip_apply, map_smul] using hh

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Actual Gaussian integration by parts along an arbitrary column, with all
product integrability proved from bounded first and second derivatives. -/
theorem candidate_gaussianColumns_integration_by_parts {n m : ℕ}
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {C₁ C₂ : ℝ}
    (hC₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (hC₂ : ∀ x, ‖candidateGaussianHessian f x‖ ≤ C₂)
    (a : Fin (n + 1) → E) (b : Fin m → E) (c d : ℝ) (i : Fin (n + 1)) :
    (∫ z, z.1 i * fderiv ℝ f
        (d • candidateGaussianColumns b z.2 + c • candidateGaussianColumns a z.1) (a i)
      ∂((candidatePiGaussian (n + 1)).prod (candidatePiGaussian m))) =
    c * ∫ z, candidateGaussianHessian f
        (d • candidateGaussianColumns b z.2 + c • candidateGaussianColumns a z.1) (a i) (a i)
      ∂((candidatePiGaussian (n + 1)).prod (candidatePiGaussian m)) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hdd : Continuous (candidateGaussianHessian f) :=
    (show ContDiff ℝ 0 (candidateGaussianHessian f) from hd.fderiv_right (by norm_num)).continuous
  let F := fun z : (Fin (n + 1) → ℝ) × (Fin m → ℝ) =>
    fderiv ℝ f (d • candidateGaussianColumns b z.2 + c • candidateGaussianColumns a z.1) (a i)
  let D := fun z : (Fin (n + 1) → ℝ) × (Fin m → ℝ) =>
    c * candidateGaussianHessian f
      (d • candidateGaussianColumns b z.2 + c • candidateGaussianColumns a z.1) (a i) (a i)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hFB : ∀ z, ‖F z‖ ≤ C₁ * ‖a i‖ := by
    intro z
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hC₁ _) (norm_nonneg _))
  have hDB : ∀ z, ‖D z‖ ≤ |c| * (C₂ * ‖a i‖ * ‖a i‖) := by
    intro z
    dsimp [D]
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (candidate_gaussianHessian_norm_le hC₂ _ _ _) (abs_nonneg _)
  have hi : Integrable (fun z : (Fin (n + 1) → ℝ) × (Fin m → ℝ) => z.1 i)
      ((candidatePiGaussian (n + 1)).prod (candidatePiGaussian m)) :=
    (candidate_integrable_gaussian_coordinate i).comp_fst _
  have h := candidate_piGaussian_prod_integration_by_parts i
    (fun y => candidate_gaussianColumns_directional_deriv hf a
      (d • candidateGaussianColumns b y) c i)
    hF.measurable hD.measurable
    (fun x y => hFB (x, y)) (fun x y => hDB (x, y))
    (hi.mul_bdd hF.aestronglyMeasurable (ae_of_all _ hFB))
    (Integrable.of_bound hD.aestronglyMeasurable _ (ae_of_all _ hDB))
  simpa [F, D, integral_const_mul] using h

end

end Erdos.Problem1144
