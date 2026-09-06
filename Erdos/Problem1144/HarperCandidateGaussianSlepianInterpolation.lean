import Erdos.Problem1144.HarperCandidateGaussianSlepianColumns
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

namespace Erdos.Problem1144

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The Gaussian interpolation uses sine and cosine to have bounded velocity
on the entire closed parameter interval, including its endpoints. -/
def candidateGaussianSlepianPath {n : ℕ} (a b : Fin n → E) (t : ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : E :=
  Real.sin t • candidateGaussianColumns a z.1 + Real.cos t • candidateGaussianColumns b z.2

/-- The velocity of the Gaussian interpolation. -/
def candidateGaussianSlepianVelocity {n : ℕ} (a b : Fin n → E) (t : ℝ)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : E :=
  Real.cos t • candidateGaussianColumns a z.1 - Real.sin t • candidateGaussianColumns b z.2

@[fun_prop]
theorem candidate_continuous_gaussianSlepianPath {n : ℕ} (a b : Fin n → E) :
    Continuous (fun q : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      candidateGaussianSlepianPath a b q.1 q.2) := by
  unfold candidateGaussianSlepianPath
  fun_prop

/-- Pointwise differentiation of the full interpolation, including both endpoints. -/
theorem candidate_hasDerivAt_gaussianSlepianPath {n : ℕ}
    (a b : Fin n → E) (t : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    HasDerivAt (fun s => candidateGaussianSlepianPath a b s z)
      (candidateGaussianSlepianVelocity a b t z) t := by
  convert ((Real.hasDerivAt_sin t).smul_const (candidateGaussianColumns a z.1)).add
    ((Real.hasDerivAt_cos t).smul_const (candidateGaussianColumns b z.2)) using 1
  simp [candidateGaussianSlepianVelocity, sub_eq_add_neg]

/-- Gaussian finite linear combinations have integrable norm. -/
theorem candidate_integrable_gaussianColumns_norm {n : ℕ} (a : Fin n → E) :
    Integrable (fun x => ‖candidateGaussianColumns a x‖) (candidatePiGaussian n) := by
  have h : Integrable (candidateGaussianColumns a) (candidatePiGaussian n) :=
    integrable_finset_sum _ fun i _ => (candidate_integrable_gaussian_coordinate i).smul_const (a i)
  exact h.norm

/-- A uniform integrable majorant for the interpolation velocity. -/
theorem candidate_gaussianSlepianVelocity_norm_le {n : ℕ} (a b : Fin n → E)
    (t : ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    ‖candidateGaussianSlepianVelocity a b t z‖ ≤
      ‖candidateGaussianColumns a z.1‖ + ‖candidateGaussianColumns b z.2‖ := by
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_smul, Real.norm_eq_abs]
  exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one t))
    (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one t))

/-- Differentiation under the actual Gaussian product integral. Boundedness of
the test and its first derivative supplies every domination hypothesis. -/
theorem candidate_hasDerivAt_gaussianSlepianExpectation {n : ℕ}
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {C₀ C₁ : ℝ}
    (hC₀ : ∀ x, ‖f x‖ ≤ C₀) (hC₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (a b : Fin n → E) (t : ℝ) :
    HasDerivAt
      (fun s => ∫ z, f (candidateGaussianSlepianPath a b s z)
        ∂((candidatePiGaussian n).prod (candidatePiGaussian n)))
      (∫ z, fderiv ℝ f (candidateGaussianSlepianPath a b t z)
        (candidateGaussianSlepianVelocity a b t z)
        ∂((candidatePiGaussian n).prod (candidatePiGaussian n))) t := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0)
  let μ := (candidatePiGaussian n).prod (candidatePiGaussian n)
  let F := fun s z => f (candidateGaussianSlepianPath a b s z)
  let D := fun s z => fderiv ℝ f (candidateGaussianSlepianPath a b s z)
    (candidateGaussianSlepianVelocity a b s z)
  let bound := fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
    C₁ * (‖candidateGaussianColumns a z.1‖ + ‖candidateGaussianColumns b z.2‖)
  have hF (s : ℝ) : Continuous (F s) := by
    dsimp [F, candidateGaussianSlepianPath]; fun_prop
  have hD (s : ℝ) : Continuous (D s) := by
    dsimp [D, candidateGaussianSlepianPath, candidateGaussianSlepianVelocity]; fun_prop
  have hb : Integrable bound μ := by
    exact (((candidate_integrable_gaussianColumns_norm a).comp_fst _).add
      ((candidate_integrable_gaussianColumns_norm b).comp_snd _)).const_mul C₁
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (bound := bound) (x₀ := t)
    (by simp) (Filter.Eventually.of_forall (fun s => (hF s).aestronglyMeasurable))
    (Integrable.of_bound (hF t).aestronglyMeasurable C₀ (ae_of_all _ fun z => hC₀ _))
    (hD t).aestronglyMeasurable ?_ hb ?_).2
  · filter_upwards [] with z s _
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul_of_nonneg_right (hC₁ _) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (candidate_gaussianSlepianVelocity_norm_le a b s z) hC₁0))
  · filter_upwards [] with z s _
    exact ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s
      (candidate_hasDerivAt_gaussianSlepianPath a b s z))

/-! The two coordinate IBP identities now give the exact covariance derivative. -/

/-- Gaussian interpolation turns the derivative expectation into the
difference of the two Hessian column traces. This is an identity of the
actual product Gaussian integrals, with no comparison premise. -/
theorem candidate_gaussianSlepian_derivative_eq_hessian {n : ℕ}
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {C₁ C₂ : ℝ}
    (hC₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (hC₂ : ∀ x, ‖candidateGaussianHessian f x‖ ≤ C₂)
    (a b : Fin (n + 1) → E) (t : ℝ) :
    (∫ z, fderiv ℝ f (candidateGaussianSlepianPath a b t z)
      (candidateGaussianSlepianVelocity a b t z)
      ∂((candidatePiGaussian (n + 1)).prod (candidatePiGaussian (n + 1)))) =
    Real.sin t * Real.cos t * ∫ z,
      ((∑ i, candidateGaussianHessian f (candidateGaussianSlepianPath a b t z) (a i) (a i)) -
        ∑ i, candidateGaussianHessian f (candidateGaussianSlepianPath a b t z) (b i) (b i))
      ∂((candidatePiGaussian (n + 1)).prod (candidatePiGaussian (n + 1))) := by
  let μ := (candidatePiGaussian (n + 1)).prod (candidatePiGaussian (n + 1))
  let P := candidateGaussianSlepianPath a b t
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hdd : Continuous (candidateGaussianHessian f) :=
    (show ContDiff ℝ 0 (candidateGaussianHessian f) from hd.fderiv_right (by norm_num)).continuous
  have hP : Continuous P := by dsimp [P, candidateGaussianSlepianPath]; fun_prop
  have hF (v : E) : Continuous (fun z => fderiv ℝ f (P z) v) := by fun_prop
  have hFB (v : E) : ∀ z, ‖fderiv ℝ f (P z) v‖ ≤ C₁ * ‖v‖ := fun z =>
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hC₁ _) (norm_nonneg _))
  have hH (v : E) : Integrable (fun z => candidateGaussianHessian f (P z) v v) μ := by
    have hc : Continuous (fun z => candidateGaussianHessian f (P z) v v) := by fun_prop
    exact Integrable.of_bound hc.aestronglyMeasurable (C₂ * ‖v‖ * ‖v‖)
      (ae_of_all _ fun z => candidate_gaussianHessian_norm_le hC₂ _ _ _)
  have hL (i : Fin (n + 1)) : Integrable (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
      z.1 i * fderiv ℝ f (P z) (a i)) μ :=
    ((candidate_integrable_gaussian_coordinate i).comp_fst _).mul_bdd
      (hF _).aestronglyMeasurable (ae_of_all _ (hFB _))
  have hR (i : Fin (n + 1)) : Integrable (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
      z.2 i * fderiv ℝ f (P z) (b i)) μ :=
    ((candidate_integrable_gaussian_coordinate i).comp_snd _).mul_bdd
      (hF _).aestronglyMeasurable (ae_of_all _ (hFB _))
  have hiL (i : Fin (n + 1)) :
      (∫ z, z.1 i * fderiv ℝ f (P z) (a i) ∂μ) =
        Real.sin t * ∫ z, candidateGaussianHessian f (P z) (a i) (a i) ∂μ := by
    simpa [P, μ, candidateGaussianSlepianPath, add_comm] using
      candidate_gaussianColumns_integration_by_parts hf hC₁ hC₂ a b (Real.sin t) (Real.cos t) i
  have hiR (i : Fin (n + 1)) :
      (∫ z, z.2 i * fderiv ℝ f (P z) (b i) ∂μ) =
        Real.cos t * ∫ z, candidateGaussianHessian f (P z) (b i) (b i) ∂μ := by
    have h := candidate_gaussianColumns_integration_by_parts hf hC₁ hC₂ b a
      (Real.cos t) (Real.sin t) i
    rw [← integral_prod_swap (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => z.1 i * fderiv ℝ f
      (Real.sin t • candidateGaussianColumns a z.2 + Real.cos t • candidateGaussianColumns b z.1)
      (b i)), ← integral_prod_swap (fun z => candidateGaussianHessian f
      (Real.sin t • candidateGaussianColumns a z.2 + Real.cos t • candidateGaussianColumns b z.1)
      (b i) (b i))] at h
    exact h
  have he (z) : fderiv ℝ f (P z) (candidateGaussianSlepianVelocity a b t z) =
      Real.cos t * (∑ i, z.1 i * fderiv ℝ f (P z) (a i)) -
        Real.sin t * (∑ i, z.2 i * fderiv ℝ f (P z) (b i)) := by
    simp [candidateGaussianSlepianVelocity, candidateGaussianColumns, map_sub, map_smul, map_sum]
  change (∫ z, fderiv ℝ f (P z) (candidateGaussianSlepianVelocity a b t z) ∂μ) = _
  simp_rw [he]
  rw [integral_sub ((integrable_finset_sum _ fun i _ => hL i).const_mul _)
    ((integrable_finset_sum _ fun i _ => hR i).const_mul _), integral_const_mul, integral_const_mul,
    integral_finset_sum _ (fun i _ => hL i), integral_finset_sum _ (fun i _ => hR i)]
  simp_rw [hiL, hiR]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [← integral_finset_sum _ (fun i _ => hH (a i)),
    ← integral_finset_sum _ (fun i _ => hH (b i))]
  rw [integral_sub (integrable_finset_sum _ fun i _ => hH (a i))
    (integrable_finset_sum _ fun i _ => hH (b i))]
  ring

/-- Smooth Gaussian comparison under the pointwise Hessian-trace order.
This proves the expectation inequality by interpolation; that inequality is
not among the assumptions. -/
theorem candidate_gaussianSlepian_smoothComparison {n : ℕ}
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {C₀ C₁ C₂ : ℝ}
    (hC₀ : ∀ x, ‖f x‖ ≤ C₀) (hC₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (hC₂ : ∀ x, ‖candidateGaussianHessian f x‖ ≤ C₂)
    (a b : Fin (n + 1) → E)
    (horder : ∀ x, (∑ i, candidateGaussianHessian f x (a i) (a i)) ≤
      ∑ i, candidateGaussianHessian f x (b i) (b i)) :
    (∫ x, f (candidateGaussianColumns a x) ∂candidatePiGaussian (n + 1)) ≤
      ∫ x, f (candidateGaussianColumns b x) ∂candidatePiGaussian (n + 1) := by
  let μ := (candidatePiGaussian (n + 1)).prod (candidatePiGaussian (n + 1))
  let F := fun t => ∫ z, f (candidateGaussianSlepianPath a b t z) ∂μ
  have hF (t : ℝ) := candidate_hasDerivAt_gaussianSlepianExpectation hf hC₀ hC₁ a b t
  have hdiff : Differentiable ℝ F := fun t => (hF t).differentiableAt
  have hanti : AntitoneOn F (Icc 0 (Real.pi / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      hdiff.continuous.continuousOn
      (fun t _ => (hF t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hF t).deriv, candidate_gaussianSlepian_derivative_eq_hessian hf hC₁ hC₂ a b t]
    have ht' : t ∈ Icc 0 (Real.pi / 2) := interior_subset ht
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact mul_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi ht'.1 (by linarith [ht'.2, Real.pi_pos]))
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht'.1, Real.pi_pos], ht'.2⟩)
    · exact integral_nonpos fun z => sub_nonpos.mpr (horder _)
  have h := hanti (show 0 ∈ Icc 0 (Real.pi / 2) by constructor <;> linarith [Real.pi_pos])
    (show Real.pi / 2 ∈ Icc 0 (Real.pi / 2) by constructor <;> linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])
  simp only [F, μ, candidateGaussianSlepianPath, Real.sin_pi_div_two, Real.cos_pi_div_two,
    Real.sin_zero, Real.cos_zero, one_smul, zero_smul, add_zero, zero_add] at h
  rw [integral_fun_fst (fun x => f (candidateGaussianColumns a x)),
    integral_fun_snd (fun x => f (candidateGaussianColumns b x))] at h
  simpa using h

end

end Erdos.Problem1144
