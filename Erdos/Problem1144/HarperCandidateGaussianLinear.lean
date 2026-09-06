import Erdos.Problem1144.HarperCandidateGaussianCoupling
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace

namespace Erdos.Problem1144

/-- The actual finite linear combination of independent Gaussian noises. -/
noncomputable def candidateGaussianLinear {ι P : Type*} [Fintype ι] [Fintype P]
    (c : Matrix ι P ℝ) : EuclideanSpace ℝ P →L[ℝ] EuclideanSpace ℝ ι where
  toFun x := toLp 2 (fun i => ∑ p, c i p * x p)
  map_add' x y := by ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by ext i; simp [Finset.mul_sum, mul_left_comm]
  cont := Continuous.comp' (by fun_prop) (continuous_pi (by dsimp; fun_prop))

@[simp] theorem candidateGaussianLinear_apply {ι P : Type*} [Fintype ι] [Fintype P]
    (c : Matrix ι P ℝ) (x : EuclideanSpace ℝ P) (i : ι) :
    candidateGaussianLinear c x i = ∑ p, c i p * x p := rfl

/-- Finite Gaussian linear combinations have their literal Gram covariance. -/
theorem candidate_gaussian_linear_covariance {ι P : Type*} [Fintype ι] [Fintype P]
    [DecidableEq P] (c : Matrix ι P ℝ) (i j : ι) :
    cov[fun x => ∑ p, c i p * x p, fun x => ∑ p, c j p * x p;
      multivariateGaussian (0 : EuclideanSpace ℝ P) 1] = ∑ p, c i p * c j p := by
  have hi (p : P) := (candidate_gaussian_eval_memLp_two (Matrix.PosSemidef.one :
    (1 : Matrix P P ℝ).PosSemidef) p).const_mul (c i p)
  have hj (p : P) := (candidate_gaussian_eval_memLp_two (Matrix.PosSemidef.one :
    (1 : Matrix P P ℝ).PosSemidef) p).const_mul (c j p)
  rw [covariance_fun_sum_fun_sum hi hj]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    covariance_eval_multivariateGaussian Matrix.PosSemidef.one]
  simp [Matrix.one_apply, mul_ite]

/-- A finite standard Gaussian vector mapped through the actual coefficients
has the Gram Gaussian law, including singular and rectangular cases. -/
theorem candidate_measurePreserving_gaussian_linear
    {ι P : Type*} [Fintype ι] [Fintype P] [DecidableEq ι] [DecidableEq P]
    (c : Matrix ι P ℝ) :
    MeasurePreserving (candidateGaussianLinear c)
      (multivariateGaussian (0 : EuclideanSpace ℝ P) 1)
      (multivariateGaussian 0 (c * cᴴ)) where
  measurable := by fun_prop
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
      · simp
      · exact IsGaussian.integrable_id
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covariance_map]
    · have he (i : ι) : (fun x => ⟪(EuclideanSpace.basisFun ι ℝ).toBasis i, x⟫) ∘
          candidateGaussianLinear c = fun x => ∑ p, c i p * x p := by
        ext x
        change ⟪EuclideanSpace.basisFun ι ℝ i, candidateGaussianLinear c x⟫ = _
        exact EuclideanSpace.basisFun_inner (𝕜 := ℝ) (ι := ι) (candidateGaussianLinear c x) i
      simp_rw [he, candidate_gaussian_linear_covariance,
        covarianceBilin_multivariateGaussian (posSemidef_self_mul_conjTranspose c)]
      simp [Matrix.mul_apply]
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

/-- Finite sums and the kernel Gram representation have exactly the same
covariance, with counting measure supplying the independent noise indices. -/
theorem candidate_finite_gram_eq_mul_conjTranspose
    {ι P : Type*} [Fintype P] [MeasurableSpace P] [MeasurableSingletonClass P]
    (c : Matrix ι P ℝ) :
    candidateWeightedGram (Measure.count : Measure P) c (fun _ => 1) = c * cᴴ := by
  ext i j
  simp [candidateWeightedGram, Matrix.mul_apply]

/-- The Gram law is the pushforward of the literal product of independent
standard real normal variables, the law used by the replacement theorem. -/
theorem candidate_measurePreserving_pi_gaussian_linear
    {ι P : Type*} [Fintype ι] [Fintype P] [DecidableEq ι] [DecidableEq P]
    (c : Matrix ι P ℝ) :
    MeasurePreserving (fun x : P → ℝ => toLp 2 (fun i => ∑ p, c i p * x p))
      (Measure.pi (fun _ : P => gaussianReal 0 1))
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) (c * cᴴ)) := by
  have hto : MeasurePreserving (toLp 2 : (P → ℝ) → EuclideanSpace ℝ P)
      (Measure.pi (fun _ : P => gaussianReal 0 1))
      (multivariateGaussian 0 (1 : Matrix P P ℝ)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [map_pi_eq_stdGaussian, multivariateGaussian_zero_one]
  exact (candidate_measurePreserving_gaussian_linear c).comp hto

/-- Projecting all prime noises in each bin gives exactly its total mass as
the bin variance. This identity identifies the laws before mass rescaling. -/
theorem candidate_gaussian_bin_gram_eq
    {ι B : Type*} {P : B → Type*} [Fintype B] [∀ j, Fintype (P j)]
    (b : ι → B → ℝ) (w : (j : B) → P j → ℝ) (hw : ∀ j p, 0 ≤ w j p) :
    let c : Matrix ι (Sigma P) ℝ := fun i q => b i q.1 * Real.sqrt (w q.1 q.2)
    let d : Matrix ι B ℝ := fun i j => b i j * Real.sqrt (∑ p, w j p)
    c * cᴴ = d * dᴴ := by
  dsimp only
  ext i k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  have hmass : 0 ≤ ∑ p, w j p := Finset.sum_nonneg fun p _ => hw j p
  calc
    _ = ∑ p, b i j * b k j * w j p := by
      apply Finset.sum_congr rfl
      intro p _
      calc
        _ = b i j * b k j * (Real.sqrt (w j p)) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt (hw j p)]
    _ = b i j * b k j * ∑ p, w j p := (Finset.mul_sum _ _ _).symm
    _ = _ := by
      calc
        _ = b i j * b k j * (Real.sqrt (∑ p, w j p)) ^ 2 := by rw [Real.sq_sqrt hmass]
        _ = _ := by ring

end Erdos.Problem1144
