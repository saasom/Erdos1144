import Erdos.Problem1144.HarperCandidateGaussianCoupling

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace

namespace Erdos.Problem1144

noncomputable section

/-- Coordinatewise scaling on the actual finite Gaussian space. -/
def candidateGaussianDiagonal {ι : Type*} [Fintype ι] (r : ι → ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι where
  toFun x := toLp 2 (fun i => r i * x i)
  map_add' x y := by ext i; simp [mul_add]
  map_smul' a x := by ext i; simp [mul_left_comm]
  cont := Continuous.comp' (by fun_prop) (continuous_pi (by dsimp; fun_prop))

@[simp] theorem candidateGaussianDiagonal_apply {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    candidateGaussianDiagonal r x i = r i * x i := rfl

theorem candidateCovarianceDiagonal_posSemidef {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (r : ι → ℝ) :
    (candidateCovarianceDiagonal r A).PosSemidef := by
  convert hA.mul_mul_conjTranspose_same (Matrix.diagonal r) using 1
  ext i j
  simp [candidateCovarianceDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Scaling each coordinate preserves the exact Gaussian law with the
correspondingly scaled covariance, including singular matrices. -/
theorem candidate_measurePreserving_gaussian_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (r : ι → ℝ) :
    MeasurePreserving (candidateGaussianDiagonal r) (multivariateGaussian 0 A)
      (multivariateGaussian 0 (candidateCovarianceDiagonal r A)) where
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
          candidateGaussianDiagonal r = fun x => r i * x i := by
        ext x
        change ⟪EuclideanSpace.basisFun ι ℝ i, candidateGaussianDiagonal r x⟫ = _
        exact EuclideanSpace.basisFun_inner (𝕜 := ℝ) (ι := ι)
          (candidateGaussianDiagonal r x) i
      simp_rw [he, covariance_const_mul_left, covariance_const_mul_right,
        covariance_eval_multivariateGaussian hA,
        covarianceBilin_multivariateGaussian (candidateCovarianceDiagonal_posSemidef hA r)]
      simp [candidateCovarianceDiagonal, mul_assoc, mul_comm, mul_left_comm]
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

end

end Erdos.Problem1144
