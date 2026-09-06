import Erdos.Problem1144.HarperCandidateGaussianSlepianProduct
import Erdos.Problem1144.HarperCandidateGaussianSlepianSmoothingScalar
import Erdos.Problem1144.HarperCandidateGaussianLinear

open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators Topology MatrixOrder

namespace Erdos.Problem1144

noncomputable section

/-- Slepian comparison for the literal smooth closed-box approximation.
Its differentiability, derivative bounds and Hessian signs are all proved. -/
theorem candidate_gaussianSlepian_cutoff_comparison {n m : ℕ}
    (a b : Fin (n + 1) → Fin m → ℝ) (K : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hdiag : ∀ i, (∑ p, a p i * a p i) = ∑ p, b p i * b p i)
    (hcov : ∀ i j, i ≠ j → (∑ p, a p i * a p j) ≤ ∑ p, b p i * b p j) :
    (∫ z, ∏ i, candidateSlepianCutoff K ε (candidateGaussianColumns a z i)
      ∂candidatePiGaussian (n + 1)) ≤
    ∫ z, ∏ i, candidateSlepianCutoff K ε (candidateGaussianColumns b z i)
      ∂candidatePiGaussian (n + 1) := by
  have hφ : ContDiff ℝ 2 (candidateSlepianCutoff K ε) := candidate_slepianCutoff_contDiff K ε
  obtain ⟨B, hB, hbounds⟩ := candidate_slepianCutoff_derivative_bounds K hε
  obtain ⟨_, hmixed, C, _, hC⟩ := candidate_gaussian_product_test hφ
    (candidate_slepianCutoff_nonneg K ε) (candidate_slepianCutoff_le_one K ε)
    (candidate_slepianCutoff_deriv_nonpos K hε) hB hbounds (Finset.univ : Finset (Fin m))
  have hc : ContDiff ℝ 2 (fun x : Fin m → ℝ => ∏ i, candidateSlepianCutoff K ε (x i)) := by
    fun_prop
  exact candidate_gaussianSlepian_covariance_smooth hc (fun x => (hC x).1)
    (fun x => (hC x).2.1) (fun x => (hC x).2.2) a b hdiag hcov hmixed

/-- Ordinary finite-dimensional Slepian comparison for closed maximum boxes.
It is valid for singular Gaussian linear laws and at every real threshold. -/
theorem candidate_gaussianSlepian_linear_box {n m : ℕ}
    (a b : Fin (n + 1) → Fin m → ℝ) (K : ℝ)
    (hdiag : ∀ i, (∑ p, a p i * a p i) = ∑ p, b p i * b p i)
    (hcov : ∀ i j, i ≠ j → (∑ p, a p i * a p j) ≤ ∑ p, b p i * b p j) :
    (candidatePiGaussian (n + 1)).real {z | ∀ i, candidateGaussianColumns a z i ≤ K} ≤
      (candidatePiGaussian (n + 1)).real {z | ∀ i, candidateGaussianColumns b z i ≤ K} := by
  have ha (i : Fin m) : Measurable (fun z => candidateGaussianColumns a z i) := by
    unfold candidateGaussianColumns
    fun_prop
  have hb (i : Fin m) : Measurable (fun z => candidateGaussianColumns b z i) := by
    unfold candidateGaussianColumns
    fun_prop
  apply le_of_tendsto_of_tendsto
    (candidate_integral_slepianCutoff_product_tendsto (candidatePiGaussian (n + 1))
      (fun i z => candidateGaussianColumns a z i) ha K)
    (candidate_integral_slepianCutoff_product_tendsto (candidatePiGaussian (n + 1))
      (fun i z => candidateGaussianColumns b z i) hb K)
  exact Filter.Eventually.of_forall fun r => candidate_gaussianSlepian_cutoff_comparison
    a b K (by positivity : 0 < ((r : ℝ) + 1)⁻¹) hdiag hcov

/-- Smaller off-diagonal covariances give a larger probability of a
one-sided Gaussian maximum crossing, with no loss in probability. -/
theorem candidate_gaussianSlepian_linear_max {n m : ℕ}
    (a b : Fin (n + 1) → Fin m → ℝ) (K : ℝ)
    (hdiag : ∀ i, (∑ p, a p i * a p i) = ∑ p, b p i * b p i)
    (hcov : ∀ i j, i ≠ j → (∑ p, a p i * a p j) ≤ ∑ p, b p i * b p j) :
    (candidatePiGaussian (n + 1)).real {z | ∃ i, K < candidateGaussianColumns b z i} ≤
      (candidatePiGaussian (n + 1)).real {z | ∃ i, K < candidateGaussianColumns a z i} := by
  have hs (c : Fin (n + 1) → Fin m → ℝ) :
      MeasurableSet {z | ∀ i, candidateGaussianColumns c z i ≤ K} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le (by unfold candidateGaussianColumns; fun_prop) measurable_const
  have he (c : Fin (n + 1) → Fin m → ℝ) :
      {z | ∃ i, K < candidateGaussianColumns c z i} =
        {z | ∀ i, candidateGaussianColumns c z i ≤ K}ᶜ := by ext z; simp
  rw [he a, he b, measureReal_compl (hs a), measureReal_compl (hs b)]
  exact sub_le_sub_left (candidate_gaussianSlepian_linear_box a b K hdiag hcov) _

/-- Ordinary Slepian comparison for the canonical multivariate Gaussian laws.
Positive-semidefinite, potentially singular, covariance matrices are sufficient. -/
theorem candidate_gaussianSlepian_box {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hdiag : ∀ i, A i i = B i i) (hcov : ∀ i j, i ≠ j → A i j ≤ B i j) (K : ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) A).real {z | ∀ i, z i ≤ K} ≤
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) B).real {z | ∀ i, z i ≤ K} := by
  cases m with
  | zero => simp
  | succ m =>
      have hgram (C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hC : C.PosSemidef) :
          CFC.sqrt C * (CFC.sqrt C)ᴴ = C := by
        rw [show (CFC.sqrt C)ᴴ = CFC.sqrt C from (CFC.sqrt_nonneg C).isSelfAdjoint]
        exact CFC.sqrt_mul_sqrt_self C hC.nonneg
      have hentry (C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hC : C.PosSemidef) (i j) :
          (∑ p, CFC.sqrt C i p * CFC.sqrt C j p) = C i j := by
        have h := congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ => M i j) (hgram C hC)
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
      have hbox : MeasurableSet {z : EuclideanSpace ℝ (Fin (m + 1)) | ∀ i, z i ≤ K} := by
        simp only [setOf_forall]
        exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const
      have hmap (C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hC : C.PosSemidef) :
          (candidatePiGaussian (m + 1)).real
            {z | ∀ i, candidateGaussianColumns (fun p i => CFC.sqrt C i p) z i ≤ K} =
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin (m + 1))) C).real
            {z | ∀ i, z i ≤ K} := by
        have h := candidate_measurePreserving_pi_gaussian_linear (CFC.sqrt C)
        rw [hgram C hC] at h
        have hh := h.measureReal_preimage hbox.nullMeasurableSet
        simpa [candidateGaussianColumns, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hh
      rw [← hmap A hA, ← hmap B hB]
      apply candidate_gaussianSlepian_linear_box _ _ K
      · intro i
        rw [hentry A hA, hentry B hB, hdiag]
      · intro i j hij
        rw [hentry A hA, hentry B hB]
        exact hcov i j hij

/-- The canonical-law maximum form of Slepian: reducing pairwise covariances
while preserving variances cannot reduce the chance of an upper crossing. -/
theorem candidate_gaussianSlepian_max {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hdiag : ∀ i, A i i = B i i) (hcov : ∀ i j, i ≠ j → A i j ≤ B i j) (K : ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) B).real {z | ∃ i, K < z i} ≤
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) A).real {z | ∃ i, K < z i} := by
  have hs : MeasurableSet {z : EuclideanSpace ℝ (Fin m) | ∀ i, z i ≤ K} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const
  have he : {z : EuclideanSpace ℝ (Fin m) | ∃ i, K < z i} =
      {z | ∀ i, z i ≤ K}ᶜ := by ext z; simp
  rw [he, measureReal_compl hs, measureReal_compl hs]
  simp only [probReal_univ]
  exact sub_le_sub_left (candidate_gaussianSlepian_box A B hA hB hdiag hcov K) 1

end

end Erdos.Problem1144
