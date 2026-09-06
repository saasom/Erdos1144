import Erdos.Problem1144.HarperCandidateGaussianComparison
import Erdos.Problem1144.HarperCandidateCovariance
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Set Matrix WithLp
open scoped BigOperators RealInnerProductSpace

namespace Erdos.Problem1144

/-!
# Finite-dimensional Gaussian coupling for square-integrable kernels

Two finite kernel families can share a joint Gaussian Gram law. Its coordinate
errors have exactly the squared kernel distances as their second moments.
This supplies the finite-grid coupling construction without a Brownian path.
-/

noncomputable def candidateGaussianCoordinates {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ → ι) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ where
  toFun x := toLp 2 (fun j => x (e j))
  map_add' x y := by ext j; simp
  map_smul' a x := by ext j; simp
  cont := Continuous.comp' (by fun_prop) (continuous_pi (by dsimp; fun_prop))

@[simp] theorem candidateGaussianCoordinates_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ → ι)
    (x : EuclideanSpace ℝ ι) (j : κ) : candidateGaussianCoordinates e x j = x (e j) := rfl

/-- Every coordinate subfamily has exactly its Gaussian submatrix law,
including repeated coordinates and singular covariance matrices. -/
theorem candidate_measurePreserving_gaussian_coordinates
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (e : κ → ι) :
    MeasurePreserving (candidateGaussianCoordinates e) (multivariateGaussian 0 A)
      (multivariateGaussian 0 (A.submatrix e e)) where
  measurable := by fun_prop
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
      · simp
      · exact IsGaussian.integrable_id
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun κ ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covariance_map]
    · have he (i : κ) : (fun x => ⟪(EuclideanSpace.basisFun κ ℝ).toBasis i, x⟫) ∘
          candidateGaussianCoordinates e = fun x => x (e i) := by
        ext x
        change ⟪EuclideanSpace.basisFun κ ℝ i, candidateGaussianCoordinates e x⟫ = x (e i)
        exact EuclideanSpace.basisFun_inner (𝕜 := ℝ) (ι := κ)
          (candidateGaussianCoordinates e x) i
      simp_rw [he, covariance_eval_multivariateGaussian hA,
        covarianceBilin_multivariateGaussian (hA.submatrix e)]
      simp
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

theorem candidate_gaussian_eval_mean_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (i : ι) :
    (∫ x, x i ∂multivariateGaussian (0 : EuclideanSpace ℝ ι) A) = 0 := by
  change (∫ x, (EuclideanSpace.proj i) x ∂multivariateGaussian (0 : EuclideanSpace ℝ ι) A) = 0
  rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
    integral_id_multivariateGaussian]
  simp

theorem candidate_gaussian_eval_memLp_two
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (i : ι) :
    MemLp (fun x => x i) 2 (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) := by
  have h := (IsGaussian.memLp_two_id (μ := gaussianReal 0 (A i i).toNNReal)).comp_measurePreserving
    (measurePreserving_eval_multivariateGaussian (μ := 0) hA (i := i))
  simpa using h

/-- In a centered Gaussian vector, coordinate-difference second moments
are the corresponding quadratic covariance expression. -/
theorem candidate_gaussian_coordinate_difference_secondMoment
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (i j : ι) :
    (∫ x, (x i - x j) ^ 2 ∂multivariateGaussian (0 : EuclideanSpace ℝ ι) A) =
      A i i - 2 * A i j + A j j := by
  have hi := candidate_gaussian_eval_memLp_two hA i
  have hj := candidate_gaussian_eval_memLp_two hA j
  have hm : (∫ x, (x i - x j) ∂multivariateGaussian (0 : EuclideanSpace ℝ ι) A) = 0 := by
    rw [integral_sub (hi.integrable (by norm_num)) (hj.integrable (by norm_num)),
      candidate_gaussian_eval_mean_zero, candidate_gaussian_eval_mean_zero, sub_self]
  have hv := variance_fun_sub hi hj
  have hmeas : AEMeasurable (fun x : EuclideanSpace ℝ ι => x i - x j)
      (multivariateGaussian 0 A) := by fun_prop
  rw [variance_eq_integral hmeas, hm] at hv
  simp only [sub_zero] at hv
  rw [variance_eval_multivariateGaussian hA, variance_eval_multivariateGaussian hA,
    covariance_eval_multivariateGaussian hA] at hv
  exact hv

/-- The joint Gaussian Gram construction realizes kernel distances exactly.
This is the isometry used by the prime-bin/white-noise approximation. -/
theorem candidate_gaussian_gram_difference_secondMoment
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (ν : Measure Ω) (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 ν) (i j : ι) :
    (∫ x, (x i - x j) ^ 2 ∂multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (candidateWeightedGram ν f (fun _ => 1))) = ∫ v, (f i v - f j v) ^ 2 ∂ν := by
  have hA : (candidateWeightedGram ν f (fun _ => 1)).PosSemidef :=
    candidateWeightedGram_posSemidef ν f (fun _ => 1)
      (fun i j => by simpa only [one_mul] using (hf i).integrable_mul (hf j))
      (ae_of_all _ fun _ => Or.inl zero_le_one)
  rw [candidate_gaussian_coordinate_difference_secondMoment hA]
  simp only [candidateWeightedGram, one_mul]
  have hi : Integrable (fun v => f i v * f i v) ν := (hf i).integrable_mul (hf i)
  have hj : Integrable (fun v => f j v * f j v) ν := (hf j).integrable_mul (hf j)
  have hij : Integrable (fun v => 2 * (f i v * f j v)) ν :=
    ((hf i).integrable_mul (hf j)).const_mul 2
  have he : (fun v => (f i v - f j v) ^ 2) =
      (fun v => (f i v * f i v - 2 * (f i v * f j v)) + f j v * f j v) := by
    funext v
    ring
  have hsub : Integrable (fun v => f i v * f i v - 2 * (f i v * f j v)) ν := hi.sub hij
  rw [he, integral_add hsub hj, integral_sub hi hij, integral_const_mul]

/-- A joint Gram Gaussian couples two finite kernel families with the
sum-of-squared-errors maximum bound. -/
theorem candidate_gaussian_gram_coupling_failure_le
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (ν : Measure Ω) (f g : ι → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) 2 ν) (hg : ∀ i, MemLp (g i) 2 ν)
    {ε : ℝ} (hε : 0 < ε) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (ι ⊕ ι))
      (candidateWeightedGram ν (Sum.elim f g) (fun _ => 1))).real
        {x | ∃ i, ε ≤ |x (Sum.inl i) - x (Sum.inr i)|} ≤
      (∑ i, ∫ v, (f i v - g i v) ^ 2 ∂ν) / ε ^ 2 := by
  classical
  let F := Sum.elim f g
  have hF (i : ι ⊕ ι) : MemLp (F i) 2 ν := by
    cases i with
    | inl i => exact hf i
    | inr i => exact hg i
  let A := candidateWeightedGram ν F (fun _ => 1)
  have hA : A.PosSemidef := candidateWeightedGram_posSemidef ν F (fun _ => 1)
    (fun i j => by simpa only [one_mul] using (hF i).integrable_mul (hF j))
    (ae_of_all _ fun _ => Or.inl zero_le_one)
  let Γ := multivariateGaussian (0 : EuclideanSpace ℝ (ι ⊕ ι)) A
  change Γ.real {x | ∃ i, ε ≤ |x (Sum.inl i) - x (Sum.inr i)|} ≤ _
  rw [show {x : EuclideanSpace ℝ (ι ⊕ ι) | ∃ i, ε ≤ |x (Sum.inl i) - x (Sum.inr i)|} =
    ⋃ i, {x | ε ≤ |x (Sum.inl i) - x (Sum.inr i)|} by ext; simp]
  calc
    _ ≤ ∑ i, Γ.real {x | ε ≤ |x (Sum.inl i) - x (Sum.inr i)|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ i, (∫ v, (f i v - g i v) ^ 2 ∂ν) / ε ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := (candidate_gaussian_eval_memLp_two hA (Sum.inl i)).sub
        (candidate_gaussian_eval_memLp_two hA (Sum.inr i))
      have hm := mul_meas_ge_le_integral_of_nonneg (μ := Γ)
        (f := fun x : EuclideanSpace ℝ (ι ⊕ ι) => (x (Sum.inl i) - x (Sum.inr i)) ^ 2)
        (ae_of_all _ fun x => sq_nonneg (x (Sum.inl i) - x (Sum.inr i))) hi.integrable_sq (ε ^ 2)
      have hevent : {x : EuclideanSpace ℝ (ι ⊕ ι) | ε ^ 2 ≤ (x (Sum.inl i) - x (Sum.inr i)) ^ 2} =
          {x | ε ≤ |x (Sum.inl i) - x (Sum.inr i)|} := by
        ext x
        simpa only [Set.mem_setOf_eq, sq_abs] using
          (sq_le_sq₀ hε.le (abs_nonneg (x (Sum.inl i) - x (Sum.inr i))))
      rw [hevent] at hm
      have he := candidate_gaussian_gram_difference_secondMoment ν F hF (Sum.inl i) (Sum.inr i)
      change (∫ x, (x (Sum.inl i) - x (Sum.inr i)) ^ 2 ∂Γ) = _ at he
      rw [he] at hm
      exact (le_div_iff₀ (sq_pos_of_pos hε)).mpr
        (by simpa only [mul_comm, F, Sum.elim_inl, Sum.elim_inr] using hm)
    _ = _ := (Finset.sum_div _ _ _).symm

/-- Kernel approximation transfers selected absolute maxima under the actual
Gaussian laws, with a threshold margin and an explicit squared-error loss.
No independence between the coordinates or selection restriction is needed. -/
theorem candidate_gaussian_gram_selected_crossing_le
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (ν : Measure Ω) (f g : ι → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) 2 ν) (hg : ∀ i, MemLp (g i) 2 ν)
    (J : Finset ι) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (candidateWeightedGram ν g (fun _ => 1))).real {x | ∃ i ∈ J, K + ε < |x i|} ≤
    (multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (candidateWeightedGram ν f (fun _ => 1))).real {x | ∃ i ∈ J, K < |x i|} +
      (∑ i, ∫ v, (f i v - g i v) ^ 2 ∂ν) / ε ^ 2 := by
  let F := Sum.elim f g
  have hF (i : ι ⊕ ι) : MemLp (F i) 2 ν := by
    cases i with
    | inl i => exact hf i
    | inr i => exact hg i
  let A := candidateWeightedGram ν F (fun _ => 1)
  have hA : A.PosSemidef := candidateWeightedGram_posSemidef ν F (fun _ => 1)
    (fun i j => by simpa only [one_mul] using (hF i).integrable_mul (hF j))
    (ae_of_all _ fun _ => Or.inl zero_le_one)
  let Γ := multivariateGaussian (0 : EuclideanSpace ℝ (ι ⊕ ι)) A
  have hmeas (c : ℝ) : MeasurableSet {x : EuclideanSpace ℝ ι | ∃ i ∈ J, c < |x i|} := by
    rw [show {x : EuclideanSpace ℝ ι | ∃ i ∈ J, c < |x i|} =
      ⋃ i ∈ J, {x | c < |x i|} by ext; simp]
    exact Finset.measurableSet_biUnion J fun i _ =>
      measurableSet_lt measurable_const (by fun_prop)
  have hprob (e : ι → ι ⊕ ι) (c : ℝ) :
      Γ.real {x | ∃ i ∈ J, c < |x (e i)|} =
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) (A.submatrix e e)).real
          {x | ∃ i ∈ J, c < |x i|} := by
    have hmap := candidate_measurePreserving_gaussian_coordinates hA e
    change _ = ((multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (A.submatrix e e)) {x | ∃ i ∈ J, c < |x i|}).toReal
    rw [← hmap.map_eq, Measure.map_apply hmap.measurable (hmeas c)]
    rfl
  have hcover : {x : EuclideanSpace ℝ (ι ⊕ ι) | ∃ i ∈ J, K + ε < |x (Sum.inr i)|} ⊆
      {x | ∃ i ∈ J, K < |x (Sum.inl i)|} ∪
        {x | ∃ i, ε ≤ |x (Sum.inl i) - x (Sum.inr i)|} := by
    rintro x ⟨i, hi, hx⟩
    by_cases he : ε ≤ |x (Sum.inl i) - x (Sum.inr i)|
    · exact Or.inr ⟨i, he⟩
    · left
      refine ⟨i, hi, ?_⟩
      have htri := abs_sub_le (x (Sum.inr i)) (x (Sum.inl i)) 0
      rw [sub_zero, sub_zero, abs_sub_comm (x (Sum.inr i))] at htri
      linarith
  have h := (measureReal_mono (μ := Γ) hcover).trans (measureReal_union_le _ _)
  rw [hprob Sum.inr (K + ε), hprob Sum.inl K] at h
  have herr := candidate_gaussian_gram_coupling_failure_le ν f g hf hg hε
  change Γ.real {x | ∃ i, ε ≤ |x (Sum.inl i) - x (Sum.inr i)|} ≤ _ at herr
  exact h.trans (add_le_add (le_refl _) herr)

end Erdos.Problem1144
