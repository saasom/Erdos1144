import Erdos.Problem1144.HarperCandidateGaussianNormalization

open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators
namespace Erdos.Problem1144
noncomputable section

/-- Selected absolute crossing under the literal centered Gaussian law. -/
def candidateGaussianSelectedCrossing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (J : Finset ι) (K : ℝ) : ℝ :=
  (multivariateGaussian (0 : EuclideanSpace ℝ ι) A).real {x | ∃ i ∈ J, K < |x i|}

/-- An unselected Gaussian maximum tail; this pays for either omitted
stationary component in the complete/squarefree comparison. -/
def candidateGaussianMaximumTail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (ε : ℝ) : ℝ :=
  (multivariateGaussian (0 : EuclideanSpace ℝ ι) A).real {x | ∃ i, ε ≤ |x i|}

private theorem selected_measurable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (K : ℝ) :
    MeasurableSet {x : EuclideanSpace ℝ ι | ∃ i ∈ J, K < |x i|} := by
  simp only [setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : i ∈ J
  · simpa only [hi, true_and] using
      (measurableSet_lt (f := fun _ : EuclideanSpace ℝ ι => K)
        (g := fun x => |x i|) measurable_const (by fun_prop))
  · simp [hi]

/-- Coordinate scaling transfers a selected crossing with its exact
minimum scale. Selection is arbitrary and fixed only within this fiber. -/
theorem candidate_gaussian_selected_diagonal_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (r : ι → ℝ)
    (J : Finset ι) (K : ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hr : ∀ i ∈ J, r₀ ≤ |r i|) :
    candidateGaussianSelectedCrossing A J K ≤
      candidateGaussianSelectedCrossing (candidateCovarianceDiagonal r A) J (r₀ * K) := by
  unfold candidateGaussianSelectedCrossing
  rw [← (candidate_measurePreserving_gaussian_diagonal hA r).measureReal_preimage
    (selected_measurable J (r₀ * K)).nullMeasurableSet]
  apply measureReal_mono
  rintro x ⟨i, hi, hx⟩
  refine ⟨i, hi, ?_⟩
  change r₀ * K < |r i * x i|
  rw [abs_mul]
  exact (mul_lt_mul_of_pos_left hx hr₀).trans_le
    (mul_le_mul_of_nonneg_right (hr i hi) (abs_nonneg _))
  all_goals finiteness

/-- Constant coordinate scaling identifies the selected crossing law
exactly, without requiring nonsingular covariance. -/
theorem candidate_gaussian_selected_smul_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (J : Finset ι) (K : ℝ)
    {c : ℝ} (hc : 0 < c) :
    candidateGaussianSelectedCrossing (c • A) J (Real.sqrt c * K) =
      candidateGaussianSelectedCrossing A J K := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have he : candidateCovarianceDiagonal (fun _ : ι => Real.sqrt c) A = c • A := by
    ext i j
    simp only [candidateCovarianceDiagonal, Matrix.smul_apply, smul_eq_mul]
    nlinarith only [congrArg (fun z : ℝ => z * A i j) (Real.sq_sqrt hc.le)]
  unfold candidateGaussianSelectedCrossing
  rw [← he, ← (candidate_measurePreserving_gaussian_diagonal hA
    (fun _ => Real.sqrt c)).measureReal_preimage (selected_measurable J (Real.sqrt c * K)).nullMeasurableSet]
  congr 1
  ext x
  simp only [mem_preimage, mem_setOf_eq, candidateGaussianDiagonal_apply,
    abs_mul, abs_of_pos hs, mul_lt_mul_iff_right₀ hs]

/-- Removing an independent Gaussian covariance component costs its actual
maximum-tail probability and one fixed threshold margin. -/
theorem candidate_gaussian_selected_sum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A H : Matrix ι ι ℝ} (hA : A.PosSemidef) (hH : H.PosSemidef)
    (J : Finset ι) (K ε : ℝ) :
    candidateGaussianSelectedCrossing (A + H) J (K + ε) ≤
      candidateGaussianSelectedCrossing A J K + candidateGaussianMaximumTail H ε := by
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) A
  let ν := multivariateGaussian (0 : EuclideanSpace ℝ ι) H
  have hm := selected_measurable J (K + ε)
  have hsum : candidateGaussianSelectedCrossing (A + H) J (K + ε) =
      (μ.prod ν).real {z | ∃ i ∈ J, K + ε < |z.1 i + z.2 i|} := by
    unfold candidateGaussianSelectedCrossing
    rw [← candidate_multivariateGaussian_conv hA hH]
    change ((((μ.prod ν).map (fun z => z.1 + z.2)) _).toReal) = _
    rw [Measure.map_apply (by fun_prop) hm]
    rfl
  rw [hsum]
  have hsub : {z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι | ∃ i ∈ J, K + ε < |z.1 i + z.2 i|} ⊆
      ({x | ∃ i ∈ J, K < |x i|} ×ˢ univ) ∪ (univ ×ˢ {x | ∃ i, ε ≤ |x i|}) := by
    rintro z ⟨i, hi, hzi⟩
    by_cases he : ε ≤ |z.2 i|
    · exact Or.inr ⟨mem_univ _, i, he⟩
    · left
      refine ⟨⟨i, hi, ?_⟩, mem_univ _⟩
      have ht := abs_add_le (z.1 i) (z.2 i)
      linarith
  apply (measureReal_mono hsub).trans
  apply (measureReal_union_le _ _).trans_eq
  simp only [measureReal_prod_prod, measureReal_univ_eq_one, mul_one, one_mul]
  rfl

/-- The complete three-PSD/two-tail comparison, under actual Gaussian laws.
This is the finite-dimensional algebra of the stationary bridge. Every
selector survives unchanged and only a universal factor eight is lost. -/
theorem candidate_gaussian_stationary_selected_comparison
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A L H Q E B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hL : L.PosSemidef) (hH : H.PosSemidef)
    (hQ : Q.PosSemidef) (hE : E.PosSemidef) (hB : B.PosSemidef)
    (r d : ι → ℝ) {c lam r₀ : ℝ} (hc : 0 < c) (hlam : 0 < lam) (hr₀ : 0 < r₀)
    (hfirst : (L + H - candidateCovarianceDiagonal r A).PosSemidef)
    (hmiddle : (Q + E - c • L).PosSemidef)
    (hlast : (lam • B - candidateCovarianceDiagonal d Q).PosSemidef)
    (J : Finset ι) (hr : ∀ i ∈ J, r₀ ≤ |r i|) (hd : ∀ i ∈ J, 1 ≤ |d i|)
    (K εS εC : ℝ) :
    candidateGaussianSelectedCrossing A J
      (((Real.sqrt lam * K + εC) / Real.sqrt c + εS) / r₀) / 8 ≤
      candidateGaussianSelectedCrossing B J K +
        candidateGaussianMaximumTail H εS / 4 + candidateGaussianMaximumTail E εC / 2 := by
  let KL := (Real.sqrt lam * K + εC) / Real.sqrt c
  have hcroot : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hfirst' := candidate_multivariateGaussian_selected_absolute_ge_half
    (candidateCovarianceDiagonal_posSemidef hA r) hfirst J (KL + εS)
  have hdiag := candidate_gaussian_selected_diagonal_le hA r J ((KL + εS) / r₀) hr₀ hr
  rw [mul_div_cancel₀ _ hr₀.ne'] at hdiag
  have hsf := candidate_gaussian_selected_sum_le hL hH J KL εS
  have hscaled : (c • L).PosSemidef := by
    have hh := candidateCovarianceDiagonal_posSemidef hL (fun _ => Real.sqrt c)
    convert hh using 1
    ext i j
    simp only [candidateCovarianceDiagonal, Matrix.smul_apply, smul_eq_mul]
    nlinarith only [congrArg (fun z : ℝ => z * L i j) (Real.sq_sqrt hc.le)]
  have hmiddle' := candidate_multivariateGaussian_selected_absolute_ge_half hscaled hmiddle J
    (Real.sqrt lam * K + εC)
  have hscale := candidate_gaussian_selected_smul_eq hL J KL hc
  have heq : Real.sqrt c * KL = Real.sqrt lam * K + εC := by dsimp only [KL]; field_simp
  rw [heq] at hscale
  have hcomplete := candidate_gaussian_selected_sum_le hQ hE J (Real.sqrt lam * K) εC
  have hdiag' := candidate_gaussian_selected_diagonal_le hQ d J (Real.sqrt lam * K)
    (by norm_num : (0 : ℝ) < 1) hd
  simp only [one_mul] at hdiag'
  have hlast' := candidate_multivariateGaussian_selected_absolute_ge_half
    (candidateCovarianceDiagonal_posSemidef hQ d) hlast J (Real.sqrt lam * K)
  have hscale' := candidate_gaussian_selected_smul_eq hB J K hlam
  change candidateGaussianSelectedCrossing _ _ _ / 2 ≤ candidateGaussianSelectedCrossing _ _ _ at hfirst'
  change candidateGaussianSelectedCrossing _ _ _ / 2 ≤ candidateGaussianSelectedCrossing _ _ _ at hmiddle'
  change candidateGaussianSelectedCrossing _ _ _ / 2 ≤ candidateGaussianSelectedCrossing _ _ _ at hlast'
  rw [hscale] at hmiddle'
  rw [hscale'] at hlast'
  dsimp only [KL] at *
  linarith

end
end Erdos.Problem1144
