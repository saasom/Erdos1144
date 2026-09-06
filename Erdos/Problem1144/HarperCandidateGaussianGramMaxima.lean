import Erdos.Problem1144.HarperCandidateGaussianRealization
import Erdos.Problem1144.HarperCandidateGaussianMaxima

open MeasureTheory ProbabilityTheory Set Matrix WithLp
open scoped BigOperators NNReal

namespace Erdos.Problem1144

/-- A difference in the actual Gaussian Gram law is centered Gaussian with
variance equal to the squared distance between its kernels. -/
theorem candidate_gaussian_gram_difference_map
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace V]
    (ν : Measure V) (f : ι → V → ℝ) (hf : ∀ i, MemLp (f i) 2 ν) (i j : ι) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (candidateWeightedGram ν f (fun _ => 1))).map (fun x => x i - x j) =
      gaussianReal 0 (∫ v, (f i v - f j v) ^ 2 ∂ν).toNNReal := by
  let A := candidateWeightedGram ν f (fun _ => 1)
  have hA : A.PosSemidef := candidateWeightedGram_posSemidef ν f (fun _ => 1)
    (fun i j => by simpa only [one_mul] using (hf i).integrable_mul (hf j))
    (ae_of_all _ fun _ => Or.inl zero_le_one)
  let L : EuclideanSpace ℝ ι →L[ℝ] ℝ := EuclideanSpace.proj i - EuclideanSpace.proj j
  have hL : (fun x : EuclideanSpace ℝ ι => x i - x j) = L := rfl
  rw [hL, IsGaussian.map_eq_gaussianReal]
  have hm : (∫ x, L x ∂multivariateGaussian (0 : EuclideanSpace ℝ ι) A) = 0 := by
    rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_multivariateGaussian]
    exact map_zero L
  change gaussianReal _ _ = _
  rw [hm, variance_eq_integral (show AEMeasurable L (multivariateGaussian 0 A) from
    L.measurable.aemeasurable), hm]
  simp only [sub_zero]
  congr 1
  congr 1
  exact candidate_gaussian_gram_difference_secondMoment ν f hf i j

/-- A common kernel-error bound gives an exponential maximum-error estimate
for the literal joint Gram Gaussian; no independence of coordinates is needed. -/
theorem candidate_gaussian_gram_coupling_exponential_le
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace V]
    (ν : Measure V) (f g : ι → V → ℝ)
    (hf : ∀ i, MemLp (f i) 2 ν) (hg : ∀ i, MemLp (g i) 2 ν)
    {v : ℝ≥0} (hvar : ∀ i, (∫ t, (f i t - g i t) ^ 2 ∂ν) ≤ v)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (ι ⊕ ι))
      (candidateWeightedGram ν (Sum.elim f g) (fun _ => 1))).real
        {x | ∃ i, ε ≤ |x (Sum.inl i) - x (Sum.inr i)|} ≤
      2 * Fintype.card ι * Real.exp (-ε ^ 2 / (2 * v)) := by
  have hF (i : ι ⊕ ι) : MemLp (Sum.elim f g i) 2 ν := by
    cases i with
    | inl i => exact hf i
    | inr i => exact hg i
  exact candidate_gaussian_maximum_tail_le
    (fun i => candidate_gaussian_gram_difference_map ν (Sum.elim f g) hF
      (Sum.inl i) (Sum.inr i))
    (fun i => Real.toNNReal_le_iff_le_coe.mpr (hvar i)) hε

/-- Selected maxima transfer between two Gram laws with the Gaussian
exponential cost of their common kernel-error variance. -/
theorem candidate_gaussian_gram_selected_crossing_exponential_le
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace V]
    (ν : Measure V) (f g : ι → V → ℝ)
    (hf : ∀ i, MemLp (f i) 2 ν) (hg : ∀ i, MemLp (g i) 2 ν)
    {v : ℝ≥0} (hvar : ∀ i, (∫ t, (f i t - g i t) ^ 2 ∂ν) ≤ v)
    (J : Finset ι) (K : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (candidateWeightedGram ν g (fun _ => 1))).real {x | ∃ i ∈ J, K + ε < |x i|} ≤
    (multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (candidateWeightedGram ν f (fun _ => 1))).real {x | ∃ i ∈ J, K < |x i|} +
      2 * Fintype.card ι * Real.exp (-ε ^ 2 / (2 * v)) := by
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
  exact h.trans (add_le_add (le_refl _)
    (candidate_gaussian_gram_coupling_exponential_le ν f g hf hg hvar hε))

/-- Averaged selected maxima pay only the logarithm of the grid cardinality
for a common random kernel-error variance. The kernels and selector may depend
on the same environment, and the conclusion concerns their actual Gram laws. -/
theorem candidate_integral_gaussian_gram_selected_crossing_log_variance_on_le
    {Ω V ι : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (ν : Measure V) [SFinite ν]
    (f g : ι → Ω → V → ℝ)
    (hf : ∀ i, Measurable (Function.uncurry (f i)))
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (hf2 : ∀ ω i, MemLp (f i ω) 2 ν) (hg2 : ∀ ω i, MemLp (g i ω) 2 ν)
    (J : Ω → Finset ι) (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω})
    (D : Set Ω) (hD : MeasurableSet D)
    (E : Ω → ℝ) (hE : Integrable E Q) (hE0 : ∀ ω, 0 ≤ E ω)
    (hvar : ∀ ω ∈ D, ∀ i, (∫ t, (f i ω t - g i ω t) ^ 2 ∂ν) ≤ E ω)
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, (multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (candidateWeightedGram ν (fun i t => g i ω t) (fun _ => 1))).real
        {x | ∃ i ∈ J ω, K + ε < |x i|} ∂Q) ≤
    (∫ ω, (multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (candidateWeightedGram ν (fun i t => f i ω t) (fun _ => 1))).real
        {x | ∃ i ∈ J ω, K < |x i|} ∂Q) + Q.real Dᶜ +
      4 * Real.log (2 * Fintype.card ι) * (∫ ω, E ω ∂Q) / ε ^ 2 +
        1 / (2 * Fintype.card ι) := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hl : 0 < Real.log (2 * Fintype.card ι) := Real.log_pos (by linarith)
  let v : ℝ≥0 := ⟨ε ^ 2 / (4 * Real.log (2 * Fintype.card ι)), by positivity⟩
  have hv : (0 : ℝ) < v := by change 0 < ε ^ 2 / (4 * Real.log (2 * Fintype.card ι)); positivity
  let c := 2 * (Fintype.card ι : ℝ) * Real.exp (-ε ^ 2 / (2 * v))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let F := fun ω => (multivariateGaussian (0 : EuclideanSpace ℝ ι)
    (candidateWeightedGram ν (fun i t => f i ω t) (fun _ => 1))).real
      {x | ∃ i ∈ J ω, K < |x i|}
  let G := fun ω => (multivariateGaussian (0 : EuclideanSpace ℝ ι)
    (candidateWeightedGram ν (fun i t => g i ω t) (fun _ => 1))).real
      {x | ∃ i ∈ J ω, K + ε < |x i|}
  have hFpos (ω : Ω) : (candidateWeightedGram ν (fun i t => f i ω t)
      (fun _ => 1)).PosSemidef := candidateWeightedGram_posSemidef ν _ _
    (fun i j => by simpa only [one_mul] using (hf2 ω i).integrable_mul (hf2 ω j))
    (ae_of_all _ fun _ => Or.inl zero_le_one)
  have hGpos (ω : Ω) : (candidateWeightedGram ν (fun i t => g i ω t)
      (fun _ => 1)).PosSemidef := candidateWeightedGram_posSemidef ν _ _
    (fun i j => by simpa only [one_mul] using (hg2 ω i).integrable_mul (hg2 ω j))
    (ae_of_all _ fun _ => Or.inl zero_le_one)
  have hiF : Integrable F Q := candidate_integrable_gaussian_selected_probability Q
    (candidate_measurable_random_gram ν f hf) hFpos J hJ K
  have hiG : Integrable G Q := candidate_integrable_gaussian_selected_probability Q
    (candidate_measurable_random_gram ν g hg) hGpos J hJ (K + ε)
  let bad := Dᶜ.indicator (fun _ => (1 : ℝ))
  have hibad : Integrable bad Q := (integrable_const _).indicator hD.compl
  have hpoint (ω : Ω) : G ω ≤ F ω + bad ω + E ω / v + c := by
    have hEdiv : 0 ≤ E ω / v := div_nonneg (hE0 ω) hv.le
    have hF0 : 0 ≤ F ω := measureReal_nonneg
    by_cases hωD : ω ∈ D
    · have hbad : bad ω = 0 := by simp [bad, hωD]
      rw [hbad, add_zero]
      by_cases hω : E ω ≤ v
      · have hh := candidate_gaussian_gram_selected_crossing_exponential_le ν
          (fun i t => f i ω t) (fun i t => g i ω t) (hf2 ω) (hg2 ω)
          (fun i => (hvar ω hωD i).trans hω) (J ω) K hε.le
        change G ω ≤ F ω + c at hh
        linarith
      · have hh : G ω ≤ 1 := measureReal_le_one
        have hrat : 1 ≤ E ω / v := (one_le_div hv).mpr (le_of_not_ge hω)
        linarith
    · have hbad : bad ω = 1 := by simp [bad, hωD]
      rw [hbad]
      have hh : G ω ≤ 1 := measureReal_le_one
      linarith
  have hint := integral_mono hiG (((hiF.add hibad).add (hE.div_const (v : ℝ))).add
    (integrable_const c)) hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_add (show Integrable (fun ω => F ω + bad ω + E ω / v) Q from
      (hiF.add hibad).add (hE.div_const (v : ℝ))) (integrable_const c),
    integral_add (show Integrable (fun ω => F ω + bad ω) Q from hiF.add hibad)
      (hE.div_const (v : ℝ)), integral_add hiF hibad, integral_div, integral_const,
    probReal_univ, one_smul] at hint
  have hbadint : (∫ ω, bad ω ∂Q) = Q.real Dᶜ := by
    simpa [bad] using integral_indicator_const (μ := Q) (1 : ℝ) hD.compl
  rw [hbadint] at hint
  have he : -ε ^ 2 / (2 * (v : ℝ)) = -(2 * Real.log (2 * Fintype.card ι)) := by
    change -ε ^ 2 / (2 * (ε ^ 2 / (4 * Real.log (2 * Fintype.card ι)))) = _
    field_simp [hε.ne', hl.ne']
    ring
  have hceq : c = 1 / (2 * Fintype.card ι) := by
    dsimp [c]
    rw [he, Real.exp_neg,
      show 2 * Real.log (2 * Fintype.card ι) =
        Real.log (2 * Fintype.card ι) + Real.log (2 * Fintype.card ι) by ring,
      Real.exp_add, Real.exp_log (by positivity)]
    field_simp
  rw [hceq] at hint
  have hveq : (∫ ω, E ω ∂Q) / (v : ℝ) =
      4 * Real.log (2 * Fintype.card ι) * (∫ ω, E ω ∂Q) / ε ^ 2 := by
    change (∫ ω, E ω ∂Q) / (ε ^ 2 / (4 * Real.log (2 * Fintype.card ι))) = _
    field_simp
  rw [hveq] at hint
  exact hint

/-- Averaged selected maxima pay only the logarithm of the grid cardinality
for a common random kernel-error variance. The kernels and selector may depend
on the same environment, and the conclusion concerns their actual Gram laws. -/
theorem candidate_integral_gaussian_gram_selected_crossing_log_variance_le
    {Ω V ι : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (ν : Measure V) [SFinite ν]
    (f g : ι → Ω → V → ℝ)
    (hf : ∀ i, Measurable (Function.uncurry (f i)))
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (hf2 : ∀ ω i, MemLp (f i ω) 2 ν) (hg2 : ∀ ω i, MemLp (g i ω) 2 ν)
    (J : Ω → Finset ι) (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω})
    (E : Ω → ℝ) (hE : Integrable E Q) (hE0 : ∀ ω, 0 ≤ E ω)
    (hvar : ∀ ω i, (∫ t, (f i ω t - g i ω t) ^ 2 ∂ν) ≤ E ω)
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, (multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (candidateWeightedGram ν (fun i t => g i ω t) (fun _ => 1))).real
        {x | ∃ i ∈ J ω, K + ε < |x i|} ∂Q) ≤
    (∫ ω, (multivariateGaussian (0 : EuclideanSpace ℝ ι)
      (candidateWeightedGram ν (fun i t => f i ω t) (fun _ => 1))).real
        {x | ∃ i ∈ J ω, K < |x i|} ∂Q) +
      4 * Real.log (2 * Fintype.card ι) * (∫ ω, E ω ∂Q) / ε ^ 2 +
        1 / (2 * Fintype.card ι) := by
  have h := candidate_integral_gaussian_gram_selected_crossing_log_variance_on_le
    Q ν f g hf hg hf2 hg2 J hJ Set.univ MeasurableSet.univ E hE hE0
    (fun ω _ i => hvar ω i) K hε
  simpa only [Set.compl_univ, measureReal_empty, add_zero] using h

end Erdos.Problem1144
