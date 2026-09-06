import Erdos.Problem1144.HarperCandidateCovarianceGapExpectation
import Erdos.Problem1144.HarperCandidateCovarianceGapResonance

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- Literal internal-gap profile; the last coordinate is the retained
right endpoint and carries no additional gap factor. -/
def candidateCovarianceGapProductProfile (start stop a : ℕ) (W : ℝ) (n : ℕ)
    (g : Fin (n + 1) → ℝ) : ℝ :=
  ∏ i : Fin n, candidateCovarianceGapEnvelope start stop (g i.castSucc) *
    candidateCovarianceGapSaving a W (g i.castSucc) ^ 2

/-- The piecewise strong/ordinary gap saving is measurable. -/
theorem candidate_measurable_gapSaving (a : ℕ) (W : ℝ) :
    Measurable (candidateCovarianceGapSaving a W) := by
  unfold candidateCovarianceGapSaving
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

/-- The actual product of bounded gap weights is measurable. -/
theorem candidate_measurable_gapProductProfile (start stop a : ℕ) (W : ℝ) (n : ℕ) :
    Measurable (candidateCovarianceGapProductProfile start stop a W n) := by
  apply Finset.measurable_fun_prod
  intro i hi
  exact (((candidate_continuous_gapEnvelope start stop).measurable.comp
    (measurable_pi_apply i.castSucc)).mul
    (((candidate_measurable_gapSaving a W).comp (measurable_pi_apply i.castSucc)).pow_const 2))

/-- The actual gap profile is nonnegative everywhere. -/
theorem candidate_gapProductProfile_nonneg (start stop a : ℕ) (W : ℝ) (n : ℕ)
    (g : Fin (n + 1) → ℝ) : 0 ≤ candidateCovarianceGapProductProfile start stop a W n g :=
  Finset.prod_nonneg fun i hi => mul_nonneg (candidate_gapEnvelope_nonneg start stop _) (sq_nonneg _)

private theorem saving_sq_bound (a : ℕ) (W g : ℝ) :
    candidateCovarianceGapSaving a W g ^ 2 ≤ max ((W ^ 1000)⁻¹ ^ 2) ((W ^ 6) ^ 2) := by
  unfold candidateCovarianceGapSaving
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- Regularity of the literal gap profile on the full finite box. No
moment, positivity, or cutoff-selection hypothesis is needed here. -/
theorem candidate_integrableOn_gapProductProfile (start stop a : ℕ) (W M : ℝ) (n : ℕ) :
    IntegrableOn (candidateCovarianceGapProductProfile start stop a W n)
      (Set.univ.pi fun _ : Fin (n + 1) => Icc (0 : ℝ) M) := by
  let K := Real.log (Problem520.harperBlockEndpoint stop : ℝ) *
    max ((W ^ 1000)⁻¹ ^ 2) ((W ^ 6) ^ 2)
  have hb (g : Fin (n + 1) → ℝ) : candidateCovarianceGapProductProfile start stop a W n g ≤ K ^ n := by
    calc
      _ ≤ ∏ _i : Fin n, K := Finset.prod_le_prod
        (fun i hi => mul_nonneg (candidate_gapEnvelope_nonneg start stop _) (sq_nonneg _))
        (fun i hi => mul_le_mul (candidate_gapEnvelope_le_top start stop _)
          (saving_sq_bound a W _) (sq_nonneg _)
          ((Problem520.one_le_log_harperBlockEndpoint stop).trans' (by norm_num)))
      _ = _ := by simp
  change Integrable _ ((Measure.pi fun _ : Fin (n + 1) => volume).restrict _)
  rw [Measure.restrict_pi_pi]
  apply (integrable_const (K ^ n)).mono'
    (candidate_measurable_gapProductProfile start stop a W n).aestronglyMeasurable
  exact ae_of_all _ fun g => by
    rw [Real.norm_eq_abs, abs_of_nonneg (candidate_gapProductProfile_nonneg start stop a W n g)]
    exact hb g

/-- The exact product Cauchy denominator costs at most four per height. -/
theorem candidate_inverse_product_cauchy_le (n : ℕ) (t : Fin n → ℝ) :
    1 / (∏ i, ((1 / 2 : ℝ) ^ 2 + (t i) ^ 2)) ≤ (4 : ℝ) ^ n := by
  calc
    _ = ∏ i, (1 / ((1 / 2 : ℝ) ^ 2 + (t i) ^ 2)) := by simp [Finset.prod_div_distrib]
    _ ≤ ∏ _i : Fin n, (4 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        apply (div_le_iff₀ (by positivity : 0 < (1 / 2 : ℝ) ^ 2 + (t i) ^ 2)).mpr
        nlinarith [sq_nonneg (t i)]
    _ = _ := by simp

private theorem region_subset_orderedBox {n : ℕ} (M : ℝ) (σ : Fin n → ℤ) (z δ : ℝ) :
    candidateCovarianceOrderedResonanceRegion M σ z δ ⊆ candidateOrderedHeightBox n M := by
  intro t ht
  refine ⟨ht.2.2, fun i => ⟨ht.2.1 i, ?_⟩⟩
  exact (le_abs_self _).trans (ht.1.1 i)

/-- Genuine arithmetic-to-gap reduction. The expectation, all original
screens, Cauchy denominators, affine resonance, and volume-preserving
coordinate transformation are discharged. The sole remaining integral is
the literal bounded gap profile over the full gap box. -/
theorem candidate_exists_ordered_screened_euler_le_gap_integral :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ n start stop a : ℕ, J ≤ start → start < a → a ≤ stop →
    ∀ W : ℝ, 1 ≤ W → ∀ M : ℝ, M ≤ candidateCovarianceHeightWindow start / 2 →
    ∀ σ : Fin (n + 1) → ℤ, ∀ z δ : ℝ,
    let Y := Problem520.harperBlockEndpoint stop
    (∫ ω, (∫ t in candidateCovarianceHeightCell start (stop - start) W M
          (Finset.Icc (a - start) (stop - start)) ω σ z δ ∩
          candidateCovarianceOrderedPositiveHeights (n + 1),
        ∏ i, candidateEulerBandSquaredWeight Y ω (t i)) ∂Problem520.μ) ≤
      ((4 : ℝ) ^ (n + 1) * candidateCovarianceGapMomentFactor C D start (n + 1) *
        Real.log (Y : ℝ) ^ (n + 1) / Real.log 3) *
      ∫ g in Set.univ.pi (fun _ : Fin (n + 1) => Icc (0 : ℝ) M),
        {g : Fin (n + 1) → ℝ | |(∑ i, (candidateGapCoefficients n σ i : ℝ) * g i) - z| ≤ δ}.indicator
          (candidateCovarianceGapProductProfile start stop a W n) g := by
  obtain ⟨C, D, hC, hD, J, hmoment⟩ := candidate_exists_allScreened_gap_product_moment_bound
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro n start stop a hstart hsa has W hW M hM σ z δ
  dsimp only
  let Y := Problem520.harperBlockEndpoint stop
  let L := Real.log (Y : ℝ)
  let B := candidateCovarianceGapMomentFactor C D start (n + 1) * L ^ (n + 1) / Real.log 3
  let K := (4 : ℝ) ^ (n + 1) * B
  let s := Finset.Icc (a - start) (stop - start)
  let R := candidateCovarianceOrderedResonanceRegion M σ z δ
  let A := {g : Fin (n + 1) → ℝ | |(∑ i, (candidateGapCoefficients n σ i : ℝ) * g i) - z| ≤ δ}
  let P := candidateCovarianceGapProductProfile start stop a W n
  let e := fun t : Fin (n + 1) → ℝ =>
    (∫ ω in candidateCovarianceHeightScreenEvent start (stop - start) W s t,
      ∏ i, Problem520.harperEulerDensity Y ω (t i) ∂Problem520.μ) /
      ∏ i, ((1 / 2 : ℝ) ^ 2 + (t i) ^ 2)
  have hL : 0 ≤ L := (Problem520.one_le_log_harperBlockEndpoint stop).trans' (by norm_num)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg (candidate_gapMomentFactor_nonneg C D start _) (pow_nonneg hL _)) (by positivity)
  have hK : 0 ≤ K := mul_nonneg (by positivity) hB
  have hR : MeasurableSet R := candidate_measurableSet_orderedResonanceRegion M σ z δ
  have hA : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  have he : IntegrableOn e R :=
    candidate_integrableOn_ordered_height_expectation Y start (stop - start) W M s σ z δ
  have hFi : IntegrableOn (fun g => K * A.indicator P g)
      (Set.univ.pi fun _ : Fin (n + 1) => Icc (0 : ℝ) M) :=
    ((candidate_integrableOn_gapProductProfile start stop a W M n).indicator hA).const_mul K
  have hFn (g : Fin (n + 1) → ℝ) : 0 ≤ K * A.indicator P g :=
    mul_nonneg hK (indicator_nonneg (fun g hg => candidate_gapProductProfile_nonneg start stop a W n g) _)
  have hpoint (t : Fin (n + 1) → ℝ) (ht : t ∈ candidateOrderedHeightBox (n + 1) M) :
      R.indicator e t ≤ K * A.indicator P (candidateGapCoordinates (n + 1) t) := by
    by_cases htr : t ∈ R
    · have hres : candidateGapCoordinates (n + 1) t ∈ A := by
        change |(∑ i, (candidateGapCoefficients n σ i : ℝ) * candidateGapCoordinates (n + 1) t i) - z| ≤ δ
        rw [← candidate_signedHeights_eq_gapCoefficients]
        exact htr.1.2
      rw [indicator_of_mem htr, indicator_of_mem hres]
      have hm := hmoment n start stop a hstart hsa has W hW t ht.1
        (fun i => ⟨(ht.2 i).1, (ht.2 i).2.trans hM⟩)
      dsimp only at hm
      have hprod : (∏ i : Fin n, L * candidateCovarianceGapEnvelope start stop (t i.succ - t i.castSucc) *
          candidateCovarianceGapSaving a W (t i.succ - t i.castSucc) ^ 2) =
          L ^ n * P (candidateGapCoordinates (n + 1) t) := by
        simp only [P, candidateCovarianceGapProductProfile, candidateGapCoordinates_apply_gap]
        simp_rw [mul_assoc, Finset.prod_mul_distrib]
        simp
      have hm' : (∫ ω in candidateCovarianceHeightScreenEvent start (stop - start) W s t,
          ∏ i, Problem520.harperEulerDensity Y ω (t i) ∂Problem520.μ) ≤
          B * P (candidateGapCoordinates (n + 1) t) := by
        change _ ≤ _ at hm
        change (∫ ω in candidateCovarianceHeightScreenEvent start (stop - start) W s t,
          ∏ i, Problem520.harperEulerDensity Y ω (t i) ∂Problem520.μ) ≤
          candidateCovarianceGapMomentFactor C D start (n + 1) * (L / Real.log 3) *
            (∏ i : Fin n, L * candidateCovarianceGapEnvelope start stop (t i.succ - t i.castSucc) *
              candidateCovarianceGapSaving a W (t i.succ - t i.castSucc) ^ 2) at hm
        rw [hprod] at hm
        convert hm using 1 <;> dsimp only [B] <;> rw [pow_succ] <;> ring
      have hden : 0 ≤ ∏ i, ((1 / 2 : ℝ) ^ 2 + (t i) ^ 2) := by positivity
      calc
        e t ≤ (B * P (candidateGapCoordinates (n + 1) t)) /
            (∏ i, ((1 / 2 : ℝ) ^ 2 + (t i) ^ 2)) := div_le_div_of_nonneg_right hm' hden
        _ = (B * P (candidateGapCoordinates (n + 1) t)) *
            (1 / (∏ i, ((1 / 2 : ℝ) ^ 2 + (t i) ^ 2))) := by ring
        _ ≤ (B * P (candidateGapCoordinates (n + 1) t)) * (4 : ℝ) ^ (n + 1) :=
          mul_le_mul_of_nonneg_left (candidate_inverse_product_cauchy_le (n + 1) t)
            (mul_nonneg hB (candidate_gapProductProfile_nonneg start stop a W n _))
        _ = _ := by dsimp only [K]; ring
    · rw [indicator_of_notMem htr]
      exact hFn _
  have hg := candidate_integral_orderedHeightBox_le_gap_box (n + 1) M (R.indicator e)
    (fun g => K * A.indicator P g) (he.integrable_indicator hR).integrableOn hFi
    (fun g hg => hFn g) hpoint
  have hsub : R ∩ candidateOrderedHeightBox (n + 1) M = R :=
    inter_eq_left.mpr (region_subset_orderedBox M σ z δ)
  rw [integral_indicator hR, Measure.restrict_restrict hR, hsub, integral_const_mul] at hg
  rw [candidate_integral_ordered_screened_euler_eq_height_expectation]
  convert hg using 1 <;> dsimp only [K, B, L, Y, R, e, A, P, s] <;> ring

end
end Erdos.Problem1144
