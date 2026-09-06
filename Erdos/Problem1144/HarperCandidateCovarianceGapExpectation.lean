import Erdos.Problem1144.HarperCandidateCovarianceSymmetryReduction
import Erdos.Problem1144.HarperCandidateCovarianceGapMoment

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section


/-- All actual D-star and strong-prefix conditions at the retained heights. -/
def candidateCovarianceHeightScreenEvent {n : ℕ} (start N : ℕ) (W : ℝ)
    (s : Finset ℕ) (t : Fin n → ℝ) : Set Problem520.Omega :=
  {ω | ∀ i, ω ∈ candidateCovarianceDStarEvent start N (t i) W ∩
    candidateCovarianceStrongScreenEvent start (t i) W s}

/-- The deterministic ordered frequency region, retaining the exact affine
resonance and the same finite cutoff as the original screened cell. -/
def candidateCovarianceOrderedResonanceRegion {n : ℕ} (H : ℝ)
    (ε : Fin n → ℤ) (z δ : ℝ) : Set (Fin n → ℝ) :=
  {t | (∀ i, |t i| ≤ H) ∧ |(∑ i, (ε i : ℝ) * t i) - z| ≤ δ} ∩
    candidateCovarianceOrderedPositiveHeights n

/-- Jointly measurable actual screen, including the largest height. -/
theorem candidate_measurableSet_heightScreen_joint {n : ℕ} (start N : ℕ) (W : ℝ)
    (s : Finset ℕ) : MeasurableSet {z : (Fin n → ℝ) × Problem520.Omega |
      z.2 ∈ candidateCovarianceHeightScreenEvent start N W s z.1} := by
  change MeasurableSet {z : (Fin n → ℝ) × Problem520.Omega | ∀ i : Fin n,
    z.2 ∈ candidateCovarianceDStarEvent start N (z.1 i) W ∩
      candidateCovarianceStrongScreenEvent start (z.1 i) W s}
  rw [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have hp : Measurable (fun z : (Fin n → ℝ) × Problem520.Omega => (z.1 i, z.2)) := by fun_prop
  have hd := (candidate_measurableSet_covarianceDStar_joint start N W).preimage hp
  have hs := (candidate_measurableSet_covarianceStrongScreen_joint start W s).preimage hp
  simp only [Set.preimage_setOf_eq] at hd hs
  exact hd.inter hs

/-- The all-coordinate screen is measurable at every fixed height vector. -/
theorem candidate_measurableSet_heightScreen {n : ℕ} (start N : ℕ) (W : ℝ)
    (s : Finset ℕ) (t : Fin n → ℝ) :
    MeasurableSet (candidateCovarianceHeightScreenEvent start N W s t) := by
  have h := (candidate_measurableSet_heightScreen_joint (n := n) start N W s).preimage
    (measurable_const.prodMk measurable_id : Measurable (fun ω : Problem520.Omega => (t, ω)))
  simpa only [Set.preimage_setOf_eq] using h

/-- The remaining deterministic ordered resonant region is measurable. -/
theorem candidate_measurableSet_orderedResonanceRegion {n : ℕ} (H : ℝ)
    (ε : Fin n → ℤ) (z δ : ℝ) :
    MeasurableSet (candidateCovarianceOrderedResonanceRegion H ε z δ) := by
  change MeasurableSet (({t : Fin n → ℝ | ∀ i, |t i| ≤ H} ∩
    {t : Fin n → ℝ | |(∑ i, (ε i : ℝ) * t i) - z| ≤ δ}) ∩
    ({t : Fin n → ℝ | ∀ i, 0 ≤ t i} ∩ {t : Fin n → ℝ | Monotone t}))
  apply MeasurableSet.inter
  · apply MeasurableSet.inter
    · change MeasurableSet {t : Fin n → ℝ | ∀ i, |t i| ≤ H}
      rw [setOf_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i).abs measurable_const
    · exact measurableSet_le (by fun_prop) measurable_const
  · apply MeasurableSet.inter
    · change MeasurableSet {t : Fin n → ℝ | ∀ i, 0 ≤ t i}
      rw [setOf_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)
    · change MeasurableSet {x : Fin n → ℝ | ∀ i j, i ≤ j → x i ≤ x j}
      simp_rw [setOf_forall]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
        MeasurableSet.iInter fun hij => measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)

/-- Literal joint screened squared-density product. -/
def candidateCovarianceScreenedEulerProduct (Y start N : ℕ) (W : ℝ) (s : Finset ℕ) {n : ℕ}
    (z : (Fin n → ℝ) × Problem520.Omega) : ℝ :=
  {z : (Fin n → ℝ) × Problem520.Omega | z.2 ∈ candidateCovarianceHeightScreenEvent start N W s z.1}.indicator
    (fun z => ∏ i, candidateEulerBandSquaredWeight Y z.2 (z.1 i)) z

/-- Joint measurability comes from the actual finite Euler factors. -/
theorem candidate_measurable_screenedEulerProduct (Y start N : ℕ) (W : ℝ) (s : Finset ℕ) (n : ℕ) :
    Measurable (candidateCovarianceScreenedEulerProduct Y start N W s (n := n)) := by
  apply Measurable.indicator _ (candidate_measurableSet_heightScreen_joint start N W s)
  apply Finset.measurable_fun_prod
  intro i hi
  have h := (Problem520.measurable_harperEulerDensity_div_cauchyKernel_joint Y).comp
    (by fun_prop : Measurable (fun z : (Fin n → ℝ) × Problem520.Omega => (z.1 i, z.2)))
  simpa only [Function.comp_def, candidateEulerBandSquaredWeight] using h

/-- Joint integrability on every frequency region follows from a product
of integrable Cauchy kernels and the deterministic finite-Euler bound.
This regularity bound is not used as the probabilistic moment estimate. -/
theorem candidate_integrable_screenedEulerProduct (Y start N : ℕ) (W : ℝ) (s : Finset ℕ)
    {n : ℕ} (I : Set (Fin n → ℝ)) :
    Integrable (candidateCovarianceScreenedEulerProduct Y start N W s (n := n))
      ((volume.restrict I).prod Problem520.μ) := by
  apply Integrable.indicator _ (candidate_measurableSet_heightScreen_joint start N W s)
  have hm : Measurable (fun z : (Fin n → ℝ) × Problem520.Omega =>
      ∏ i, candidateEulerBandSquaredWeight Y z.2 (z.1 i)) := by
    apply Finset.measurable_fun_prod
    intro i hi
    have h := (Problem520.measurable_harperEulerDensity_div_cauchyKernel_joint Y).comp
      (by fun_prop : Measurable (fun z : (Fin n → ℝ) × Problem520.Omega => (z.1 i, z.2)))
    simpa only [Function.comp_def, candidateEulerBandSquaredWeight] using h
  have hk : Integrable (fun t : Fin n → ℝ =>
      ∏ i, Problem520.harperEulerDensityUniformBound Y * (1 / ((1 / 2 : ℝ) ^ 2 + (t i) ^ 2))) :=
    Integrable.fintype_prod fun _ =>
      Problem520.integrable_one_div_harperCauchyKernel.const_mul (Problem520.harperEulerDensityUniformBound Y)
  have hmajor := (hk.integrableOn (s := I)).mul_prod (integrable_const (1 : ℝ) (μ := Problem520.μ))
  apply hmajor.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun z => by
    dsimp only [candidateEulerBandSquaredWeight]
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i hi =>
      div_nonneg (Problem520.harperEulerDensity_nonneg Y z.2 (z.1 i)) (by positivity))]
    simp only [mul_one]
    apply Finset.prod_le_prod
    · intro i hi
      exact div_nonneg (Problem520.harperEulerDensity_nonneg Y z.2 (z.1 i)) (by positivity)
    · intro i hi
      simpa only [candidateEulerBandSquaredWeight, mul_one_div] using
        div_le_div_of_nonneg_right (Problem520.harperEulerDensity_le_uniformBound Y z.2 (z.1 i))
          (by positivity : 0 ≤ (1 / 2 : ℝ) ^ 2 + (z.1 i) ^ 2)

private theorem integral_screenedProduct_eq (Y : ℕ) (ω : Problem520.Omega) {n : ℕ}
    (start N : ℕ) (W H : ℝ) (s : Finset ℕ) (ε : Fin n → ℤ) (z δ : ℝ) :
    (∫ t in candidateCovarianceOrderedResonanceRegion H ε z δ,
      candidateCovarianceScreenedEulerProduct Y start N W s (t, ω)) =
    ∫ t in candidateCovarianceHeightCell start N W H s ω ε z δ ∩
        candidateCovarianceOrderedPositiveHeights n,
      ∏ i, candidateEulerBandSquaredWeight Y ω (t i) := by
  have hR := candidate_measurableSet_orderedResonanceRegion H ε z δ
  have hG : MeasurableSet {t : Fin n → ℝ | ω ∈ candidateCovarianceHeightScreenEvent start N W s t} :=
    by
      have h := (candidate_measurableSet_heightScreen_joint (n := n) start N W s).preimage
        (measurable_id.prodMk measurable_const : Measurable (fun t : Fin n → ℝ => (t, ω)))
      simpa only [Set.preimage_setOf_eq] using h
  have hcell : candidateCovarianceOrderedResonanceRegion H ε z δ ∩
      {t : Fin n → ℝ | ω ∈ candidateCovarianceHeightScreenEvent start N W s t} =
      candidateCovarianceHeightCell start N W H s ω ε z δ ∩ candidateCovarianceOrderedPositiveHeights n := by
    ext t
    simp only [candidateCovarianceOrderedResonanceRegion, candidateCovarianceHeightCell,
      candidateCovarianceScreenedHeightSet, candidateCovarianceHeightScreenEvent, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨⟨hb, hr⟩, ho⟩, hs⟩
      exact ⟨⟨fun i => ⟨hb i, (hs i).1, (hs i).2⟩, hr⟩, ho⟩
    · rintro ⟨⟨hs, hr⟩, ho⟩
      exact ⟨⟨⟨fun i => (hs i).1, hr⟩, ho⟩, fun i => ⟨(hs i).2.1, (hs i).2.2⟩⟩
  have hf : (fun t => candidateCovarianceScreenedEulerProduct Y start N W s (t, ω)) =
      {t : Fin n → ℝ | ω ∈ candidateCovarianceHeightScreenEvent start N W s t}.indicator
        (fun t => ∏ i, candidateEulerBandSquaredWeight Y ω (t i)) := by
    funext t
    by_cases ht : ω ∈ candidateCovarianceHeightScreenEvent start N W s t <;>
      simp [candidateCovarianceScreenedEulerProduct, ht]
  rw [hf, integral_indicator hG, Measure.restrict_restrict hG,
    Set.inter_comm, hcell]

/-- The literal ordered screened integral is an integrable random variable. -/
theorem candidate_integrable_ordered_screened_euler_integral (Y : ℕ) {n : ℕ}
    (start N : ℕ) (W H : ℝ) (s : Finset ℕ) (ε : Fin n → ℤ) (z δ : ℝ) :
    Integrable (fun ω => ∫ t in candidateCovarianceHeightCell start N W H s ω ε z δ ∩
      candidateCovarianceOrderedPositiveHeights n,
      ∏ i, candidateEulerBandSquaredWeight Y ω (t i)) Problem520.μ := by
  simpa only [integral_screenedProduct_eq] using
    (candidate_integrable_screenedEulerProduct Y start N W s
      (candidateCovarianceOrderedResonanceRegion H ε z δ)).integral_prod_right

private theorem integral_omega_screenedProduct_eq (Y start N : ℕ) (W : ℝ) (s : Finset ℕ)
    {n : ℕ} (t : Fin n → ℝ) :
    (∫ ω, candidateCovarianceScreenedEulerProduct Y start N W s (t, ω) ∂Problem520.μ) =
      (∫ ω in candidateCovarianceHeightScreenEvent start N W s t,
        ∏ i, Problem520.harperEulerDensity Y ω (t i) ∂Problem520.μ) /
        ∏ i, ((1 / 2 : ℝ) ^ 2 + (t i) ^ 2) := by
  have hs := candidate_measurableSet_heightScreen start N W s t
  rw [← integral_div, ← integral_indicator hs]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    by_cases hω : ω ∈ candidateCovarianceHeightScreenEvent start N W s t
    · simp [candidateCovarianceScreenedEulerProduct, hω,
        candidateEulerBandSquaredWeight, Finset.prod_div_distrib]
    · simp [candidateCovarianceScreenedEulerProduct, hω]

/-- The actual Cauchy-weighted mixed expectation is integrable on the
ordered resonance region, independently of the arithmetic moment estimate. -/
theorem candidate_integrableOn_ordered_height_expectation (Y : ℕ) {n : ℕ}
    (start N : ℕ) (W H : ℝ) (s : Finset ℕ) (ε : Fin n → ℤ) (z δ : ℝ) :
    IntegrableOn (fun t =>
      (∫ ω in candidateCovarianceHeightScreenEvent start N W s t,
        ∏ i, Problem520.harperEulerDensity Y ω (t i) ∂Problem520.μ) /
        ∏ i, ((1 / 2 : ℝ) ^ 2 + (t i) ^ 2))
      (candidateCovarianceOrderedResonanceRegion H ε z δ) := by
  simpa only [integral_omega_screenedProduct_eq] using
    (candidate_integrable_screenedEulerProduct Y start N W s
      (candidateCovarianceOrderedResonanceRegion H ε z δ)).integral_prod_left

/-- Exact Fubini identity for the remaining actual row integral. Resonance
and Cauchy denominators remain explicit; the inner expectation is the
literal all-coordinate screened mixed Euler moment. -/
theorem candidate_integral_ordered_screened_euler_eq_height_expectation (Y : ℕ) {n : ℕ}
    (start N : ℕ) (W H : ℝ) (s : Finset ℕ) (ε : Fin n → ℤ) (z δ : ℝ) :
    (∫ ω, (∫ t in candidateCovarianceHeightCell start N W H s ω ε z δ ∩
        candidateCovarianceOrderedPositiveHeights n,
      ∏ i, candidateEulerBandSquaredWeight Y ω (t i)) ∂Problem520.μ) =
    ∫ t in candidateCovarianceOrderedResonanceRegion H ε z δ,
      (∫ ω in candidateCovarianceHeightScreenEvent start N W s t,
        ∏ i, Problem520.harperEulerDensity Y ω (t i) ∂Problem520.μ) /
        ∏ i, ((1 / 2 : ℝ) ^ 2 + (t i) ^ 2) := by
  simp_rw [← integral_screenedProduct_eq Y _ start N W H s ε z δ]
  rw [← integral_integral_swap (f := fun t ω => candidateCovarianceScreenedEulerProduct Y start N W s (t, ω))
    (candidate_integrable_screenedEulerProduct Y start N W s
      (candidateCovarianceOrderedResonanceRegion H ε z δ))]
  apply integral_congr_ae
  exact ae_of_all _ fun t => integral_omega_screenedProduct_eq Y start N W s t

/-- The already proved consecutive-gap moment bounds the literal
all-coordinate screen in the Fubini identity. The extra root screen is
retained on the left and can only decrease the nonnegative expectation. -/
theorem candidate_exists_allScreened_gap_product_moment_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ n start stop a : ℕ, J ≤ start → start < a → a ≤ stop →
    ∀ W : ℝ, 1 ≤ W →
    ∀ t : Fin (n + 1) → ℝ, Monotone t →
      (∀ i, 0 ≤ t i ∧ t i ≤ candidateCovarianceHeightWindow start / 2) →
    let y := Problem520.harperBlockEndpoint stop
    let g := fun i : Fin n => t i.succ - t i.castSucc
    (∫ ω in candidateCovarianceHeightScreenEvent start (stop - start) W
        (Finset.Icc (a - start) (stop - start)) t,
      ∏ i : Fin (n + 1), Problem520.harperEulerDensity y ω (t i) ∂Problem520.μ) ≤
      candidateCovarianceGapMomentFactor C D start (n + 1) *
        (Real.log (y : ℝ) / Real.log 3) *
        ∏ i : Fin n, Real.log (y : ℝ) * candidateCovarianceGapEnvelope start stop (g i) *
          candidateCovarianceGapSaving a W (g i) ^ 2 := by
  obtain ⟨C, D, hC, hD, J, hbound⟩ := candidate_exists_screened_gap_product_moment_bound
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro n start stop a hstart hsa has W hW t hmono ht
  dsimp only
  let y := Problem520.harperBlockEndpoint stop
  let E := {ω | ∀ i : Fin n, ω ∈
      candidateCovarianceDStarEvent start (stop - start) (t i.castSucc) W ∩
      candidateCovarianceStrongScreenEvent start (t i.castSucc) W
        (Finset.Icc (a - start) (stop - start))}
  have hE : MeasurableSet E :=
    candidate_measurableSet_heightScreen start (stop - start) W
      (Finset.Icc (a - start) (stop - start)) (fun i : Fin n => t i.castSucc)
  have hi : Integrable (fun ω => ∏ i : Fin (n + 1), Problem520.harperEulerDensity y ω (t i))
      Problem520.μ := by
    have hm := Finset.measurable_prod univ (fun i _ =>
      (Problem520.stronglyMeasurable_harperEulerDensity y (t i)).measurable)
    apply Integrable.of_bound hm.aestronglyMeasurable
      (Problem520.harperEulerDensityUniformBound y ^ (n + 1))
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ =>
        Problem520.harperEulerDensity_nonneg y ω (t i))]
      simpa using Finset.prod_le_prod (s := univ)
        (g := fun _ : Fin (n + 1) => Problem520.harperEulerDensityUniformBound y)
        (fun i _ => Problem520.harperEulerDensity_nonneg y ω (t i))
        (fun i _ => Problem520.harperEulerDensity_le_uniformBound y ω (t i))
  apply le_trans _ (hbound n start stop a hstart hsa has W hW t hmono ht)
  rw [← integral_indicator (candidate_measurableSet_heightScreen _ _ _ _ _)]
  apply integral_mono_of_nonneg
    (ae_of_all _ fun ω => indicator_nonneg (fun ω _ => Finset.prod_nonneg fun i _ =>
      Problem520.harperEulerDensity_nonneg y ω (t i)) ω) (hi.indicator hE)
  have hsub : candidateCovarianceHeightScreenEvent start (stop - start) W
      (Finset.Icc (a - start) (stop - start)) t ⊆ E := fun ω hω i => hω i.castSucc
  exact ae_of_all _ fun ω => Set.indicator_le_indicator_of_subset
    hsub
    (fun ω => Finset.prod_nonneg fun i _ => Problem520.harperEulerDensity_nonneg y ω (t i)) ω

end
end Erdos.Problem1144
