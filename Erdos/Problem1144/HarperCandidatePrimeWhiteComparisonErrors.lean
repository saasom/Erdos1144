import Erdos.Problem1144.HarperCandidatePrimeWhiteComparison

open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators

namespace Erdos.Problem1144

noncomputable def candidateComparisonWhiteError (sf : Bool) (ω : Omega) (t T h : ℝ) (n : ℕ) : ℝ :=
  ∫ x, (candidateComparisonWhiteStep sf ω t T h n x - candidateComparisonWhite sf ω t T x) ^ 2

noncomputable def candidateComparisonMassError (sf : Bool) (ω : Omega) (t T h : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (Real.sqrt (candidateComparisonBinMass T h j) - Real.sqrt h) ^ 2 *
    candidateComparisonEndpoint sf ω t T h j ^ 2

noncomputable def candidateComparisonStepBound (T h L : ℝ) (n : ℕ) : ℝ :=
  (4 / T) * h * (1 + (n : ℝ) * h * Real.exp h) * (1 + L) +
    (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * ((n : ℝ) * h) * (1 + L)

theorem candidate_memLp_finite_count {P : Type*} [Fintype P] [MeasurableSpace P]
    [MeasurableSingletonClass P] (f : P → ℝ) : MemLp f 2 Measure.count := by
  apply MemLp.of_bound (measurable_of_finite f).aestronglyMeasurable (∑ p, ‖f p‖)
  exact ae_of_all _ fun p ↦ Finset.single_le_sum (fun q _ ↦ norm_nonneg (f q)) (Finset.mem_univ p)

theorem measurable_candidateComparisonPrime (sf : Bool) (t T h : ℝ) (n : ℕ) :
    Measurable (fun z : Omega × candidatePrimeWhiteIndex T h n ↦
      candidateComparisonPrime sf z.1 t T h n z.2) := by
  apply measurable_from_prod_countable_left
  intro q
  change Measurable (fun ω ↦ candidateComparisonPrime sf ω t T h n q)
  unfold candidateComparisonPrime
  exact (((measurable_candidateComparisonProcess sf).comp
    measurable_prodMk_right).div_const _).mul_const _

theorem measurable_candidateComparisonPrimeStep (sf : Bool) (t T h : ℝ) (n : ℕ) :
    Measurable (fun z : Omega × candidatePrimeWhiteIndex T h n ↦
      candidateComparisonPrimeStep sf z.1 t T h n z.2) := by
  apply measurable_from_prod_countable_left
  intro q
  change Measurable (fun ω ↦ candidateComparisonPrimeStep sf ω t T h n q)
  unfold candidateComparisonPrimeStep candidateComparisonEndpoint
  exact (((measurable_candidateComparisonProcess sf).comp
    measurable_prodMk_right).div_const _).mul_const _

theorem measurable_candidateComparisonMassBin (sf : Bool) (t T h : ℝ) (n : ℕ) :
    Measurable (fun z : Omega × Fin n ↦ candidateComparisonMassBin sf z.1 t T h n z.2) := by
  apply measurable_from_prod_countable_left
  intro q
  change Measurable (fun ω ↦ candidateComparisonMassBin sf ω t T h n q)
  unfold candidateComparisonMassBin candidateComparisonEndpoint
  exact (((measurable_candidateComparisonProcess sf).comp
    measurable_prodMk_right).div_const _).mul_const _

theorem measurable_candidateComparisonWhiteBin (sf : Bool) (t T h : ℝ) (n : ℕ) :
    Measurable (fun z : Omega × Fin n ↦ candidateComparisonWhiteBin sf z.1 t T h n z.2) := by
  apply measurable_from_prod_countable_left
  intro q
  change Measurable (fun ω ↦ candidateComparisonWhiteBin sf ω t T h n q)
  unfold candidateComparisonWhiteBin candidateComparisonEndpoint
  exact (((measurable_candidateComparisonProcess sf).comp
    measurable_prodMk_right).div_const _).mul_const _

theorem measurable_candidateComparisonWhite (sf : Bool) (t T : ℝ) :
    Measurable (fun z : Omega × ℝ ↦ candidateComparisonWhite sf z.1 t T z.2) := by
  cases sf
  · exact measurable_candidateCompleteWhiteKernel t T
  · exact measurable_candidateSquarefreeWhiteKernel t T

theorem measurable_candidateComparisonWhiteStep (sf : Bool) (t T h : ℝ) (n : ℕ) :
    Measurable (fun z : Omega × ℝ ↦ candidateComparisonWhiteStep sf z.1 t T h n z.2) := by
  cases sf
  · exact measurable_candidateCompleteWhiteStepKernel t T h n
  · exact measurable_candidateSquarefreeWhiteStepKernel t T h n

theorem candidate_memLp_comparisonWhite (sf : Bool) (ω : Omega) (t : ℝ) {T : ℝ} (hT : 0 < T) :
    MemLp (candidateComparisonWhite sf ω t T) 2 volume := by
  cases sf
  · exact candidate_memLp_completeWhiteKernel ω t hT
  · exact candidate_memLp_squarefreeWhiteKernel ω t hT

theorem candidate_memLp_comparisonWhiteStep (sf : Bool) (ω : Omega) (t T : ℝ)
    {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    MemLp (candidateComparisonWhiteStep sf ω t T h n) 2 volume := by
  cases sf
  · exact candidate_memLp_completeWhiteStepKernel ω t T hh n
  · exact candidate_memLp_squarefreeWhiteStepKernel ω t T hh n

theorem candidate_comparison_mass_error_eq (sf : Bool) (ω : Omega) (t T h : ℝ) (n : ℕ) :
    (∫ j, (candidateComparisonMassBin sf ω t T h n j -
      candidateComparisonWhiteBin sf ω t T h n j) ^ 2 ∂Measure.count) =
        candidateComparisonMassError sf ω t T h n := by
  rw [integral_count]
  simp only [candidateComparisonMassBin, candidateComparisonWhiteBin, ← mul_sub, mul_pow]
  calc
    _ = ∑ j : Fin n, (Real.sqrt (candidateComparisonBinMass T h j) - Real.sqrt h) ^ 2 *
        candidateComparisonEndpoint sf ω t T h j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    _ = _ := Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
      (Real.sqrt (candidateComparisonBinMass T h j) - Real.sqrt h) ^ 2 *
        candidateComparisonEndpoint sf ω t T h j ^ 2) n

theorem candidate_integrable_comparisonPrimeEnergy (sf : Bool) (t T h : ℝ) (n : ℕ) :
    Integrable (fun ω ↦ candidateComparisonPrimeEnergy sf ω t T h n) mu := by
  cases sf
  · exact candidate_integrable_primeStepEnergy t T h n
  · exact candidate_integrable_squarefreePrimeStepEnergy t T h n

theorem candidate_integrable_comparisonEndpoint_sq (sf : Bool) (t T h : ℝ) (j : ℕ) :
    Integrable (fun ω ↦ candidateComparisonEndpoint sf ω t T h j ^ 2) mu := by
  simpa only [candidateComparisonEndpoint, div_eq_mul_inv] using
    ((candidate_memLp_comparisonProcess sf (t - (T + (j : ℝ) * h + h))).mul_const
      (Real.sqrt (T + (j : ℝ) * h + h))⁻¹).integrable_sq

theorem candidate_integrable_comparisonMassError (sf : Bool) (t T h : ℝ) (n : ℕ) :
    Integrable (fun ω ↦ candidateComparisonMassError sf ω t T h n) mu :=
  integrable_finset_sum _ fun j _ ↦
    (candidate_integrable_comparisonEndpoint_sq sf t T h j).const_mul _

theorem candidate_integrable_comparisonWhiteError (sf : Bool) {t T h : ℝ} {n : ℕ}
    (hT : 0 < T) (hh : 0 ≤ h) (hcover : t ≤ T + (n : ℝ) * h) :
    Integrable (fun ω ↦ candidateComparisonWhiteError sf ω t T h n) mu := by
  unfold candidateComparisonWhiteError
  simp_rw [sub_sq_comm]
  cases sf
  · exact candidate_integrable_completeWhiteKernel_step_error hT hh hcover
  · exact candidate_integrable_squarefreeWhiteKernel_step_error hT hh hcover

theorem candidate_comparisonPrimeEnergy_nonneg (sf : Bool) (ω : Omega) (t T h : ℝ) (n : ℕ) :
    0 ≤ candidateComparisonPrimeEnergy sf ω t T h n := by
  rw [← candidate_comparison_prime_error_eq]
  exact integral_nonneg fun _ ↦ sq_nonneg _

theorem candidate_comparisonMassError_nonneg (sf : Bool) (ω : Omega) (t T h : ℝ) (n : ℕ) :
    0 ≤ candidateComparisonMassError sf ω t T h n :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem candidate_comparisonWhiteError_nonneg (sf : Bool) (ω : Omega) (t T h : ℝ) (n : ℕ) :
    0 ≤ candidateComparisonWhiteError sf ω t T h n := integral_nonneg fun _ ↦ sq_nonneg _

/-- The same literal endpoint second-moment bound works for both models. -/
theorem candidate_integral_comparisonEndpoint_sq_le (sf : Bool) {t T h L : ℝ}
    (hT : 0 < T) (hh : 0 ≤ h) (hL : 0 ≤ L) (ht : t - T ≤ L) (j : ℕ) :
    (∫ ω, candidateComparisonEndpoint sf ω t T h j ^ 2 ∂mu) ≤ (1 + L) / T := by
  have hjh : 0 ≤ (j : ℝ) * h + h := by positivity
  have hy : 0 < T + (j : ℝ) * h + h := by linarith
  cases sf
  · exact candidate_integral_logCoefficient_sq_le hT (by linarith) hL (by linarith)
  · simp only [candidateComparisonEndpoint, candidateComparisonProcess, ↓reduceIte,
      div_pow, integral_div, Real.sq_sqrt hy.le]
    apply div_le_div₀ (by positivity)
      ((candidate_integral_squarefreeLog_sq_le_one _).trans (by linarith)) hT
    linarith

/-- A finite quantitative normalization error, on the actual prime-bin
masses, for the complete and squarefree processes alike. -/
theorem candidate_integral_comparisonMassError_le (sf : Bool) {t T h L r : ℝ} {n : ℕ}
    (hT : 0 < T) (hh : 0 < h) (hL : 0 ≤ L) (ht : t - T ≤ L)
    (hmass : ∀ j ∈ Finset.range n, |candidateComparisonBinMass T h j / h - 1| ≤ r) :
    (∫ ω, candidateComparisonMassError sf ω t T h n ∂mu) ≤
      ((n : ℝ) * h) * r ^ 2 * ((1 + L) / T) := by
  unfold candidateComparisonMassError
  rw [integral_finset_sum _ (fun j _ ↦
    (candidate_integrable_comparisonEndpoint_sq sf t T h j).const_mul _)]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∑ _j ∈ Finset.range n, h * r ^ 2 * ((1 + L) / T) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul
        (candidate_sqrt_mass_difference_sq_le (candidateComparisonBinMass_nonneg T h j)
          hh (hmass j hj))
        (candidate_integral_comparisonEndpoint_sq_le sf hT hh.le hL ht j)
        (integral_nonneg fun _ ↦ sq_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem candidate_integral_comparisonPrimeEnergy_le (sf : Bool) {t T h L : ℝ} {n : ℕ}
    (hT : 0 < T) (hh : 0 < h) (hL : 0 ≤ L) (ht : t - T + h ≤ L)
    (hmass : ∀ j ∈ Finset.range n, |candidateComparisonBinMass T h j / h - 1| ≤ 1) :
    (∫ ω, candidateComparisonPrimeEnergy sf ω t T h n ∂mu) ≤
      2 * candidateComparisonStepBound T h L n := by
  have hm : ∀ j ∈ Finset.range n,
      |Problem520.weightedPrimeReciprocalBlock ⌊Real.exp (T + (j : ℝ) * h)⌋₊
        ⌊Real.exp (T + (j : ℝ) * h + h)⌋₊ / h - 1| ≤ 1 := by
    intro j hj
    convert hmass j hj using 1
  cases sf
  · exact candidate_integral_primeStepEnergy_le hT hh hL ht hm
  · exact candidate_integral_squarefreePrimeStepEnergy_le hT hh hL ht hm

theorem candidate_integral_comparisonWhiteError_le (sf : Bool) {t T h L : ℝ} {n : ℕ}
    (hT : 0 < T) (hh : 0 ≤ h) (hL : 0 ≤ L) (ht : t - T + h ≤ L)
    (hcover : t ≤ T + (n : ℝ) * h) :
    (∫ ω, candidateComparisonWhiteError sf ω t T h n ∂mu) ≤
      candidateComparisonStepBound T h L n := by
  unfold candidateComparisonWhiteError
  simp_rw [sub_sq_comm]
  cases sf
  · exact candidate_integral_completeWhiteKernel_step_error_le hT hh ht hL hcover
  · exact candidate_integral_squarefreeWhiteKernel_step_error_le hT hh ht hL hcover

end Erdos.Problem1144
