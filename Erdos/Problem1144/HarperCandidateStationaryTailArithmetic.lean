import Erdos.Problem1144.HarperCandidateSpectralCovarianceIntegrability

open MeasureTheory Set

namespace Erdos.Problem1144

/-- The literal weighted squarefree sum at logarithmic time. Its value at
negative time is zero; at nonnegative time the cutoff is `floor(exp t)`. -/
noncomputable def candidateWeightedLogProcess (ω : Omega) (t : ℝ) : ℝ :=
  if 0 ≤ t then squarefreeCriticalSum ω (⌊Real.exp t⌋₊ - 1) else 0

/-- The exact floor-normalized square error, with the deterministic
normalization factor needed by the literal complete process. -/
noncomputable def candidateLogSquareError (ω : Omega) (t : ℝ) : ℝ :=
  if 0 ≤ t then harperCandidateLogNormalization t *
    trackBError ω (⌊Real.exp t⌋₊ - 1) else 0

theorem measurable_candidateWeightedLogProcess :
    Measurable fun z : Omega × ℝ => candidateWeightedLogProcess z.1 z.2 := by
  have hR : Measurable fun z : Omega × ℕ => squarefreeCriticalSum z.1 z.2 :=
    measurable_from_prod_countable_left measurable_squarefreeCriticalSum
  exact (hR.comp (measurable_fst.prodMk
    (((Real.measurable_exp.comp measurable_snd).nat_floor).sub measurable_const))).ite
      (measurableSet_le measurable_const measurable_snd) measurable_const

theorem measurable_candidateLogSquareError :
    Measurable fun z : Omega × ℝ => candidateLogSquareError z.1 z.2 := by
  have hR : Measurable fun z : Omega × ℕ => trackBError z.1 z.2 :=
    measurable_from_prod_countable_left measurable_trackBError
  exact ((measurable_harperCandidateLogNormalization.comp measurable_snd).mul
    (hR.comp (measurable_fst.prodMk
      (((Real.measurable_exp.comp measurable_snd).nat_floor).sub measurable_const)))).ite
        (measurableSet_le measurable_const measurable_snd) measurable_const

/-- The actual logarithmic process splits exactly into the contracted
weighted sum and a square error with uniformly bounded second moment. -/
theorem candidateLogProcess_eq_weighted_add_error (ω : Omega) (t : ℝ) :
    harperCandidateLogProcess ω t =
      harperCandidateLogNormalization t * candidateWeightedLogProcess ω t +
        candidateLogSquareError ω t := by
  by_cases ht : 0 ≤ t
  · have he : normSum ω (⌊Real.exp t⌋₊ - 1) = cutoffNormSum ω ⌊Real.exp t⌋₊ := by
      simpa only [Nat.sub_add_cancel (harperCandidateLogCutoff_pos ht)] using
        normSum_eq_cutoffNormSum_succ ω (⌊Real.exp t⌋₊ - 1)
    rw [harperCandidateLogProcess_eq_cutoffNormSum_mul ω ht, ← he]
    simp only [candidateWeightedLogProcess, candidateLogSquareError, if_pos ht, trackBError]
    ring
  · simp [harperCandidateLogProcess, candidateWeightedLogProcess, candidateLogSquareError, ht]

theorem candidate_integrable_logSquareError_sq (t : ℝ) :
    Integrable (fun ω => candidateLogSquareError ω t ^ 2) mu := by
  by_cases ht : 0 ≤ t
  · simpa only [candidateLogSquareError, if_pos ht, mul_pow] using
      (integrable_trackBError_sq (⌊Real.exp t⌋₊ - 1)).const_mul
        (harperCandidateLogNormalization t ^ 2)
  · simp only [candidateLogSquareError, if_neg ht, zero_pow (by decide : 2 ≠ 0)]
    exact integrable_const (0 : ℝ)

/-- The deterministic normalization preserves the existing error bound one. -/
theorem candidate_integral_logSquareError_sq_le_one (t : ℝ) :
    (∫ ω, candidateLogSquareError ω t ^ 2 ∂mu) ≤ 1 := by
  by_cases ht : 0 ≤ t
  · simp only [candidateLogSquareError, if_pos ht, mul_pow, integral_const_mul]
    have hnorm := harperCandidateLogNormalization_mem_Icc t
    have hnsq : harperCandidateLogNormalization t ^ 2 ≤ 1 := by nlinarith [hnorm.1, hnorm.2]
    exact (mul_le_mul_of_nonneg_left (integral_trackBError_sq_le_one _)
      (sq_nonneg _)).trans (by simpa only [mul_one] using hnsq)
  · simp [candidateLogSquareError, ht]

/-- The arithmetic input for the stationary tail, with the admissible
Atherfold exponent `γ = 1` stated explicitly rather than assumed globally. -/
def CandidateWeightedLogBound (ω : Omega) (K : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → |candidateWeightedLogProcess ω t| ≤ K * Real.log (t + 2)

/-- On a weighted-bound event, the actual complete square is bounded by the
log-square majorant plus twice the literal square error. -/
theorem candidateLogProcess_sq_le_of_weighted_bound
    {ω : Omega} {K : ℝ} (hK : 0 ≤ K) (hR : CandidateWeightedLogBound ω K)
    {t : ℝ} (ht : 0 ≤ t) :
    harperCandidateLogProcess ω t ^ 2 ≤
      2 * K ^ 2 * Real.log (t + 2) ^ 2 + 2 * candidateLogSquareError ω t ^ 2 := by
  have hnorm := harperCandidateLogNormalization_mem_Icc t
  have hl : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
  have hmain : |harperCandidateLogNormalization t * candidateWeightedLogProcess ω t| ≤
      K * Real.log (t + 2) := by
    rw [abs_mul, abs_of_nonneg hnorm.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) hnorm.2).trans (hR t ht)
  have hsq : (harperCandidateLogNormalization t * candidateWeightedLogProcess ω t) ^ 2 ≤
      (K * Real.log (t + 2)) ^ 2 :=
    sq_le_sq.mpr (by simpa only [abs_of_nonneg (mul_nonneg hK hl)] using hmain)
  rw [candidateLogProcess_eq_weighted_add_error]
  nlinarith [sq_nonneg (harperCandidateLogNormalization t *
    candidateWeightedLogProcess ω t - candidateLogSquareError ω t)]

end Erdos.Problem1144
