import Erdos.Problem1144.HarperCandidateTranslationWhiteKernel
import Erdos.Problem1144.HarperCandidateGaussianRealization
import Erdos.Problem1144.HarperCandidateGaussianLinear
import Erdos.Problem1144.HarperCandidatePrimeNormalization
import Erdos.Problem1144.HarperCandidateSpectralTail

open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators

namespace Erdos.Problem1144

/-! Literal prime/white comparison, simultaneously for the complete (`false`)
and squarefree (`true`) processes. All finite noise indices are actual primes. -/

noncomputable def candidateComparisonProcess (sf : Bool) : Omega → ℝ → ℝ :=
  if sf then harperCandidateSquarefreeLogProcess else harperCandidateLogProcess

noncomputable def candidateComparisonWhite (sf : Bool) : Omega → ℝ → ℝ → ℝ → ℝ :=
  if sf then candidateSquarefreeWhiteKernel else candidateCompleteWhiteKernel

noncomputable def candidateComparisonWhiteStep (sf : Bool) : Omega → ℝ → ℝ → ℝ → ℕ → ℝ → ℝ :=
  if sf then candidateSquarefreeWhiteStepKernel else candidateCompleteWhiteStepKernel

noncomputable def candidateComparisonPrimeEnergy (sf : Bool) : Omega → ℝ → ℝ → ℝ → ℕ → ℝ :=
  if sf then candidateSquarefreePrimeStepEnergy else candidatePrimeStepEnergy

/-- A prime is indexed by its unique whole logarithmic bin. -/
def candidatePrimeWhiteIndex (T h : ℝ) (n : ℕ) : Type :=
  Σ j : Fin n, ↥(candidateLogPrimeBin (T + (j : ℝ) * h) h)

noncomputable instance (T h : ℝ) (n : ℕ) : Fintype (candidatePrimeWhiteIndex T h n) :=
  inferInstanceAs (Fintype (Σ j : Fin n, ↥(candidateLogPrimeBin (T + (j : ℝ) * h) h)))
noncomputable instance (T h : ℝ) (n : ℕ) : DecidableEq (candidatePrimeWhiteIndex T h n) :=
  Classical.decEq _
instance (T h : ℝ) (n : ℕ) : MeasurableSpace (candidatePrimeWhiteIndex T h n) := ⊤
instance (T h : ℝ) (n : ℕ) : MeasurableSingletonClass (candidatePrimeWhiteIndex T h n) :=
  ⟨fun _ ↦ trivial⟩

noncomputable def candidateComparisonEndpoint (sf : Bool) (ω : Omega) (t T h : ℝ) (j : ℕ) : ℝ :=
  candidateComparisonProcess sf ω (t - (T + (j : ℝ) * h + h)) /
    Real.sqrt (T + (j : ℝ) * h + h)

noncomputable def candidateComparisonBinMass (T h : ℝ) (j : ℕ) : ℝ :=
  ∑ p ∈ candidateLogPrimeBin (T + (j : ℝ) * h) h, Real.log (p : ℝ) / p

noncomputable def candidateComparisonPrime (sf : Bool) (ω : Omega) (t T h : ℝ) (n : ℕ)
    (q : candidatePrimeWhiteIndex T h n) : ℝ :=
  candidateComparisonProcess sf ω (t - Real.log (q.2.val : ℝ)) /
    Real.sqrt (Real.log (q.2.val : ℝ)) * Real.sqrt (Real.log (q.2.val : ℝ) / q.2.val)

noncomputable def candidateComparisonPrimeStep (sf : Bool) (ω : Omega) (t T h : ℝ) (n : ℕ)
    (q : candidatePrimeWhiteIndex T h n) : ℝ :=
  candidateComparisonEndpoint sf ω t T h q.1.val *
    Real.sqrt (Real.log (q.2.val : ℝ) / q.2.val)

noncomputable def candidateComparisonMassBin (sf : Bool) (ω : Omega) (t T h : ℝ) (n : ℕ)
    (j : Fin n) : ℝ :=
  candidateComparisonEndpoint sf ω t T h j * Real.sqrt (candidateComparisonBinMass T h j)

noncomputable def candidateComparisonWhiteBin (sf : Bool) (ω : Omega) (t T h : ℝ) (n : ℕ)
    (j : Fin n) : ℝ :=
  candidateComparisonEndpoint sf ω t T h j * Real.sqrt h

theorem measurable_candidateComparisonProcess (sf : Bool) :
    Measurable (Function.uncurry (candidateComparisonProcess sf)) := by
  cases sf
  · exact measurable_harperCandidateLogProcess
  · exact measurable_harperCandidateSquarefreeLogProcess

theorem candidate_memLp_comparisonProcess (sf : Bool) (t : ℝ) :
    MemLp (fun ω ↦ candidateComparisonProcess sf ω t) 2 mu := by
  apply (memLp_two_iff_integrable_sq
    ((measurable_candidateComparisonProcess sf).comp measurable_prodMk_right).aestronglyMeasurable).mpr
  cases sf
  · exact candidate_integrable_logProcess_sq t
  · exact candidate_integrable_squarefreeLog_pow t 2

theorem candidateComparisonBinMass_nonneg (T h : ℝ) (j : ℕ) :
    0 ≤ candidateComparisonBinMass T h j :=
  Finset.sum_nonneg fun _ hp ↦ candidate_logPrimeBin_weight_nonneg hp

/-- The prime kernel is exactly the coefficient of its independent standard
normal prime noise, with the logarithmic weight canceled. -/
theorem candidateComparisonPrime_eq (sf : Bool) (ω : Omega) (t T h : ℝ) (n : ℕ)
    (q : candidatePrimeWhiteIndex T h n) :
    candidateComparisonPrime sf ω t T h n q =
      candidateComparisonProcess sf ω (t - Real.log (q.2.val : ℝ)) / Real.sqrt q.2.val := by
  have hp := (Finset.mem_filter.mp q.2.property).2
  have hp0 : (0 : ℝ) < q.2.val := Nat.cast_pos.mpr hp.pos
  have hl : 0 < Real.log (q.2.val : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  unfold candidateComparisonPrime
  rw [Real.sqrt_div (le_of_lt hl)]
  field_simp

/-- Projection of every prime in a bin has precisely the total prime mass
as covariance; this is an equality of literal finite covariance matrices. -/
theorem candidate_comparison_primeStep_gram_eq {ι : Type*} (sf : Bool) (ω : Omega)
    (t : ι → ℝ) (T h : ℝ) (n : ℕ) :
    candidateWeightedGram Measure.count (fun i ↦ candidateComparisonPrimeStep sf ω (t i) T h n)
      (fun _ ↦ 1) =
    candidateWeightedGram Measure.count (fun i ↦ candidateComparisonMassBin sf ω (t i) T h n)
      (fun _ ↦ 1) := by
  rw [candidate_finite_gram_eq_mul_conjTranspose, candidate_finite_gram_eq_mul_conjTranspose]
  have he := candidate_gaussian_bin_gram_eq
    (fun i (j : Fin n) ↦ candidateComparisonEndpoint sf ω (t i) T h j)
    (fun (j : Fin n) (p : ↥(candidateLogPrimeBin (T + (j : ℝ) * h) h)) ↦
      Real.log (p.val : ℝ) / p.val)
    (fun _ p ↦ candidate_logPrimeBin_weight_nonneg p.property)
  have hm (j : Fin n) :
      (∑ p : ↥(candidateLogPrimeBin (T + (j : ℝ) * h) h), Real.log (p.val : ℝ) / p.val) =
        candidateComparisonBinMass T h j :=
    Finset.sum_coe_sort _ (fun p : ℕ ↦ Real.log (p : ℝ) / p)
  simp_rw [hm] at he
  exact he

/-- White bin normal variables and the literal white step kernel have equal
covariance, with bin length supplying the exact white-noise variance. -/
theorem candidate_comparison_whiteBin_gram_eq {ι : Type*} (sf : Bool) (ω : Omega)
    (t : ι → ℝ) (T : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    candidateWeightedGram Measure.count (fun i ↦ candidateComparisonWhiteBin sf ω (t i) T h n)
      (fun _ ↦ 1) =
    candidateWeightedGram volume (fun i ↦ candidateComparisonWhiteStep sf ω (t i) T h n)
      (fun _ ↦ 1) := by
  have hs : candidateComparisonWhiteStep sf ω = fun t T h n ↦
      candidateWholeBinStep T h n (candidateComparisonEndpoint sf ω t T h) := by
    cases sf <;> rfl
  rw [hs, candidate_wholeBinStep_gram_eq hh]
  ext i k
  simp only [candidateWeightedGram, one_mul, integral_count,
    candidateComparisonWhiteBin]
  calc
    _ = ∑ j : Fin n, h * candidateComparisonEndpoint sf ω (t i) T h j *
        candidateComparisonEndpoint sf ω (t k) T h j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show candidateComparisonEndpoint sf ω (t i) T h j * Real.sqrt h *
              (candidateComparisonEndpoint sf ω (t k) T h j * Real.sqrt h) =
              (Real.sqrt h) ^ 2 * candidateComparisonEndpoint sf ω (t i) T h j *
                candidateComparisonEndpoint sf ω (t k) T h j by ring, Real.sq_sqrt hh]
    _ = _ := Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
      h * candidateComparisonEndpoint sf ω (t i) T h j *
        candidateComparisonEndpoint sf ω (t k) T h j) n

/-- Exact squared Hilbert error of replacing each actual prime coefficient
by the right-endpoint coefficient in its bin. -/
theorem candidate_comparison_prime_error_eq (sf : Bool) (ω : Omega) (t T h : ℝ) (n : ℕ) :
    (∫ q, (candidateComparisonPrime sf ω t T h n q -
      candidateComparisonPrimeStep sf ω t T h n q) ^ 2 ∂Measure.count) =
        candidateComparisonPrimeEnergy sf ω t T h n := by
  rw [integral_count]
  change (∑ q : Sigma (fun j : Fin n ↦ ↥(candidateLogPrimeBin (T + (j : ℝ) * h) h)), _) = _
  rw [Fintype.sum_sigma]
  simp only [candidateComparisonPrime, candidateComparisonPrimeStep,
    ← sub_mul, mul_pow]
  have hw (j : Fin n) (p : ↥(candidateLogPrimeBin (T + (j : ℝ) * h) h)) :
      (Real.sqrt (Real.log (p.val : ℝ) / p.val)) ^ 2 = Real.log (p.val : ℝ) / p.val :=
    Real.sq_sqrt (candidate_logPrimeBin_weight_nonneg p.property)
  simp_rw [hw]
  let F (j p : ℕ) := (Real.log (p : ℝ) / p) *
    (candidateComparisonProcess sf ω (t - Real.log (p : ℝ)) / Real.sqrt (Real.log (p : ℝ)) -
      candidateComparisonEndpoint sf ω t T h j) ^ 2
  have he : (∑ j : Fin n, ∑ p : ↥(candidateLogPrimeBin (T + (j : ℝ) * h) h),
      F j p.val) = ∑ j ∈ Finset.range n,
        ∑ p ∈ candidateLogPrimeBin (T + (j : ℝ) * h) h, F j p := by
    simp_rw [Finset.sum_coe_sort _ (F _)]
    exact Fin.sum_univ_eq_sum_range
      (fun j : ℕ ↦ ∑ p ∈ candidateLogPrimeBin (T + (j : ℝ) * h) h, F j p) n
  calc
    _ = ∑ j : Fin n, ∑ p : ↥(candidateLogPrimeBin (T + (j : ℝ) * h) h), F j p.val := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro p _
      exact mul_comm _ _
    _ = _ := he
    _ = _ := by cases sf <;> rfl

end Erdos.Problem1144
