import Erdos.Problem1144.HarperCandidatePrimeWhiteComparisonCrossing

open MeasureTheory ProbabilityTheory Set Matrix WithLp
open scoped BigOperators

namespace Erdos.Problem1144

/-- Summing the disjoint dependent prime family is exactly summing all primes
between the two exponential cutoffs, once each. -/
theorem candidate_sum_primeWhiteIndex {T h : ℝ} (hh : 0 ≤ h) (n : ℕ) (F : ℕ → ℝ) :
    (∑ q : candidatePrimeWhiteIndex T h n, F q.2.val) =
      ∑ p ∈ (Finset.Ioc ⌊Real.exp T⌋₊ ⌊Real.exp (T + (n : ℝ) * h)⌋₊).filter Nat.Prime,
        F p := by
  change (∑ q : Sigma (fun j : Fin n ↦ ↥(candidateLogPrimeBin (T + (j : ℝ) * h) h)), _) = _
  rw [Fintype.sum_sigma]
  simp_rw [Finset.sum_coe_sort _ F]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
    ∑ p ∈ candidateLogPrimeBin (T + (j : ℝ) * h) h, F p) n]
  rw [← candidateLogPrimeBin_union hh n]
  symm
  apply Finset.sum_biUnion
  intro j _ k _ hjk
  exact candidateLogPrimeBin_disjoint hh hjk

/-- The actual prime covariance matrix is the full finite prime sum, with
literal normalized complete or squarefree coefficients. Extra endpoint
primes contribute zero by the zero extension of the process. -/
theorem candidate_comparison_prime_covariance_eq {ι : Type*} (sf : Bool) (ω : Omega)
    (t : ι → ℝ) (T : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    candidateWeightedGram Measure.count (fun i ↦ candidateComparisonPrime sf ω (t i) T h n)
      (fun _ ↦ 1) = fun i k ↦
      ∑ p ∈ (Finset.Ioc ⌊Real.exp T⌋₊ ⌊Real.exp (T + (n : ℝ) * h)⌋₊).filter Nat.Prime,
        (candidateComparisonProcess sf ω (t i - Real.log (p : ℝ)) / Real.sqrt p) *
        (candidateComparisonProcess sf ω (t k - Real.log (p : ℝ)) / Real.sqrt p) := by
  ext i k
  simp only [candidateWeightedGram, one_mul, integral_count, candidateComparisonPrime_eq]
  exact candidate_sum_primeWhiteIndex hh n (fun p : ℕ ↦
    (candidateComparisonProcess sf ω (t i - Real.log (p : ℝ)) / Real.sqrt p) *
    (candidateComparisonProcess sf ω (t k - Real.log (p : ℝ)) / Real.sqrt p))

/-- The actual independent-prime normal linear combination has exactly the
Gram law used in the selected-crossing comparison. No law-identification
hypothesis or nonsingularity requirement is imposed. -/
theorem candidate_measurePreserving_comparison_prime_linear
    {ι : Type*} [Fintype ι] [DecidableEq ι] (sf : Bool) (ω : Omega)
    (t : ι → ℝ) (T h : ℝ) (n : ℕ) :
    MeasurePreserving (fun g : candidatePrimeWhiteIndex T h n → ℝ ↦
      toLp 2 (fun i ↦ ∑ q,
        (candidateComparisonProcess sf ω (t i - Real.log (q.2.val : ℝ)) /
          Real.sqrt q.2.val) * g q))
      (Measure.pi (fun _ : candidatePrimeWhiteIndex T h n ↦ gaussianReal 0 1))
      (multivariateGaussian (0 : EuclideanSpace ℝ ι)
        (candidateWeightedGram Measure.count
          (fun i ↦ candidateComparisonPrime sf ω (t i) T h n) (fun _ ↦ 1))) := by
  rw [candidate_finite_gram_eq_mul_conjTranspose]
  have h := candidate_measurePreserving_pi_gaussian_linear
    (fun i ↦ candidateComparisonPrime sf ω (t i) T h n)
  simpa only [candidateComparisonPrime_eq] using h

theorem candidateComparisonProcess_zero_of_neg (sf : Bool) (ω : Omega) {t : ℝ} (ht : t < 0) :
    candidateComparisonProcess sf ω t = 0 := by
  cases sf <;> simp [candidateComparisonProcess, harperCandidateLogProcess,
    harperCandidateSquarefreeLogProcess, not_le.mpr ht]

/-- Whole bins may extend beyond a coordinate's endpoint: every such prime
has exactly zero coefficient, so there is no omitted partial-bin correction. -/
theorem candidateComparisonPrime_eq_zero_of_endpoint (sf : Bool) (ω : Omega)
    (t T h : ℝ) (n : ℕ) (q : candidatePrimeWhiteIndex T h n)
    (hq : ⌊Real.exp t⌋₊ < q.2.val) : candidateComparisonPrime sf ω t T h n q = 0 := by
  rw [candidateComparisonPrime_eq]
  have hp := (Finset.mem_filter.mp q.2.property).2
  have he : Real.exp t < (q.2.val : ℝ) :=
    (Nat.floor_lt (Real.exp_pos t).le).mp hq
  have hl : t < Real.log (q.2.val : ℝ) :=
    (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr hp.pos)).mpr he
  rw [candidateComparisonProcess_zero_of_neg sf ω (sub_neg.mpr hl), zero_div]

/-- The prime crossing probability appearing in the comparison is literally
the selected crossing of the independent standard-normal prime sum. -/
theorem candidate_comparison_prime_crossing_eq_pi
    {ι : Type*} [Fintype ι] [DecidableEq ι] (sf : Bool) (t : ι → ℝ)
    (T h : ℝ) (n : ℕ) (J : Omega → Finset ι) (K : ℝ) (ω : Omega) :
    candidateComparisonPrimeCrossing sf t T h n J K ω =
      (Measure.pi (fun _ : candidatePrimeWhiteIndex T h n ↦ gaussianReal 0 1)).real
        {g | ∃ i ∈ J ω, K < |∑ q : candidatePrimeWhiteIndex T h n,
          (candidateComparisonProcess sf ω (t i - Real.log (q.2.val : ℝ)) /
            Real.sqrt q.2.val) * g q|} := by
  have hs : MeasurableSet {x : EuclideanSpace ℝ ι | ∃ i ∈ J ω, K < |x i|} := by
    simp only [setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    by_cases hi : i ∈ J ω
    · simpa only [hi, true_and] using
        (measurableSet_lt (measurable_const : Measurable (fun _ : EuclideanSpace ℝ ι ↦ K))
          (show Measurable (fun x : EuclideanSpace ℝ ι ↦ |x i|) by fun_prop))
    · simp only [hi, false_and, setOf_false, MeasurableSet.empty]
  exact ((candidate_measurePreserving_comparison_prime_linear sf ω t T h n).measureReal_preimage
    hs.nullMeasurableSet).symm

end Erdos.Problem1144
