import Erdos.Problem1144.HarperCandidatePrimeWhiteComparisonErrors

open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators

namespace Erdos.Problem1144

noncomputable def candidateComparisonPrimeCrossing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sf : Bool) (t : ι → ℝ) (T h : ℝ) (n : ℕ) (J : Omega → Finset ι) (K : ℝ)
    (ω : Omega) : ℝ :=
  (multivariateGaussian (0 : EuclideanSpace ℝ ι)
    (candidateWeightedGram Measure.count (fun i ↦ candidateComparisonPrime sf ω (t i) T h n)
      (fun _ ↦ 1))).real {x | ∃ i ∈ J ω, K < |x i|}

noncomputable def candidateComparisonWhiteCrossing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sf : Bool) (t : ι → ℝ) (T : ℝ) (J : Omega → Finset ι) (K : ℝ) (ω : Omega) : ℝ :=
  (multivariateGaussian (0 : EuclideanSpace ℝ ι)
    (candidateWeightedGram volume (fun i ↦ candidateComparisonWhite sf ω (t i) T)
      (fun _ ↦ 1))).real {x | ∃ i ∈ J ω, K < |x i|}

noncomputable def candidateComparisonTotalError {ι : Type*} [Fintype ι]
    (sf : Bool) (t : ι → ℝ) (T h : ℝ) (n : ℕ) (ω : Omega) : ℝ :=
  ∑ i, (candidateComparisonPrimeEnergy sf ω (t i) T h n +
    candidateComparisonMassError sf ω (t i) T h n +
    candidateComparisonWhiteError sf ω (t i) T h n)

/-- Three literal Gaussian couplings, averaged under an arbitrary fixed
cylinder and for an arbitrary measurable retained set. The only loss is the
actual prime, bin-normalization and white-kernel squared error budget. -/
theorem candidate_prime_white_selected_crossing_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] (sf : Bool)
    (s : Finset ℕ) (η : s → Bool) (t : ι → ℝ) {T h : ℝ} {n : ℕ}
    (hT : 0 < T) (hh : 0 ≤ h) (hcover : ∀ i, t i ≤ T + (n : ℝ) * h)
    (J : Omega → Finset ι) (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω})
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, candidateComparisonWhiteCrossing sf t T J (K + 3 * ε) ω
      ∂candidateCylinderLaw s η) ≤
    (∫ ω, candidateComparisonPrimeCrossing sf t T h n J K ω
      ∂candidateCylinderLaw s η) +
    (∫ ω, candidateComparisonTotalError sf t T h n ω ∂mu) /
      (mu.real (candidateCylinder s η) * ε ^ 2) := by
  let Q := candidateCylinderLaw s η
  let P := fun ω ↦ ∑ i, candidateComparisonPrimeEnergy sf ω (t i) T h n
  let M := fun ω ↦ ∑ i, candidateComparisonMassError sf ω (t i) T h n
  let W := fun ω ↦ ∑ i, candidateComparisonWhiteError sf ω (t i) T h n
  have hP : Integrable P mu := integrable_finset_sum _ fun i _ ↦
    candidate_integrable_comparisonPrimeEnergy sf (t i) T h n
  have hM : Integrable M mu := integrable_finset_sum _ fun i _ ↦
    candidate_integrable_comparisonMassError sf (t i) T h n
  have hW : Integrable W mu := integrable_finset_sum _ fun i _ ↦
    candidate_integrable_comparisonWhiteError sf hT hh (hcover i)
  have hcP := candidateCylinderLaw_integral_nonneg_le s η hP
    (fun ω ↦ Finset.sum_nonneg fun i _ ↦ candidate_comparisonPrimeEnergy_nonneg sf ω (t i) T h n)
  have hcM := candidateCylinderLaw_integral_nonneg_le s η hM
    (fun ω ↦ Finset.sum_nonneg fun i _ ↦ candidate_comparisonMassError_nonneg sf ω (t i) T h n)
  have hcW := candidateCylinderLaw_integral_nonneg_le s η hW
    (fun ω ↦ Finset.sum_nonneg fun i _ ↦ candidate_comparisonWhiteError_nonneg sf ω (t i) T h n)
  have h1 := candidate_integral_gaussian_gram_selected_crossing_le Q Measure.count
    (fun i ω ↦ candidateComparisonPrime sf ω (t i) T h n)
    (fun i ω ↦ candidateComparisonPrimeStep sf ω (t i) T h n)
    (fun i ↦ measurable_candidateComparisonPrime sf (t i) T h n)
    (fun i ↦ measurable_candidateComparisonPrimeStep sf (t i) T h n)
    (fun _ _ ↦ candidate_memLp_finite_count _) (fun _ _ ↦ candidate_memLp_finite_count _)
    J hJ (by simpa only [candidate_comparison_prime_error_eq] using hcP.1) K hε
  have h2 := candidate_integral_gaussian_gram_selected_crossing_le Q Measure.count
    (fun i ω ↦ candidateComparisonMassBin sf ω (t i) T h n)
    (fun i ω ↦ candidateComparisonWhiteBin sf ω (t i) T h n)
    (fun i ↦ measurable_candidateComparisonMassBin sf (t i) T h n)
    (fun i ↦ measurable_candidateComparisonWhiteBin sf (t i) T h n)
    (fun _ _ ↦ candidate_memLp_finite_count _) (fun _ _ ↦ candidate_memLp_finite_count _)
    J hJ (by simpa only [candidate_comparison_mass_error_eq] using hcM.1) (K + ε) hε
  have h3 := candidate_integral_gaussian_gram_selected_crossing_le Q volume
    (fun i ω ↦ candidateComparisonWhiteStep sf ω (t i) T h n)
    (fun i ω ↦ candidateComparisonWhite sf ω (t i) T)
    (fun i ↦ measurable_candidateComparisonWhiteStep sf (t i) T h n)
    (fun i ↦ measurable_candidateComparisonWhite sf (t i) T)
    (fun ω i ↦ candidate_memLp_comparisonWhiteStep sf ω (t i) T hh n)
    (fun ω i ↦ candidate_memLp_comparisonWhite sf ω (t i) hT)
    J hJ hcW.1 (K + ε + ε) hε
  simp_rw [candidate_comparison_primeStep_gram_eq, candidate_comparison_prime_error_eq] at h1
  simp_rw [candidate_comparison_whiteBin_gram_eq sf _ t T hh n,
    candidate_comparison_mass_error_eq] at h2
  have hsum : (∫ ω, candidateComparisonTotalError sf t T h n ω ∂mu) =
      (∫ ω, P ω ∂mu) + (∫ ω, M ω ∂mu) + (∫ ω, W ω ∂mu) := by
    simp only [candidateComparisonTotalError, Finset.sum_add_distrib]
    change (∫ ω, (P + M) ω + W ω ∂mu) = _
    rw [integral_add (hP.add hM) hW]
    simp only [Pi.add_apply]
    rw [integral_add hP hM]
  have herr : (∫ ω, P ω ∂Q) / ε ^ 2 + (∫ ω, M ω ∂Q) / ε ^ 2 +
      (∫ ω, W ω ∂Q) / ε ^ 2 ≤
        (∫ ω, candidateComparisonTotalError sf t T h n ω ∂mu) /
          (mu.real (candidateCylinder s η) * ε ^ 2) := by
    rw [hsum]
    have hp := div_le_div_of_nonneg_right hcP.2 (sq_nonneg ε)
    have hm := div_le_div_of_nonneg_right hcM.2 (sq_nonneg ε)
    have hw := div_le_div_of_nonneg_right hcW.2 (sq_nonneg ε)
    simpa only [div_div, ← add_div] using add_le_add (add_le_add hp hm) hw
  have hlevel : K + ε + ε + ε = K + 3 * ε := by ring
  rw [hlevel] at h3
  change (∫ ω, candidateComparisonWhiteCrossing sf t T J (K + 3 * ε) ω ∂Q) ≤ _ at h3
  change _ ≤ (∫ ω, candidateComparisonPrimeCrossing sf t T h n J K ω ∂Q) +
    (∫ ω, P ω ∂Q) / ε ^ 2 at h1
  change _ ≤ _ + (∫ ω, M ω ∂Q) / ε ^ 2 at h2
  change _ ≤ _ + (∫ ω, W ω ∂Q) / ε ^ 2 at h3
  linarith

end Erdos.Problem1144
