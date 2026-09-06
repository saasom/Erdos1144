import Erdos.Problem1144.HarperCandidatePrimeWhiteComparisonCrossing

open MeasureTheory ProbabilityTheory

namespace Erdos.Problem1144

/-- Both actual white crossing probabilities are integrable under any
external probability law, for every measurable random selector. -/
theorem candidate_integrable_comparisonWhiteCrossing
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (sf : Bool) (u : ι → ℝ)
    {T : ℝ} (hT : 0 < T) (J : Omega → Finset ι)
    (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω}) (K : ℝ) :
    Integrable (candidateComparisonWhiteCrossing sf u T J K) Q := by
  exact candidate_integrable_gaussian_selected_probability Q
    (candidate_measurable_random_gram volume
      (fun i ω => candidateComparisonWhite sf ω (u i) T)
      (fun i => measurable_candidateComparisonWhite sf (u i) T))
    (fun ω => candidateWeightedGram_posSemidef volume
      (fun i => candidateComparisonWhite sf ω (u i) T) (fun _ => 1)
      (fun i j => by
        have hi := candidate_memLp_comparisonWhite sf ω (u i) hT
        have hj := candidate_memLp_comparisonWhite sf ω (u j) hT
        simpa only [one_mul] using hi.integrable_mul hj)
      (ae_of_all _ fun _ => Or.inl zero_le_one)) J hJ K

/-- Increasing the threshold decreases the actual averaged selected white
crossing, including singular covariance laws and random selectors. -/
theorem candidate_integral_comparisonWhiteCrossing_antitone
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Measure Omega) [IsProbabilityMeasure Q] (sf : Bool) (u : ι → ℝ)
    {T : ℝ} (hT : 0 < T) (J : Omega → Finset ι)
    (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω}) {K L : ℝ} (hKL : K ≤ L) :
    (∫ ω, candidateComparisonWhiteCrossing sf u T J L ω ∂Q) ≤
      ∫ ω, candidateComparisonWhiteCrossing sf u T J K ω ∂Q := by
  apply integral_mono (candidate_integrable_comparisonWhiteCrossing Q sf u hT J hJ L)
    (candidate_integrable_comparisonWhiteCrossing Q sf u hT J hJ K)
  intro ω
  exact measureReal_mono fun _ ⟨i, hi, hx⟩ => ⟨i, hi, hKL.trans_lt hx⟩

end Erdos.Problem1144
