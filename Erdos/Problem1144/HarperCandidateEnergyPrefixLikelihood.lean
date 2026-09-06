import Erdos.Problem1144.HarperCandidateEnergyPrefixPinch

open Finset MeasureTheory ProbabilityTheory Set
open Erdos.Problem520
open scoped BigOperators

namespace Erdos.Problem1144

/-- Exact two-height correlation on a subset of shifted Euler coordinates. -/
noncomputable def candidateRankinSubsetCorrelation
    (y : ℕ) (P : Finset (HarperPrimeIndex y)) (a t s : ℝ) : ℝ :=
  ∏ p ∈ P, harperRankinTwoHeightPrimeCorrelation p.1 a t s

theorem candidate_rankinSubsetCorrelation_pos
    (y : ℕ) (P : Finset (HarperPrimeIndex y)) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    0 < candidateRankinSubsetCorrelation y P a t s := by
  exact Finset.prod_pos fun p hp => harperRankinTwoHeightPrimeCorrelation_pos
    (Nat.prime_of_mem_primesBelow p.property) ha t s

private theorem candidate_integral_normalizedRankinCoordinate
    (p : ℕ) (a t s : ℝ) :
    (∫ b, harperRankinCoordinateFactor p a s b / harperRankinEulerNormalizer p a
      ∂harperRankinTiltedCoin p a t) = harperRankinTwoHeightPrimeCorrelation p a t s := by
  rw [integral_harperRankinTiltedCoin]
  unfold harperRankinTwoHeightPrimeCorrelation
  rw [harperRankinTwoHeightPrimeNormalizer_eq]
  unfold harperRankinTiltedCoinWeight
  ring

/-- Independent coordinates average the unobserved likelihood exactly. -/
theorem candidate_integral_rankinSubsetNormalizedDensity
    (y : ℕ) (P : Finset (HarperPrimeIndex y)) (a t s : ℝ) :
    (∫ eta, candidateRankinSubsetNormalizedDensity y P a s eta
      ∂harperRankinTiltedCubeLaw y a t) = candidateRankinSubsetCorrelation y P a t s := by
  classical
  let g : HarperPrimeIndex y → Bool → ℝ := fun p b =>
    if p ∈ P then harperRankinCoordinateFactor p.1 a s b / harperRankinEulerNormalizer p.1 a else 1
  have hfactor := integral_prod_harperRankinTiltedCubeLaw y a t g
  have hleft : (fun eta => ∏ p : HarperPrimeIndex y, g p (eta p)) =
      candidateRankinSubsetNormalizedDensity y P a s := by
    funext eta
    simp only [g, Finset.prod_ite_mem, Finset.univ_inter]
    rfl
  have hright : (∏ p : HarperPrimeIndex y, ∫ b, g p b ∂harperRankinTiltedCoin p.1 a t) =
      candidateRankinSubsetCorrelation y P a t s := by
    change _ = ∏ p ∈ P, harperRankinTwoHeightPrimeCorrelation p.1 a t s
    rw [← Fintype.prod_ite_mem P]
    apply Finset.prod_congr rfl
    intro p hp
    by_cases hpP : p ∈ P
    · simp only [g, if_pos hpP]
      exact candidate_integral_normalizedRankinCoordinate p.1 a t s
    · simp only [g, if_neg hpP, integral_const, probReal_univ, one_smul]
  rw [hleft, hright] at hfactor
  exact hfactor

private theorem candidate_rankinCorrelation_mul_singleton
    (y : ℕ) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) (eta : HarperPrimeCube y) :
    harperRankinTwoHeightCorrelation y a t s *
      (harperRankinTwoHeightCubeLaw y a ha t s).real {eta} =
      candidateRankinSubsetNormalizedDensity y Finset.univ a s eta *
        (harperRankinTiltedCubeLaw y a t).real {eta} := by
  rw [harperRankinTwoHeightCubeLaw_real_singleton,
    harperRankinTiltedCubeLaw_real_singleton]
  unfold harperRankinTwoHeightCorrelation candidateRankinSubsetNormalizedDensity
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  unfold harperRankinTwoHeightPrimeCorrelation harperRankinTwoHeightCoinWeight
    harperRankinTiltedCoinWeight
  field_simp [(harperRankinTwoHeightPrimeNormalizer_pos
    (Nat.prime_of_mem_primesBelow p.property) ha t s).ne',
    (harperRankinEulerNormalizer_pos p.1 a).ne']

/-- Sharp shifted likelihood cancellation on any finite-cube event. -/
theorem candidate_rankinTwoHeightCorrelation_mul_probability_eq_oneHeight_restrict
    (y : ℕ) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) (A : Set (HarperPrimeCube y)) :
    harperRankinTwoHeightCorrelation y a t s *
      (harperRankinTwoHeightCubeLaw y a ha t s).real A =
      ∫ eta in A, candidateRankinSubsetNormalizedDensity y Finset.univ a s eta
        ∂harperRankinTiltedCubeLaw y a t := by
  classical
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  rw [← integral_indicator_one (μ := harperRankinTwoHeightCubeLaw y a ha t s) hA,
    ← integral_indicator hA, integral_fintype Integrable.of_finite,
    integral_fintype Integrable.of_finite, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta heta
  by_cases hmem : eta ∈ A
  · simp only [Set.indicator_of_mem hmem, Pi.one_apply, smul_eq_mul, mul_one]
    rw [candidate_rankinCorrelation_mul_singleton]
    ring
  · simp [hmem]

/-- Capping the literal prefix likelihood removes it; every remaining
coordinate contributes exactly its complementary shifted correlation. -/
theorem candidate_rankinTwoHeightCorrelation_mul_probability_le_of_prefixCap
    (y : ℕ) (P : Finset (HarperPrimeIndex y)) {a : ℝ} (ha : 0 ≤ a)
    (t s M : ℝ) (A : Set (HarperPrimeCube y)) (hM : 0 ≤ M)
    (hcap : ∀ eta ∈ A, candidateRankinSubsetNormalizedDensity y P a s eta ≤ M) :
    harperRankinTwoHeightCorrelation y a t s *
      (harperRankinTwoHeightCubeLaw y a ha t s).real A ≤
      M * candidateRankinSubsetCorrelation y Pᶜ a t s := by
  classical
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  rw [candidate_rankinTwoHeightCorrelation_mul_probability_eq_oneHeight_restrict,
    ← integral_indicator hA]
  have hsplit (eta : HarperPrimeCube y) :
      candidateRankinSubsetNormalizedDensity y Finset.univ a s eta =
      candidateRankinSubsetNormalizedDensity y P a s eta *
        candidateRankinSubsetNormalizedDensity y Pᶜ a s eta := by
    exact (Finset.prod_mul_prod_compl P _).symm
  calc
    _ ≤ ∫ eta, M * candidateRankinSubsetNormalizedDensity y Pᶜ a s eta
      ∂harperRankinTiltedCubeLaw y a t := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro eta
      have hnonneg := (candidate_rankinSubsetNormalizedDensity_pos y Pᶜ ha s eta).le
      by_cases hmem : eta ∈ A
      · rw [Set.indicator_of_mem hmem, hsplit]
        exact mul_le_mul_of_nonneg_right (hcap eta hmem) hnonneg
      · rw [Set.indicator_of_notMem hmem]
        exact mul_nonneg hM hnonneg
    _ = _ := by rw [integral_const_mul, candidate_integral_rankinSubsetNormalizedDensity]

/-- The sharp same-graph prefix cancellation is uniform in the Rankin shift. -/
theorem candidate_exists_rankinLogBallot_correlation_probability_le_prefix_compl :
    ∃ B > 0, ∃ J : ℕ, ∀ start n y : ℕ, J + 1 ≤ start →
      harperBlockEndpoint (start + n) ≤ y → ∀ a : ℝ, ∀ ha : 0 ≤ a,
        ∀ s ∈ harperLowerVerticalBand, ∀ t : ℝ, ∀ k : Fin n,
          harperRankinTwoHeightCorrelation y a t s *
            (harperRankinTwoHeightCubeLaw y a ha t s).real
              (harperRankinLogBallotCubeEvent y start n a s) ≤
            (B * (2 : ℝ) ^ (k.val + 1) / (((k.val + 1 : ℕ) : ℝ) ^ 4)) *
              candidateRankinSubsetCorrelation y
                (harperScheduledPrimeRangeFrom y start (k.val + 1))ᶜ a t s := by
  obtain ⟨B, hB, J, hcap⟩ := candidate_exists_rankinLogBallot_prefixDensity_le_powTwo_div_fourth
  refine ⟨B, hB, J, ?_⟩
  intro start n y hstart hy a ha s hs t k
  apply candidate_rankinTwoHeightCorrelation_mul_probability_le_of_prefixCap
    y _ ha t s _ _ (by positivity)
  intro eta heta
  exact hcap start n y hstart hy a ha s hs eta heta k

end Erdos.Problem1144
