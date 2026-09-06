import Erdos.Problem1144.HarperCandidateEnergyPrefixTaylor
import Erdos.Problem1144.HarperCandidateEnergyTwoHeightScheduled
import Erdos.Problem1144.HarperRankinBlockIndependence

open Finset MeasureTheory ProbabilityTheory Set
open Erdos.Problem520
open scoped BigOperators

namespace Erdos.Problem1144

/-- Actual normalized shifted Euler likelihood on a set of prime coordinates. -/
noncomputable def candidateRankinSubsetNormalizedDensity
    (y : ℕ) (P : Finset (HarperPrimeIndex y)) (a t : ℝ) (eta : HarperPrimeCube y) : ℝ :=
  ∏ p ∈ P, harperRankinCoordinateFactor p.1 a t (eta p) /
    harperRankinEulerNormalizer p.1 a

theorem candidate_rankinSubsetNormalizedDensity_pos
    (y : ℕ) (P : Finset (HarperPrimeIndex y)) {a : ℝ} (ha : 0 ≤ a)
    (t : ℝ) (eta : HarperPrimeCube y) :
    0 < candidateRankinSubsetNormalizedDensity y P a t eta := by
  apply Finset.prod_pos
  intro p hp
  exact div_pos (harperRankinCoordinateFactor_pos
    (Nat.prime_of_mem_primesBelow p.property) ha t (eta p))
    (harperRankinEulerNormalizer_pos p.1 a)

/-- The same shifted ballot graph imposes its pinch on the literal prime prefix. -/
theorem candidate_rankinCenteredRangeFrom_le_forwardLog
    (y start n : ℕ) (a t : ℝ) (eta : HarperPrimeCube y)
    (heta : eta ∈ harperRankinLogBallotCubeEvent y start n a t) (k : Fin n) :
    harperRankinCenteredLinearPrimeBlockSum y
      (harperScheduledPrimeRangeFrom y start (k.val + 1)) a t t eta ≤
      1 - 2 * Real.log ((k.val + 1 : ℕ) : ℝ) := by
  have hsum : harperRankinCenteredLinearPrimeBlockSum y
      (harperScheduledPrimeRangeFrom y start (k.val + 1)) a t t eta =
      harperPathPartialSum (harperRankinScheduledCenteredBlockVector y start n a t eta) k := by
    unfold harperRankinCenteredLinearPrimeBlockSum harperScheduledPrimeRangeFrom
    rw [Finset.sum_biUnion (pairwiseDisjoint_harperScheduledPrimeBlock_add y start _)]
    rw [harperPathPartialSum_eq_sum_prefix]
    change (∑ x ∈ Finset.range (k.val + 1),
      harperRankinCenteredLinearPrimeBlockSum y
        (harperScheduledPrimeBlock y (start + x)) a t t eta) =
      ∑ i : Fin (k.val + 1), harperRankinCenteredLinearPrimeBlockSum y
        (harperScheduledPrimeBlock y (start + i.val)) a t t eta
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  rw [hsum]
  exact (mem_harperPartialSumBarrierSet.mp heta k).2

private theorem candidate_rankinPrefix_oscillation_bound :
    ∃ K ≥ 0, ∃ J : ℕ, ∀ start n y : ℕ, J + 1 ≤ start →
      harperBlockEndpoint (start + n) ≤ y → ∀ a : ℝ, 0 ≤ a →
        ∀ t ∈ harperLowerVerticalBand,
          |∑ p ∈ harperScheduledPrimeRangeFrom y start n,
            harperRankinEulerRadius p.1 a ^ 2 *
              Real.cos (2 * t * Real.log (p.1 : ℝ))| ≤ K := by
  obtain ⟨c, hc, C, hC, J, hosc⟩ := candidate_exists_rankinScheduledDyadicOscillationBounds
  let E := harperScheduledDyadicOscillationEnvelope 1 c C
  have hE : Summable E := summable_harperScheduledDyadicOscillationEnvelope 1 hc hC.le
  have hE0 : ∀ j, 0 ≤ E j := fun j =>
    harperScheduledDyadicOscillationEnvelope_nonneg 1 hC.le j
  refine ⟨∑' j, E j, tsum_nonneg hE0, J, ?_⟩
  intro start n y hstart hy a ha t ht
  have hsum : (∑ p ∈ harperScheduledPrimeRangeFrom y start n,
      harperRankinEulerRadius p.1 a ^ 2 * Real.cos (2 * t * Real.log (p.1 : ℝ))) =
      ∑ j ∈ Finset.range n, candidateRankinScheduledOscillation y (start + j) a (2 * t) := by
    unfold harperScheduledPrimeRangeFrom
    rw [Finset.sum_biUnion (pairwiseDisjoint_harperScheduledPrimeBlock_add y start n)]
    apply Finset.sum_congr rfl
    intro j hj
    unfold candidateRankinScheduledOscillation
    apply Finset.sum_congr rfl
    intro p hp
    rw [harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg
      (Nat.prime_of_mem_primesBelow p.property).pos]
    ring
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ Finset.range n, |candidateRankinScheduledOscillation y (start + j) a (2 * t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, E (start + j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn := Finset.mem_range.mp hj
      apply hosc 1 (start + j) y (by omega)
        ((monotone_harperBlockEndpoint (by omega)).trans hy) a ha t t
      · rw [abs_of_nonneg (show 0 ≤ t by linarith [ht.1])]
        norm_num
        linarith [ht.1]
      · rw [abs_of_nonneg (show 0 ≤ t by linarith [ht.1])]
        linarith [ht.2]
      · simp
    _ = ∑ j ∈ (Finset.range n).image (fun j => start + j), E j := by
      rw [Finset.sum_image]
      intro i hi j hj h
      exact Nat.add_left_cancel h
    _ ≤ ∑' j, E j := hE.sum_le_tsum _ (fun j hj => hE0 j)


private theorem candidate_rankinPrefix_log_upper
    (y start m : ℕ) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) (eta : HarperPrimeCube y) :
    Real.log (candidateRankinSubsetNormalizedDensity y
      (harperScheduledPrimeRangeFrom y start m) a t eta) ≤
      2 * harperRankinCenteredLinearPrimeBlockSum y
        (harperScheduledPrimeRangeFrom y start m) a t t eta +
      (∑ p ∈ harperScheduledPrimeRangeFrom y start m, (p.1 : ℝ)⁻¹) +
      (∑ p ∈ harperScheduledPrimeRangeFrom y start m,
        harperRankinEulerRadius p.1 a ^ 2 * Real.cos (2 * t * Real.log (p.1 : ℝ))) +
      1 + 8 / 3 := by
  let P := harperScheduledPrimeRangeFrom y start m
  have hrad (p : HarperPrimeIndex y) : harperRankinEulerRadius p.1 a ^ 2 ≤ (p.1 : ℝ)⁻¹ := by
    have h := pow_le_pow_left₀ (harperRankinEulerRadius_nonneg p.1 a)
      (harperRankinEulerRadius_le_inv_sqrt
        (Nat.prime_of_mem_primesBelow p.property).one_le ha) 2
    simpa [inv_pow, Real.sq_sqrt (Nat.cast_nonneg p.1)] using h
  have hfour : (∑ p ∈ P, harperRankinEulerRadius p.1 a ^ 4) ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ P, (p.1 : ℝ)⁻¹ ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        simpa only [← pow_mul, Nat.reduceMul] using pow_le_pow_left₀ (sq_nonneg _) (hrad p) 2
      _ ≤ harperPrimeSquareBudget y := Finset.sum_le_sum_of_subset_of_nonneg
        P.subset_univ (fun p hp hnp => by positivity)
      _ ≤ 1 := harperPrimeSquareBudget_le_one y
  have hcubic : (∑ p ∈ P, (4 / 3 : ℝ) * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3) ≤ 8 / 3 := by
    calc
      _ = 2 * harperBlockCubicRemainder y P := by
        unfold harperBlockCubicRemainder
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ 2 * ((4 / 3 : ℝ) * (Real.sqrt (harperBlockEndpoint start : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left (harperBlockCubicRemainder_rangeFrom_le y start m) (by norm_num)
      _ ≤ 8 / 3 := by
        have h := harperScheduledLogTaylorAllowance_le_four_thirds start
        change (4 / 3 : ℝ) * (Real.sqrt (harperBlockEndpoint start : ℝ))⁻¹ ≤ 4 / 3 at h
        linarith
  have hlog : Real.log (candidateRankinSubsetNormalizedDensity y P a t eta) ≤
      ∑ p ∈ P, (2 * harperRankinCenteredLinearPrimeIncrement p.1 a t t (eta p) +
        harperRankinEulerRadius p.1 a ^ 2 +
        harperRankinEulerRadius p.1 a ^ 2 * Real.cos (2 * t * Real.log (p.1 : ℝ)) +
        harperRankinEulerRadius p.1 a ^ 4 +
        (4 / 3 : ℝ) * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3) := by
    unfold candidateRankinSubsetNormalizedDensity
    rw [Real.log_prod (fun p hp => (div_pos
      (harperRankinCoordinateFactor_pos (Nat.prime_of_mem_primesBelow p.property) ha t (eta p))
      (harperRankinEulerNormalizer_pos p.1 a)).ne')]
    apply Finset.sum_le_sum
    intro p hp
    apply candidate_rankin_log_normalized_factor_le
      (Nat.prime_of_mem_primesBelow p.property) _ ha
    have hmem := (mem_harperScheduledPrimeRangeFrom p).mp hp
    have := harperBlockEndpoint_ge_sixteen start
    omega
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hlog
  rw [← Finset.mul_sum] at hcubic
  have hradSum := Finset.sum_le_sum (s := P) (fun p hp => hrad p)
  change _ ≤ 2 * (∑ p ∈ P, harperRankinCenteredLinearPrimeIncrement p.1 a t t (eta p)) +
    (∑ p ∈ P, (p.1 : ℝ)⁻¹) +
    (∑ p ∈ P, harperRankinEulerRadius p.1 a ^ 2 * Real.cos (2 * t * Real.log (p.1 : ℝ))) + 1 + 8 / 3
  linarith

/-- Uniform in every nonnegative shift: the same Rankin ballot graph caps
its prefix likelihood by the sharp fourth-power pinch. -/
theorem candidate_exists_rankinLogBallot_prefixDensity_le_powTwo_div_fourth :
    ∃ B > 0, ∃ J : ℕ, ∀ start n y : ℕ, J + 1 ≤ start →
      harperBlockEndpoint (start + n) ≤ y → ∀ a : ℝ, 0 ≤ a →
        ∀ t ∈ harperLowerVerticalBand, ∀ eta ∈ harperRankinLogBallotCubeEvent y start n a t,
          ∀ k : Fin n, candidateRankinSubsetNormalizedDensity y
            (harperScheduledPrimeRangeFrom y start (k.val + 1)) a t eta ≤
              B * (2 : ℝ) ^ (k.val + 1) / (((k.val + 1 : ℕ) : ℝ) ^ 4) := by
  obtain ⟨K, hK, Jo, ho⟩ := candidate_rankinPrefix_oscillation_bound
  obtain ⟨L, hL, Jr, hr⟩ := exists_harperScheduledCentralBandVerticalCumulativeDrift_constant_bound
  let C := 2 + L + K + 1 + 8 / 3
  refine ⟨Real.exp C, Real.exp_pos C, max Jo Jr, ?_⟩
  intro start n y hstart hy a ha t ht eta heta k
  let m := k.val + 1
  have hm : m ≤ n := by dsimp [m]; omega
  have hym : harperBlockEndpoint (start + m) ≤ y :=
    (monotone_harperBlockEndpoint (by omega)).trans hy
  have hosc := ho start m y (by omega) hym a ha t ht
  have hrecip := (hr 1 start n y (by omega) hy t
    (by rw [abs_of_nonneg (show 0 ≤ t by linarith [ht.1])]; norm_num; linarith [ht.1])
    (by rw [abs_of_nonneg (show 0 ≤ t by linarith [ht.1])]; simpa using ht.2) k).1
  have hsum : (∑ p ∈ harperScheduledPrimeRangeFrom y start m, (p.1 : ℝ)⁻¹) ≤
      (m : ℝ) * Real.log 2 + L := by
    rw [sum_inv_harperScheduledPrimeRangeFrom_eq,
      ← sum_Iic_eq_sum_fin_prefix (fun q => harperScheduledReciprocalMass y (start + q)) k]
    linarith [le_of_abs_le hrecip]
  have hpinch := candidate_rankinCenteredRangeFrom_le_forwardLog y start n a t eta heta k
  have hlog := candidate_rankinPrefix_log_upper y start m ha t eta
  have hexp : Real.log (candidateRankinSubsetNormalizedDensity y
      (harperScheduledPrimeRangeFrom y start m) a t eta) ≤
        (m : ℝ) * Real.log 2 + C - 4 * Real.log (m : ℝ) := by
    dsimp [C, m] at *
    linarith [le_of_abs_le hosc]
  have hpos := candidate_rankinSubsetNormalizedDensity_pos y
    (harperScheduledPrimeRangeFrom y start m) ha t eta
  have hmpos : (0 : ℝ) < m := by dsimp [m]; positivity
  calc
    _ ≤ Real.exp ((m : ℝ) * Real.log 2 + C - 4 * Real.log (m : ℝ)) :=
      (Real.log_le_iff_le_exp hpos).mp hexp
    _ = Real.exp C * (2 : ℝ) ^ m / (m : ℝ) ^ 4 := by
      rw [show (m : ℝ) * Real.log 2 + C - 4 * Real.log (m : ℝ) =
        C + (m : ℝ) * Real.log 2 - 4 * Real.log (m : ℝ) by ring,
        Real.exp_sub, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [show (4 : ℝ) * Real.log (m : ℝ) = ((4 : ℕ) : ℝ) * Real.log (m : ℝ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hmpos]

end Erdos.Problem1144
