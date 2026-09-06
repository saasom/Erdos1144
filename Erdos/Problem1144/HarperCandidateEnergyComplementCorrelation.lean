import Erdos.Problem1144.HarperCandidateEnergySubsetCorrelation
import Erdos.Problem1144.HarperPartialBlockScreen

open Finset
open Erdos.Problem520
open scoped BigOperators

namespace Erdos.Problem1144

/-- The actual shifted complement, including an arbitrary terminal partial
block, has the critical shell bound with only polynomial Rankin loss.
The initial index and the multiplicative constant are absolute. -/
theorem candidate_exists_rankinPrefixComplement_shell_le_polynomial :
    ∃ D > 0, ∃ J : ℕ, ∀ V : ℝ, 0 ≤ V → ∀ q start r n y : ℕ,
      J ≤ start → r ≤ n → J + (q + 1) ≤ start + r →
      harperBlockEndpoint (start + n) ≤ y →
      y < harperBlockEndpoint (start + n + 1) →
      (1 + 4 * V) * Real.log 4 ≤ Real.log y →
      ∀ t ∈ harperLowerVerticalBand, ∀ s ∈ harperLowerVerticalBand,
        (1 / 2 : ℝ) ^ (q + 1) < |t - s| →
        candidateRankinSubsetCorrelation y (harperScheduledPrimeRangeFrom y start r)ᶜ
          (4 * V / Real.log y) t s ≤
          D * (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72 * (4 : ℝ) ^ start := by
  obtain ⟨D, hD, J, hcrit⟩ := exists_harperScheduledPrefixComplement_shell_le_four_pow_start_envelope
  refine ⟨D, hD, J, ?_⟩
  intro V hV q start r n y hstart hrn hcoh hlow hupp hsize t ht s hs hsep
  have hy : 4 ≤ y := (by have := harperBlockEndpoint_ge_sixteen (start + n); omega)
  have hshift := candidate_rankinSubsetCorrelation_le_critical_polynomial hV hy hsize
    (harperScheduledPrimeRangeFrom y start r)ᶜ t s
  have hbound := hcrit q start r n y hstart hrn hcoh hlow hupp t ht s hs hsep
  calc
    _ ≤ _ := hshift
    _ ≤ (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72 *
      (D * (4 : ℝ) ^ start) := mul_le_mul_of_nonneg_left hbound
        (pow_nonneg (mul_nonneg candidateRankinNormalizerRatioConstant_pos.le (by linarith)) 72)
    _ = _ := by ring

private theorem critical_terminal_complement_with_gap :
    ∃ D > 0, ∃ J : ℕ, ∀ start n gap y : ℕ, J ≤ start →
      harperBlockEndpoint (start + n + gap) ≤ y →
      y < harperBlockEndpoint (start + n + gap + 1) →
      ∀ t ∈ harperLowerVerticalBand, ∀ s ∈ harperLowerVerticalBand,
        harperSubsetCorrelation y (harperScheduledPrimeRangeFrom y start n)ᶜ t s ≤
          D * (4 : ℝ) ^ (start + gap) := by
  obtain ⟨D₀, hD₀, J₀, hprefix⟩ := exists_harperScheduledPrimePrefix_correlation_le_four_pow
  obtain ⟨D₁, hD₁, J₁, htail⟩ := exists_harperScheduledRange_correlation_le_four_pow
  obtain ⟨D₂, hD₂, J₂, hpartial⟩ := exists_eventually_harperScheduledPrimeBlock_partial_correlation_le
  let J := max J₀ (max (J₁ + 1) J₂)
  refine ⟨D₀ * D₁ * D₂, by positivity, J, ?_⟩
  intro start n gap y hstart hlow hupp t ht s hs
  have hpref := hprefix start y (by dsimp [J] at hstart; omega)
    ((monotone_harperBlockEndpoint (by omega)).trans hlow) t ht s hs
  have hlate := htail (start + n) gap y (by dsimp [J] at hstart; omega) hlow t ht s hs
  have hpart := hpartial (start + (n + gap)) (by dsimp [J] at hstart; omega) y t s
  have hdis : Disjoint (harperScheduledPrimePrefix y start)
      (harperScheduledPrimeRangeFrom y (start + n) gap) := by
    rw [Finset.disjoint_left]
    intro p hp ht
    have hlo := (mem_harperScheduledPrimeRangeFrom p).mp ht |>.1
    have hhi := (mem_harperScheduledPrimePrefix p).mp hp
    have hmono := monotone_harperBlockEndpoint (show start ≤ start + n by omega)
    omega
  have hset := harperScheduledPrimeRangeFrom_compl_eq_prefix_union_tail_union_partial
    (y := y) (start := start) (r := n) (n := n + gap) (by omega)
    (by simpa [Nat.add_assoc] using hlow) (by simpa [Nat.add_assoc] using hupp)
  have hdispart := disjoint_harperPrefix_union_tail_partialBlock y start n (n + gap) (by omega)
  simp only [Nat.add_sub_cancel_left] at hset hdispart
  rw [hset, harperSubsetCorrelation_union y hdispart, harperSubsetCorrelation_union y hdis]
  calc
    _ ≤ ((D₀ * (4 : ℝ) ^ start) * (D₁ * (4 : ℝ) ^ gap)) * D₂ :=
      mul_le_mul (mul_le_mul hpref hlate (harperSubsetCorrelation_pos y _ t s).le (by positivity))
        hpart (harperSubsetCorrelation_pos y _ t s).le (by positivity)
    _ = (D₀ * D₁ * D₂) * (4 : ℝ) ^ (start + gap) := by rw [pow_add]; ring

/-- Terminal complements retain an explicit radial gap, with the whole
unfinished prime block included. The gap costs only `4^gap`. -/
theorem candidate_exists_rankinTerminalComplement_le_polynomial_gap :
    ∃ D > 0, ∃ J : ℕ, ∀ V : ℝ, 0 ≤ V → ∀ start n gap y : ℕ, J ≤ start →
      harperBlockEndpoint (start + n + gap) ≤ y →
      y < harperBlockEndpoint (start + n + gap + 1) →
      (1 + 4 * V) * Real.log 4 ≤ Real.log y →
      ∀ t ∈ harperLowerVerticalBand, ∀ s ∈ harperLowerVerticalBand,
        candidateRankinSubsetCorrelation y (harperScheduledPrimeRangeFrom y start n)ᶜ
          (4 * V / Real.log y) t s ≤
          D * (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72 *
            (4 : ℝ) ^ (start + gap) := by
  obtain ⟨D, hD, J, hcrit⟩ := critical_terminal_complement_with_gap
  refine ⟨D, hD, J, ?_⟩
  intro V hV start n gap y hstart hlow hupp hsize t ht s hs
  have hy : 4 ≤ y := (by have := harperBlockEndpoint_ge_sixteen (start + n + gap); omega)
  have hshift := candidate_rankinSubsetCorrelation_le_critical_polynomial hV hy hsize
    (harperScheduledPrimeRangeFrom y start n)ᶜ t s
  have hbound := hcrit start n gap y hstart hlow hupp t ht s hs
  calc
    _ ≤ _ := hshift
    _ ≤ (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72 *
      (D * (4 : ℝ) ^ (start + gap)) := mul_le_mul_of_nonneg_left hbound
        (pow_nonneg (mul_nonneg candidateRankinNormalizerRatioConstant_pos.le (by linarith)) 72)
    _ = _ := by ring

/-- The same-graph terminal likelihood estimate, with both the actual
radial gap and the arbitrary final prime cutoff visible. -/
theorem candidate_exists_rankinLogBallot_terminal_correlation_probability_le :
    ∃ C > 0, ∃ J : ℕ, ∀ V : ℝ, 0 ≤ V → ∀ start n gap y : ℕ,
      J ≤ start → 0 < n → harperBlockEndpoint (start + n + gap) ≤ y →
      y < harperBlockEndpoint (start + n + gap + 1) →
      (1 + 4 * V) * Real.log 4 ≤ Real.log y →
      ∀ t ∈ harperLowerVerticalBand, ∀ s ∈ harperLowerVerticalBand,
        let a := 4 * V / Real.log y
        ∀ ha : 0 ≤ a,
        harperRankinTwoHeightCorrelation y a t s *
          (harperRankinTwoHeightCubeLaw y a ha t s).real
            (harperRankinLogBallotCubeEvent y start n a t ∩
              harperRankinLogBallotCubeEvent y start n a s) ≤
          C * (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72 *
            (4 : ℝ) ^ (start + gap) * (2 : ℝ) ^ n / (n : ℝ) ^ 4 := by
  obtain ⟨B, hB, Jp, hcap⟩ := candidate_exists_rankinLogBallot_prefixDensity_le_powTwo_div_fourth
  obtain ⟨D, hD, Jc, hcorr⟩ := candidate_exists_rankinTerminalComplement_le_polynomial_gap
  refine ⟨B * D, mul_pos hB hD, max (Jp + 1) Jc, ?_⟩
  intro V hV start n gap y hstart hn hlow hupp hsize t ht s hs a ha
  let k : Fin n := ⟨n - 1, by omega⟩
  have hk : k.val + 1 = n := by dsimp [k]; omega
  have hcap' (eta : HarperPrimeCube y)
      (heta : eta ∈ harperRankinLogBallotCubeEvent y start n a t ∩
        harperRankinLogBallotCubeEvent y start n a s) :
      candidateRankinSubsetNormalizedDensity y (harperScheduledPrimeRangeFrom y start n) a s eta ≤
        B * (2 : ℝ) ^ n / (n : ℝ) ^ 4 := by
    have h := hcap start n y (by omega)
      ((monotone_harperBlockEndpoint (by omega)).trans hlow) a ha s hs eta heta.2 k
    simpa only [hk] using h
  have hprob := candidate_rankinTwoHeightCorrelation_mul_probability_le_of_prefixCap
    y (harperScheduledPrimeRangeFrom y start n) ha t s _ _ (by positivity) hcap'
  have hcomp := hcorr V hV start n gap y (by omega) hlow hupp hsize t ht s hs
  calc
    _ ≤ _ := hprob
    _ ≤ (B * (2 : ℝ) ^ n / (n : ℝ) ^ 4) *
      (D * (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72 *
        (4 : ℝ) ^ (start + gap)) := mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = _ := by ring

end Erdos.Problem1144
