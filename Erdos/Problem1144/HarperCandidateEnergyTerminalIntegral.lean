import Erdos.Problem1144.HarperCandidateEnergyComplementCorrelation
import Erdos.Problem1144.HarperNearDiagonalStrip

open Finset MeasureTheory ProbabilityTheory Set Filter
open Erdos.Problem520
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- The terminal gap is absorbed by three spare powers of the path length.
Thus its possibly large fixed size does not affect the polynomial Rankin
constant in the actual near-diagonal height integral. -/
theorem candidate_exists_rankinLogBallot_nearDiagonal_integral_le_polynomial :
    ∃ C > 0, ∃ J : ℕ, ∀ V : ℝ, 0 ≤ V → ∀ start n gap y : ℕ,
      J ≤ start → 0 < n → harperBlockEndpoint (start + n + gap) ≤ y →
      y < harperBlockEndpoint (start + n + gap + 1) →
      (1 + 4 * V) * Real.log 4 ≤ Real.log y →
      (4 : ℝ) ^ gap ≤ (n : ℝ) ^ 3 →
      ∀ ha : 0 ≤ 4 * V / Real.log (y : ℝ),
      (∫ ts in harperTerminalNearDiagonalStrip n,
        harperRankinTwoHeightCorrelation y (4 * V / Real.log y) ts.1 ts.2 *
          (harperRankinTwoHeightCubeLaw y (4 * V / Real.log y) ha ts.1 ts.2).real
            (harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) ts.1 ∩
              harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) ts.2)
        ∂(volume.restrict harperLowerVerticalBand).prod (volume.restrict harperLowerVerticalBand)) ≤
          C * (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72 *
            (4 : ℝ) ^ start * (n : ℝ)⁻¹ := by
  obtain ⟨C₀, hC₀, J, hpoint⟩ := candidate_exists_rankinLogBallot_terminal_correlation_probability_le
  refine ⟨C₀ / 3, by positivity, J, ?_⟩
  intro V hV start n gap y hstart hn hlow hupp hsize hgap ha
  let R := candidateRankinNormalizerRatioConstant * (1 + 4 * V)
  have hR : 0 ≤ R := mul_nonneg candidateRankinNormalizerRatioConstant_pos.le (by linarith)
  let f : ℝ × ℝ → ℝ := fun ts =>
    harperRankinTwoHeightCorrelation y (4 * V / Real.log y) ts.1 ts.2 *
      (harperRankinTwoHeightCubeLaw y (4 * V / Real.log y) ha ts.1 ts.2).real
        (harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) ts.1 ∩
          harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) ts.2)
  have hC : 0 ≤ C₀ * R ^ 72 * (4 : ℝ) ^ start :=
    mul_nonneg (mul_nonneg hC₀.le (pow_nonneg hR _)) (by positivity)
  have hf : ∀ ts, 0 ≤ f ts := fun ts => mul_nonneg
    (harperRankinTwoHeightCorrelation_pos y ha ts.1 ts.2).le measureReal_nonneg
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfrac : (4 : ℝ) ^ gap / (n : ℝ) ^ 4 ≤ (n : ℝ)⁻¹ := by
    calc
      _ ≤ (n : ℝ) ^ 3 / (n : ℝ) ^ 4 := div_le_div_of_nonneg_right hgap (by positivity)
      _ = _ := by field_simp
  have hb (ts : ℝ × ℝ) (ht : ts.1 ∈ harperLowerVerticalBand)
      (hs : ts.2 ∈ harperLowerVerticalBand) :
      f ts ≤ (C₀ * R ^ 72 * (4 : ℝ) ^ start) * (2 : ℝ) ^ n * (n : ℝ)⁻¹ := by
    have h := hpoint V hV start n gap y hstart hn hlow hupp hsize ts.1 ht ts.2 hs ha
    calc
      _ ≤ C₀ * R ^ 72 * (4 : ℝ) ^ (start + gap) * (2 : ℝ) ^ n / (n : ℝ) ^ 4 := h
      _ = (C₀ * R ^ 72 * (4 : ℝ) ^ start * (2 : ℝ) ^ n) *
        ((4 : ℝ) ^ gap / (n : ℝ) ^ 4) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hC (by positivity))
  have h := integral_harperTerminalNearDiagonalStrip_le_of_bound n hn f
    (C₀ * R ^ 72 * (4 : ℝ) ^ start) hC hf hb
  convert h using 1 <;> ring

/-- Every fixed terminal gap eventually meets the preceding absorption
condition, with no growth restriction on the gap as a function of `V`. -/
theorem candidate_eventually_terminalGap_absorbed (gap : ℕ) :
    ∀ᶠ n : ℕ in atTop, (4 : ℝ) ^ gap ≤ (n : ℝ) ^ 3 := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop _

end Erdos.Problem1144
