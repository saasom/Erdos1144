import Erdos.Problem1144.HarperCandidateEnergyNaturalRooted
import Erdos.Problem1144.HarperCandidateEnergyComplementCorrelation
import Erdos.Problem1144.HarperOverlapShellAssembly

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos.Problem1144

/-- Natural separated-height shell bound.  The absolute start is independent
of the Rankin parameter, and any larger terminal gap is allowed. -/
theorem candidate_exists_rankinLogBallot_naturalShell_pointwise_le :
    ∃ C > 0, ∃ J : Nat, ∀ V : ℝ, 0 ≤ V → ∃ gap₀ : Nat,
      ∀ start q d m gap y : Nat, J ≤ start → q + 1 ≤ d → 0 < m → gap₀ ≤ gap →
        Problem520.harperBlockEndpoint (start + d + m + gap) ≤ y →
        y < Problem520.harperBlockEndpoint (start + d + m + gap + 1) →
        (1 + 4 * V) * Real.log 4 ≤ Real.log y →
        ∀ ha : 0 ≤ 4 * V / Real.log (y : ℝ), ∀ t ∈ harperLowerVerticalBand,
        ∀ s ∈ harperLowerVerticalBand, (1 / 2 : ℝ) ^ (q + 1) < |t - s| →
          harperRankinTwoHeightCorrelation y (4 * V / Real.log y) t s *
            (harperRankinTwoHeightCubeLaw y (4 * V / Real.log y) ha t s).real
              (harperRankinLogBallotCubeEvent y start (d + m) (4 * V / Real.log y) t ∩
                harperRankinLogBallotCubeEvent y start (d + m) (4 * V / Real.log y) s) ≤
          C * (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72 *
            (4 : ℝ) ^ start * (2 : ℝ) ^ (q + 1) / (q + 1 : Nat) ^ 4 *
              ((d + 1 : Nat) ^ 2 * (m : ℝ)⁻¹) := by
  obtain ⟨B, hB, L, hL, Jroot, hroot⟩ :=
    candidate_exists_gap_rankinLogBallot_rooted_naturalSuffix_le
  obtain ⟨D, hD, Jcorr, hcorr⟩ :=
    candidate_exists_rankinPrefixComplement_shell_le_polynomial
  let K : ℝ := 4 * Real.exp 4 * (4096 * 68 * (536 * L + 68))
  let C : ℝ := B * D * K
  refine ⟨C, by dsimp only [C, K]; positivity, max Jroot Jcorr, ?_⟩
  intro V hV
  obtain ⟨gap₀, hroot⟩ := hroot V hV
  refine ⟨gap₀, ?_⟩
  intro start q d m gap y hstart hqd hm hgap hy hyupper hsize ha t ht s hs hsep
  have hstartRoot : Jroot ≤ start := (le_max_left _ _).trans hstart
  have hstartCorr : Jcorr ≤ start := (le_max_right _ _).trans hstart
  have hyRoot : Problem520.harperBlockEndpoint (start + d + m + gap₀) ≤ y :=
    (Problem520.strictMono_harperBlockEndpoint.monotone (by omega)).trans hy
  have hrooted := hroot start q d m y hstartRoot hqd hm hyRoot ha t ht s hs hsep
  dsimp only at hrooted
  have hcomp := hcorr V hV q start (q + 1) (d + m + gap) y hstartCorr
    (by omega) (by omega) (by simpa only [add_assoc] using hy)
    (by simpa only [add_assoc] using hyupper) hsize t ht s hs hsep
  have hleft : 0 ≤ B * (2 : ℝ) ^ (q + 1) / (q + 1 : Nat) ^ 4 := by positivity
  have hsuffix : 0 ≤ 4 * Real.exp 4 *
      ((4096 * 68 * (536 * L + 68)) * (d + 1 : Nat) ^ 2 * (m : ℝ)⁻¹) := by positivity
  apply hrooted.trans
  calc
    _ ≤ ((B * (2 : ℝ) ^ (q + 1) / (q + 1 : Nat) ^ 4) *
        (D * (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72 *
          (4 : ℝ) ^ start)) *
        (4 * Real.exp 4 * ((4096 * 68 * (536 * L + 68)) *
          (d + 1 : Nat) ^ 2 * (m : ℝ)⁻¹)) := by gcongr
    _ = _ := by dsimp only [C, K]; ring

/-- Integration of every shell with a nonempty suffix gives the summable
natural shell weight, uniformly in the allowable terminal gap. -/
theorem candidate_exists_rankinLogBallot_naturalShell_integral_le :
    ∃ C > 0, ∃ J : Nat, ∀ V : ℝ, 0 ≤ V → ∃ gap₀ : Nat,
      ∀ start n q gap y : Nat, J ≤ start → q + 2 ≤ n → gap₀ ≤ gap →
        Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
        y < Problem520.harperBlockEndpoint (start + n + gap + 1) →
        (1 + 4 * V) * Real.log 4 ≤ Real.log y →
        ∀ ha : 0 ≤ 4 * V / Real.log (y : ℝ),
        (∫ ts in harper1144OverlapShell q,
          harperRankinTwoHeightCorrelation y (4 * V / Real.log y) ts.1 ts.2 *
            (harperRankinTwoHeightCubeLaw y (4 * V / Real.log y) ha ts.1 ts.2).real
              (harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) ts.1 ∩
                harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) ts.2)
          ∂(volume.restrict harperLowerVerticalBand).prod (volume.restrict harperLowerVerticalBand)) ≤
        C * (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72 *
          (4 : ℝ) ^ start * harper1144OverlapShellWeight n q := by
  obtain ⟨C₀, hC₀, J, hpoint⟩ := candidate_exists_rankinLogBallot_naturalShell_pointwise_le
  refine ⟨8 * C₀, by positivity, J, ?_⟩
  intro V hV
  obtain ⟨gap₀, hpoint⟩ := hpoint V hV
  refine ⟨gap₀, ?_⟩
  intro start n q gap y hstart hq hgap hy hyupper hsize ha
  let d : Nat := q + 1
  let m : Nat := n - (q + 1)
  let R : ℝ := (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hm : 0 < m := by dsimp only [m]; omega
  have hsum : d + m = n := by dsimp only [d, m]; omega
  have hid : start + d + m = start + n := by omega
  let f : ℝ × ℝ → ℝ := fun ts =>
    harperRankinTwoHeightCorrelation y (4 * V / Real.log y) ts.1 ts.2 *
      (harperRankinTwoHeightCubeLaw y (4 * V / Real.log y) ha ts.1 ts.2).real
        (harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) ts.1 ∩
          harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) ts.2)
  have hf : ∀ ts, 0 ≤ f ts := fun ts =>
    mul_nonneg (harperRankinTwoHeightCorrelation_pos y ha ts.1 ts.2).le measureReal_nonneg
  have hb : ∀ ts ∈ harperLowerVerticalBand ×ˢ harperLowerVerticalBand,
      ts ∈ harper1144OverlapShell q →
      f ts ≤ (C₀ * R) * (4 : ℝ) ^ start * (2 : ℝ) ^ (q + 1) /
        (q + 1 : Nat) ^ 4 * ((d + 1 : Nat) ^ 2 * (m : ℝ)⁻¹) := by
    intro ts hband hshell
    have hsep : (1 / 2 : ℝ) ^ (q + 1) < |ts.1 - ts.2| := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
      exact (mem_harper1144OverlapShell_iff.mp hshell).1
    have h := hpoint start q d m gap y hstart (by simp [d]) hm hgap
      (by simpa only [hid] using hy)
      (by simpa only [hid] using hyupper) hsize ha
      ts.1 hband.1 ts.2 hband.2 hsep
    simpa only [f, R, hsum] using h
  have hi := integral_harper1144OverlapShell_le_of_naturalRooted_bound
    q start d m (C₀ * R) (mul_nonneg hC₀.le hR) f hf hb
  have hn := mul_le_mul_of_nonneg_left
    (harper1144_naturalShell_numeric_le_weight hq)
    (show 0 ≤ C₀ * R * (4 : ℝ) ^ start by positivity)
  have heq : (q + 1 + 1 : Nat) = q + 2 := by omega
  dsimp only [d, m] at hi
  rw [heq] at hi
  convert hi.trans (by convert hn using 1 <;> ring) using 1 <;> dsimp only [f, R] <;> ring

end Erdos.Problem1144
