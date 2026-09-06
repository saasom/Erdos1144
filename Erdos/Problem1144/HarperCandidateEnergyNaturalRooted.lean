import Erdos.Problem1144.HarperCandidateEnergyNaturalSuffix
import Erdos.Problem1144.HarperCandidateEnergyTwoHeightPath
import Erdos.Problem1144.HarperCandidateEnergyPrefixLikelihood

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos.Problem1144

/-! Exact same-graph prefix identification and rooted natural suffix assembly. -/

theorem candidate_rankinCubeLaw_logBallotPrefixInter_eq_pi
    (y start d m : Nat) (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real) :
    (harperRankinTwoHeightCubeLaw y σ hσ t s).real
        (harperRankinLogBallotCubeEvent y start d σ t ∩
          harperRankinLogBallotCubeEvent y start d σ s) =
      (Measure.pi (fun i : Fin d ↦
        candidateRankinTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + i.val)) σ hσ t s)).real
        (harperPairedLogBallotPrefixSet start d m) := by
  have hproduct :=
    candidate_rankinCubeLaw_real_preimage_scheduledBallotBlockVectors_eq_pi
      y start d σ hσ t s
      (harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start d)
        (harper1144LogBallotUpperBarrier d))
      (measurableSet_harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start d)
        (harper1144LogBallotUpperBarrier d))
  rw [candidate_preimage_rankinScheduledBallotBlockVectors_pairedLogBarrier_eq_inter] at hproduct
  rw [harperPairedLogBallotPrefixSet_eq]
  exact hproduct

theorem candidate_exists_gap_rankinLogBallot_rooted_naturalSuffix_le :
    ∃ B > 0, ∃ L > 0, ∃ J : Nat, ∀ V : ℝ, 0 ≤ V → ∃ gap : Nat,
      ∀ start q d m y : Nat, J ≤ start → q + 1 ≤ d → 0 < m →
        Problem520.harperBlockEndpoint (start + d + m + gap) ≤ y →
          ∀ hσ : 0 ≤ 4 * V / Real.log (y : ℝ), ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (q + 1) < |t - s| →
                let P := Problem520.harperScheduledPrimeRangeFrom y start (q + 1)
                harperRankinTwoHeightCorrelation y (4 * V / Real.log (y : ℝ)) t s *
                    (harperRankinTwoHeightCubeLaw y (4 * V / Real.log (y : ℝ)) hσ t s).real
                      (harperRankinLogBallotCubeEvent y start (d + m) (4 * V / Real.log (y : ℝ)) t ∩
                        harperRankinLogBallotCubeEvent y start (d + m) (4 * V / Real.log (y : ℝ)) s) ≤
                  ((B * (2 : Real) ^ (q + 1) /
                      (((q + 1 : Nat) : Real) ^ (4 : Nat))) *
                    candidateRankinSubsetCorrelation y Pᶜ (4 * V / Real.log (y : ℝ)) t s) *
                    (4 * Real.exp 4 *
                      ((4096 * 68 * (536 * L + 68)) *
                        (((d + 1 : Nat) : Real) ^ (2 : Nat)) *
                          (m : Real)⁻¹)) := by
  obtain ⟨B, hB, Jroot, hroot⟩ :=
    candidate_exists_rankinLogBallot_correlation_probability_le_prefix_compl
  obtain ⟨L, hL, Jsuffix, hsuffix⟩ :=
    candidate_exists_gap_rankinLogBallotProduct_natural_le_prefix_mul
  let J := max (Jroot + 1) Jsuffix
  refine ⟨B, hB, L, hL, J, ?_⟩
  intro V hV
  obtain ⟨gap, hsuffix⟩ := hsuffix V hV
  refine ⟨gap, ?_⟩
  intro start q d m y hstart hqd hm hy hσ t ht s hs hsep
  dsimp only
  let C : Real := 4 * Real.exp 4 *
    ((4096 * 68 * (536 * L + 68)) *
      (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹)
  let M : Real := B * (2 : Real) ^ (q + 1) /
    (((q + 1 : Nat) : Real) ^ (4 : Nat))
  have hstartRoot : Jroot + 1 ≤ start :=
    (le_max_left (Jroot + 1) Jsuffix).trans hstart
  have hstartSuffix : Jsuffix ≤ start :=
    (le_max_right (Jroot + 1) Jsuffix).trans hstart
  have hdPos : 0 < d := by omega
  have hprefixY : Problem520.harperBlockEndpoint (start + d) ≤ y := by
    apply (Problem520.strictMono_harperBlockEndpoint.monotone ?_).trans hy
    omega
  let commonLast : Fin d := ⟨q, by omega⟩
  have hcommonLastVal : commonLast.val + 1 = q + 1 := by
    rfl
  have hprefixOne := hroot start d y hstartRoot hprefixY
    _ hσ s hs t commonLast
  have hprefixRoot := (mul_le_mul_of_nonneg_left
    (measureReal_mono (μ := harperRankinTwoHeightCubeLaw y _ hσ t s)
      (show harperRankinLogBallotCubeEvent y start d (4 * V / Real.log (y : ℝ)) t ∩
        harperRankinLogBallotCubeEvent y start d (4 * V / Real.log (y : ℝ)) s ⊆
        harperRankinLogBallotCubeEvent y start d (4 * V / Real.log (y : ℝ)) s from inter_subset_right))
    (harperRankinTwoHeightCorrelation_pos y hσ t s).le).trans hprefixOne
  rw [hcommonLastVal] at hprefixRoot
  have hprefixProduct := hsuffix q start d m y hm hstartSuffix hqd hy
    hσ t ht s hs hsep
  have hfullEq :=
    candidate_rankinCubeLaw_real_preimage_scheduledBallotBlockVectors_eq_pi
      y start (d + m) _ hσ t s
      (harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start (d + m))
        (harper1144LogBallotUpperBarrier (d + m)))
      (measurableSet_harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start (d + m))
        (harper1144LogBallotUpperBarrier (d + m)))
  rw [candidate_preimage_rankinScheduledBallotBlockVectors_pairedLogBarrier_eq_inter] at hfullEq
  have hprefixEq :=
    candidate_rankinCubeLaw_logBallotPrefixInter_eq_pi
      y start d m _ hσ t s
  have hprob :
      (harperRankinTwoHeightCubeLaw y (4 * V / Real.log (y : ℝ)) hσ t s).real
          (harperRankinLogBallotCubeEvent y start (d + m) (4 * V / Real.log (y : ℝ)) t ∩
            harperRankinLogBallotCubeEvent y start (d + m) (4 * V / Real.log (y : ℝ)) s) ≤
        (harperRankinTwoHeightCubeLaw y (4 * V / Real.log (y : ℝ)) hσ t s).real
          (harperRankinLogBallotCubeEvent y start d (4 * V / Real.log (y : ℝ)) t ∩
            harperRankinLogBallotCubeEvent y start d (4 * V / Real.log (y : ℝ)) s) * C := by
    rw [hfullEq, hprefixEq]
    simpa only [C] using hprefixProduct
  have hcorrNonneg : 0 ≤ harperRankinTwoHeightCorrelation y (4 * V / Real.log (y : ℝ)) t s :=
    (harperRankinTwoHeightCorrelation_pos y hσ t s).le
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    positivity
  calc
    harperRankinTwoHeightCorrelation y (4 * V / Real.log (y : ℝ)) t s *
        (harperRankinTwoHeightCubeLaw y (4 * V / Real.log (y : ℝ)) hσ t s).real
          (harperRankinLogBallotCubeEvent y start (d + m) (4 * V / Real.log (y : ℝ)) t ∩
            harperRankinLogBallotCubeEvent y start (d + m) (4 * V / Real.log (y : ℝ)) s) ≤
      harperRankinTwoHeightCorrelation y (4 * V / Real.log (y : ℝ)) t s *
        ((harperRankinTwoHeightCubeLaw y (4 * V / Real.log (y : ℝ)) hσ t s).real
          (harperRankinLogBallotCubeEvent y start d (4 * V / Real.log (y : ℝ)) t ∩
            harperRankinLogBallotCubeEvent y start d (4 * V / Real.log (y : ℝ)) s) * C) :=
        mul_le_mul_of_nonneg_left hprob hcorrNonneg
    _ = (harperRankinTwoHeightCorrelation y (4 * V / Real.log (y : ℝ)) t s *
        (harperRankinTwoHeightCubeLaw y (4 * V / Real.log (y : ℝ)) hσ t s).real
          (harperRankinLogBallotCubeEvent y start d (4 * V / Real.log (y : ℝ)) t ∩
            harperRankinLogBallotCubeEvent y start d (4 * V / Real.log (y : ℝ)) s)) * C := by ring
    _ ≤ (M * candidateRankinSubsetCorrelation y
        (Problem520.harperScheduledPrimeRangeFrom y start (q + 1))ᶜ (4 * V / Real.log (y : ℝ)) t s) * C :=
      mul_le_mul_of_nonneg_right (by simpa only [M] using hprefixRoot)
        hCnonneg
    _ = _ := by rfl

end Erdos.Problem1144
