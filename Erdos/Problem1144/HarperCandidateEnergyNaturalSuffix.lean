import Erdos.Problem1144.HarperCandidateEnergyMatchedDrift

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos.Problem1144

/-- Literal one-height-centered Rankin suffix survival from natural coherence.
The constants and starting index are absolute; only the terminal gap depends on V. -/
theorem candidate_exists_gap_rankinLogBallotSuffix_natural_le :
    ∃ L > 0, ∃ J : Nat, ∀ V : ℝ, 0 ≤ V → ∃ gap : Nat,
      ∀ shell baseStart d m y : Nat, 0 < m →
        J ≤ baseStart → shell + 1 ≤ d →
        Problem520.harperBlockEndpoint (baseStart + d + m + gap) ≤ y →
          ∀ hσ : 0 ≤ 4 * V / Real.log (y : ℝ), ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (shell + 1) < |t - s| →
                ∀ u : Fin d → Real × Real,
                  ∀ v : Fin m → Real × Real,
                    Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
                      (harper1144LogBallotLowerBarrier baseStart (d + m))
                      (harper1144LogBallotUpperBarrier (d + m)) →
                    let lower := harperPairedSuffixLower
                      (harper1144LogBallotLowerBarrier baseStart (d + m)) u
                    let upper := harperPairedSuffixUpper
                      (harper1144LogBallotUpperBarrier (d + m)) u
                    (Measure.pi (fun i : Fin m ↦
                      candidateRankinTwoHeightBallotBlockLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (baseStart + d + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
                        (harperPairedPartialSumBarrierSet lower upper) ≤
                      4 * Real.exp 4 *
                        ((4096 * 68 * (536 * L + 68)) *
                          (((d + 1 : Nat) : Real) ^ (2 : Nat)) *
                            (m : Real)⁻¹) := by
  obtain ⟨Jpath, hpath⟩ :=
    candidate_exists_gap_rankinPairedBarrier_le_gaussianRelaxed
  obtain ⟨L, hL, Jgauss, hgauss⟩ :=
    candidate_exists_gap_rankinMatchedGaussian_relaxedSuffixGuard_le
  obtain ⟨Jdrift, hdrift⟩ :=
    candidate_exists_rankinRelativeDrift_geometric_half
  let J := max 31 (max Jpath (max Jgauss Jdrift))
  refine ⟨L, hL, J, ?_⟩
  intro V hV
  obtain ⟨gapPath, hpath⟩ := hpath V hV
  obtain ⟨gapGauss, hgauss⟩ := hgauss V hV
  refine ⟨max gapPath gapGauss, ?_⟩
  intro shell baseStart d m y hm hstart hd hy hσ t ht s hs hsep u v hfull
  dsimp only
  have hyPath : Problem520.harperBlockEndpoint (baseStart + d + m + gapPath) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans hy
  have hyGauss : Problem520.harperBlockEndpoint (baseStart + d + m + gapGauss) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans hy
  have hyNear : Problem520.harperBlockEndpoint (baseStart + d + m) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans hy
  have hdPos : 0 < d := by omega
  have hbaseThirtyOne : 31 ≤ baseStart :=
    (le_max_left 31 (max Jpath (max Jgauss Jdrift))).trans hstart
  have hJpath : Jpath + (shell + 1) ≤ baseStart + d := by
    have : Jpath ≤ baseStart := by
      have hle : Jpath ≤ max 31 (max Jpath (max Jgauss Jdrift)) :=
        (le_max_left Jpath (max Jgauss Jdrift)).trans
          (le_max_right 31 _)
      exact hle.trans hstart
    omega
  have hJgauss : Jgauss + (shell + 1) ≤ baseStart + d := by
    have : Jgauss ≤ baseStart := by
      have hle : Jgauss ≤ max 31 (max Jpath (max Jgauss Jdrift)) :=
        ((le_max_left Jgauss Jdrift).trans (le_max_right Jpath _)).trans
          (le_max_right 31 _)
      exact hle.trans hstart
    omega
  have hJdrift : Jdrift ≤ baseStart := by
    have hle : Jdrift ≤ max 31 (max Jpath (max Jgauss Jdrift)) :=
      ((le_max_right Jgauss Jdrift).trans (le_max_right Jpath _)).trans
        (le_max_right 31 _)
    exact hle.trans hstart
  let lower := harperPairedSuffixLower
    (harper1144LogBallotLowerBarrier baseStart (d + m)) u
  let upper := harperPairedSuffixUpper
    (harper1144LogBallotUpperBarrier (d + m)) u
  let lower₁ : Fin m → Real := fun k ↦ lower k - 1
  let upper₁ : Fin m → Real := fun k ↦ upper k + 1
  let R : Fin m → Real := fun i ↦
    128 * ((d + i.val + 1 : Nat) : Real) + 6
  let G : Fin m → Measure (Real × Real) := fun i ↦
    harperRankinTwoHeightPrimeBlockVectorLaw y
      (Problem520.harperScheduledPrimeBlock y
        (baseStart + d + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s
  let drift : Fin m → Real × Real := fun i ↦
    candidateRankinTwoHeightBallotBlockDrift y
      (Problem520.harperScheduledPrimeBlock y
        (baseStart + d + i.val)) (4 * V / Real.log (y : ℝ)) t s
  let Ggauss : Measure (Fin m → Real × Real) :=
    Measure.pi (fun i : Fin m ↦
      candidateRankinMatchedGaussianLaw y
        (Problem520.harperScheduledPrimeBlock y
          (baseStart + d + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)
  have hdriftPoint := hdrift shell baseStart d m y hJdrift hd hyNear
    _ hσ t ht s hs hsep
  have hdriftPrefix := candidate_cumulative_rankinRelativeDrift_le_one
    hdriftPoint
  have hremoveRaw := pi_translated_pairedBarrier_real_le_relaxed
    G drift lower upper 1
    (fun k ↦ (hdriftPrefix k).1) (fun k ↦ (hdriftPrefix k).2)
  have hlaw :
      (fun i : Fin m ↦
        candidateRankinTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s) =
      fun i : Fin m ↦
        Measure.map (harperPairTranslate (drift i)) (G i) := by
    funext i
    dsimp only [drift, G]
    exact candidateRankinTwoHeightBallotBlockLaw_eq_translate y
      (Problem520.harperScheduledPrimeBlock y
        (baseStart + d + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s
  have hremove :
      (Measure.pi (fun i : Fin m ↦
        candidateRankinTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
          (harperPairedPartialSumBarrierSet lower upper) ≤
        (Measure.pi G).real
          (harperPairedPartialSumBarrierSet lower₁ upper₁) := by
    rw [hlaw]
    simpa only [lower₁, upper₁] using hremoveRaw
  have hcoordinate :
      ∀ x ∈ harperPairedPartialSumBarrierSet lower₁ upper₁,
        ∀ i, |(x i).1| ≤ R i ∧ |(x i).2| ≤ R i := by
    intro x hx i
    have hxRelaxed : x ∈
        harperPairedRelaxedPartialSumBarrierSet lower upper := by
      simpa only [harperPairedRelaxedPartialSumBarrierSet, lower₁, upper₁]
        using hx
    simpa only [lower, upper, R] using
      abs_coordinates_le_of_mem_harperPairedRelaxedSuffix_logBallot
        hdPos u v hfull x hxRelaxed i
  have hmoderate : ∀ i, 2 * R i + 5 ≤
      (1 / 16 : Real) *
        Real.sqrt (((2 ^ (baseStart + d + i.val) : Nat) : Real)) := by
    intro i
    have hmod := harperScheduled_relaxedSuffixEnvelope_le_moderateWindow
      hbaseThirtyOne (d + i.val)
    dsimp only [R]
    rw [show
      2 * (128 * ((d + i.val + 1 : Nat) : Real) + 6) + 5 =
        256 * ((d + i.val + 1 : Nat) : Real) + 17 by ring]
    simpa only [add_assoc] using hmod
  have hcenterCompare := hpath shell (baseStart + d) m y hJpath
    (by simpa only [add_assoc] using hyPath) hσ t ht s hs hsep
    lower₁ upper₁ R hcoordinate hmoderate
  have hlower₁ (k : Fin m) :
      -64 * ((d + k.val + 1 : Nat) : Real) - 2 ≤ lower₁ k := by
    dsimp only [lower₁, lower]
    linarith
      [neg_sixtyFour_mul_suffixElapsed_sub_one_le_harperPairedSuffixLower_logBallot
        hdPos u v hfull k]
  have hupper₁ (k : Fin m) : upper₁ k ≤ 64 * (d : Real) + 1 := by
    dsimp only [upper₁, upper]
    linarith [harperPairedSuffixUpper_logBallot_le hdPos u v hfull k]
  have hsubset :
      harperPairedRelaxedPartialSumBarrierSet lower₁ upper₁ ⊆
        harperPairedRelaxedSuffixGuardPathEvent d m :=
    harperPairedRelaxedPartialSumBarrierSet_subset_suffixGuard
      lower₁ upper₁ hlower₁ hupper₁
  have hmono :
      Ggauss.real
          (harperPairedRelaxedPartialSumBarrierSet lower₁ upper₁) ≤
        Ggauss.real (harperPairedRelaxedSuffixGuardPathEvent d m) :=
    measureReal_mono hsubset
  have hgaussBound := hgauss shell (baseStart + d) d m y hm hJgauss
    (by simpa only [add_assoc] using hyGauss) hσ t ht s hs hsep
  dsimp only [G, Ggauss] at hremove hcenterCompare hmono ⊢
  calc
    (Measure.pi (fun i : Fin m ↦
        candidateRankinTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi (fun i : Fin m ↦
        harperRankinTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
        (harperPairedPartialSumBarrierSet lower₁ upper₁) := hremove
    _ ≤ 4 * Real.exp 4 *
        (Measure.pi (fun i : Fin m ↦
          candidateRankinMatchedGaussianLaw y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
          (harperPairedRelaxedPartialSumBarrierSet lower₁ upper₁) :=
      hcenterCompare
    _ ≤ 4 * Real.exp 4 *
        (Measure.pi (fun i : Fin m ↦
          candidateRankinMatchedGaussianLaw y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
          (harperPairedRelaxedSuffixGuardPathEvent d m) := by
      exact mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ 4 * Real.exp 4 *
        ((4096 * 68 * (536 * L + 68)) *
          (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹) := by
      exact mul_le_mul_of_nonneg_left hgaussBound (by positivity)


/-- Fubini separates the actual exposed prefix from its uniformly bounded suffix. -/
theorem candidate_exists_gap_rankinLogBallotProduct_natural_le_prefix_mul :
    ∃ L > 0, ∃ J : Nat, ∀ V : ℝ, 0 ≤ V → ∃ gap : Nat,
      ∀ shell start d m y : Nat, 0 < m →
        J ≤ start → shell + 1 ≤ d →
        Problem520.harperBlockEndpoint (start + d + m + gap) ≤ y →
          ∀ hσ : 0 ≤ 4 * V / Real.log (y : ℝ), ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (shell + 1) < |t - s| →
                (Measure.pi (fun i : Fin (d + m) ↦
                  candidateRankinTwoHeightBallotBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
                    (harperPairedPartialSumBarrierSet
                      (harper1144LogBallotLowerBarrier start (d + m))
                      (harper1144LogBallotUpperBarrier (d + m))) ≤
                  (Measure.pi (fun i : Fin d ↦
                    candidateRankinTwoHeightBallotBlockLaw y
                      (Problem520.harperScheduledPrimeBlock y
                        (start + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
                      (harperPairedLogBallotPrefixSet start d m) *
                    (4 * Real.exp 4 *
                      ((4096 * 68 * (536 * L + 68)) *
                        (((d + 1 : Nat) : Real) ^ (2 : Nat)) *
                          (m : Real)⁻¹)) := by
  obtain ⟨L, hL, J, hsuffix⟩ :=
    candidate_exists_gap_rankinLogBallotSuffix_natural_le
  refine ⟨L, hL, J, ?_⟩
  intro V hV
  obtain ⟨gap, hsuffix⟩ := hsuffix V hV
  refine ⟨gap, ?_⟩
  intro shell start d m y hm hstart hd hy hσ t ht s hs hsep
  let M : Fin (d + m) → Measure (Real × Real) := fun i ↦
    candidateRankinTwoHeightBallotBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s
  let C : Real := 4 * Real.exp 4 *
    ((4096 * 68 * (536 * L + 68)) *
      (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹)
  apply pi_real_le_prefixEvent_mul_of_suffix_fiberwise M
    (harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)))
    (measurableSet_harperPairedPartialSumBarrierSet _ _)
    (harperPairedLogBallotPrefixSet start d m)
    (measurableSet_harperPairedLogBallotPrefixSet start d m) C
  · intro u v huv
    exact mem_harperPairedLogBallotPrefixSet_of_addCases_mem u v huv
  · intro u _hu
    by_cases hcont : ∃ v : Fin m → Real × Real,
        Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
          (harper1144LogBallotLowerBarrier start (d + m))
          (harper1144LogBallotUpperBarrier (d + m))
    · obtain ⟨v, hv⟩ := hcont
      have hsubset :
          {w : Fin m → Real × Real | Fin.addCases u w ∈
            harperPairedPartialSumBarrierSet
              (harper1144LogBallotLowerBarrier start (d + m))
              (harper1144LogBallotUpperBarrier (d + m))} ⊆
            harperPairedPartialSumBarrierSet
              (harperPairedSuffixLower
                (harper1144LogBallotLowerBarrier start (d + m)) u)
              (harperPairedSuffixUpper
                (harper1144LogBallotUpperBarrier (d + m)) u) := by
        intro w hw
        exact mem_harperPairedSuffixBarrier_of_addCases_mem _ _ u w hw
      have hsuffixBound := hsuffix shell start d m y hm hstart hd hy
        hσ t ht s hs hsep u v hv
      exact (measureReal_mono hsubset (measure_ne_top _ _)).trans (by
        simpa only [M, C, Fin.val_natAdd, add_assoc] using hsuffixBound)
    · have hempty :
          {w : Fin m → Real × Real | Fin.addCases u w ∈
            harperPairedPartialSumBarrierSet
              (harper1144LogBallotLowerBarrier start (d + m))
              (harper1144LogBallotUpperBarrier (d + m))} = ∅ := by
        ext w
        constructor
        · intro hw
          exact False.elim (hcont ⟨w, hw⟩)
        · intro hw
          exact False.elim hw
      rw [hempty, measureReal_empty]
      dsimp only [C]
      positivity


end Erdos.Problem1144
