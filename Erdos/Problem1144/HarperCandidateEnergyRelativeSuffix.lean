import Erdos.Problem1144.HarperCandidateEnergyRelativeLattice
import Erdos.Problem1144.HarperShiftedLatticeSuffix

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos.Problem1144

/-! Covariance-matched comparison of actual shifted translated suffix corridors. -/

theorem candidate_exists_gap_rankinPairedBarrier_le_gaussianRelaxed :
    ∃ J : Nat, ∀ V : ℝ, 0 ≤ V → ∃ gap : Nat, ∀ shell start n y : Nat,
      J + (shell + 1) ≤ start →
      Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
        ∀ hσ : 0 ≤ 4 * V / Real.log (y : ℝ), ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ lower upper R : Fin n → Real,
                (∀ x ∈ harperPairedPartialSumBarrierSet lower upper,
                  ∀ i, |(x i).1| ≤ R i ∧ |(x i).2| ≤ R i) →
                (∀ i, 2 * R i + 5 ≤
                  (1 / 16 : Real) *
                    Real.sqrt (((2 ^ (start + i.val) : Nat) : Real))) →
                (Measure.pi (fun i : Fin n ↦
                  harperRankinTwoHeightPrimeBlockVectorLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
                    (harperPairedPartialSumBarrierSet lower upper) ≤
                  4 * Real.exp 4 *
                    (Measure.pi (fun i : Fin n ↦
                      candidateRankinMatchedGaussianLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (start + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
                      (harperPairedRelaxedPartialSumBarrierSet lower upper) := by
  obtain ⟨Jpath, hpath⟩ :=
    candidate_exists_gap_rankinRelativeShiftedPath_le
  let J := max 6 Jpath
  refine ⟨J, ?_⟩
  intro V hV
  obtain ⟨gap, hpath⟩ := hpath V hV
  refine ⟨gap, ?_⟩
  intro shell start n y hstart hy hσ t ht s hs hsep lower upper R
    hcoordinate hmoderate
  have hstartSix : 6 ≤ start := by
    dsimp only [J] at hstart
    omega
  have hstartPath : Jpath + (shell + 1) ≤ start := by
    dsimp only [J] at hstart
    omega
  let delta : Fin n → Real := fun i ↦
    Problem520.harperScheduledRelativeIntervalWidth (start + i.val)
  let h : Fin n → Real := fun i ↦
    harperScheduledBivariateExpansionRadius (start + i.val)
  let period : Fin n → Real := fun i ↦
    harperShiftedLatticePeriod (delta i) (h i)
  have hdelta (i : Fin n) : 0 ≤ delta i :=
    (Problem520.harperScheduledRelativeIntervalWidth_pos _).le
  have hh (i : Fin n) : 0 ≤ h i :=
    (harperScheduledBivariateExpansionRadius_pos _).le
  have hperiodPos (i : Fin n) : 0 < period i := by
    dsimp only [period, delta, h, harperShiftedLatticePeriod]
    exact add_pos_of_pos_of_nonneg
      (Problem520.harperScheduledRelativeIntervalWidth_pos _)
      (mul_nonneg (by norm_num)
        (harperScheduledBivariateExpansionRadius_pos _).le)
  have hbounded :
      ∀ x ∈ harperPairedPartialSumBarrierSet lower upper, ∀ i,
        (x i).1 ∈ Icc (-(R i)) (R i) ∧
          (x i).2 ∈ Icc (-(R i)) (R i) := by
    intro x hx i
    exact ⟨abs_le.mp (hcoordinate x hx i).1,
      abs_le.mp (hcoordinate x hx i).2⟩
  have hgeometry :
      ∀ phi : Fin n → UnitAddCircle × UnitAddCircle,
        ∃ active : Finset (Fin n → Int × Int),
          harperPairedPartialSumBarrierSet lower upper ∩
              harperShiftedPairPathCoreSet delta h phi ⊆
            ⋃ z ∈ active,
              harperShiftedPairPathCoreCell delta h phi z ∧
          (∀ z ∈ active, ∀ i,
            let j := start + i.val
            let delta :=
              Problem520.harperScheduledRelativeIntervalWidth j
            let h := harperScheduledBivariateExpansionRadius j
            let a := ((z i).1 : Real) +
              harperUnitPhaseRepresentative (phi i).1
            let b := ((z i).2 : Real) +
              harperUnitPhaseRepresentative (phi i).2
            |a * harperShiftedLatticePeriod delta h| +
                |b * harperShiftedLatticePeriod delta h| + 3 ≤
              (1 / 16 : Real) *
                Real.sqrt (((2 ^ j : Nat) : Real))) ∧
          (⋃ z ∈ active,
              harperShiftedPairPathFullCell delta h phi z) ⊆
            harperPairedRelaxedPartialSumBarrierSet lower upper := by
    intro phi
    obtain ⟨active, hcover, hmeets⟩ :=
      exists_finite_shiftedPairPathCoreCell_cover_of_bounded
        (harperPairedPartialSumBarrierSet lower upper)
        delta h R phi (fun i ↦ by
          simpa only [period] using hperiodPos i) hbounded
    refine ⟨active, hcover, ?_, ?_⟩
    · intro z hz i
      dsimp only
      obtain ⟨x, hxBarrier, hxCell⟩ := hmeets z hz
      have hxAll :
          (x i).1 ∈ harperShiftedCoreCell
              (delta i) (h i) (phi i).1 (z i).1 ∧
            (x i).2 ∈ harperShiftedCoreCell
              (delta i) (h i) (phi i).2 (z i).2 := by
        simpa only [harperShiftedPairPathCoreCell, Set.mem_pi,
          Set.mem_univ, forall_const, harperShiftedPairCoreCell,
          Set.mem_prod] using hxCell i
      have hdeltaOne : delta i ≤ 1 := by
        exact Problem520.harperScheduledRelativeIntervalWidth_le_one _
      have ha := abs_shiftedCoreCell_lower_le_abs_add_delta
        (hdelta i) hxAll.1
      have hb := abs_shiftedCoreCell_lower_le_abs_add_delta
        (hdelta i) hxAll.2
      have hxBound := hcoordinate x hxBarrier i
      have hmod := hmoderate i
      dsimp only [delta, h] at ha hb ⊢
      calc
        |(((z i).1 : Real) +
              harperUnitPhaseRepresentative (phi i).1) *
            harperShiftedLatticePeriod
              (Problem520.harperScheduledRelativeIntervalWidth
                (start + i.val))
              (harperScheduledBivariateExpansionRadius
                (start + i.val))| +
          |(((z i).2 : Real) +
              harperUnitPhaseRepresentative (phi i).2) *
            harperShiftedLatticePeriod
              (Problem520.harperScheduledRelativeIntervalWidth
                (start + i.val))
              (harperScheduledBivariateExpansionRadius
                (start + i.val))| + 3 ≤
            2 * R i + 5 := by
              nlinarith
        _ ≤ (1 / 16 : Real) *
            Real.sqrt (((2 ^ (start + i.val) : Nat) : Real)) := hmod
    · apply (iUnion_fullCells_subset_coordinateNeighborhood_of_meets
          (harperPairedPartialSumBarrierSet lower upper)
          delta h phi active hdelta hh hmeets).trans
      apply coordinateNeighborhood_pairedBarrier_subset_relaxed
        lower upper period
      · intro i
        exact (hperiodPos i).le
      · dsimp only [period, delta, h]
        exact sum_harperScheduled_shiftedLatticePeriod_le_one hstartSix
  have hraw := hpath shell start n y hstartPath hy hσ t ht s hs hsep
    (harperPairedPartialSumBarrierSet lower upper)
    (harperPairedRelaxedPartialSumBarrierSet lower upper)
    (measurableSet_harperPairedPartialSumBarrierSet lower upper)
    (by simpa only [delta, h] using hgeometry)
  apply le_four_mul_exp_four_of_harperScheduled_products
    (start := start) (n := n) hstartSix
    measureReal_nonneg measureReal_nonneg
  simpa only [harperPairedRelaxedPartialSumBarrierSet] using hraw


theorem candidate_exists_gap_rankinCenteredLogBallotSuffix_le_gaussianRelaxed :
    ∃ J : Nat, ∀ V : ℝ, 0 ≤ V → ∃ gap : Nat, ∀ shell baseStart d m y : Nat,
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
                    harperRankinTwoHeightPrimeBlockVectorLaw y
                      (Problem520.harperScheduledPrimeBlock y
                        (baseStart + d + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
                      (harperPairedPartialSumBarrierSet lower upper) ≤
                    4 * Real.exp 4 *
                      (Measure.pi (fun i : Fin m ↦
                        candidateRankinMatchedGaussianLaw y
                          (Problem520.harperScheduledPrimeBlock y
                            (baseStart + d + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
                        (harperPairedRelaxedPartialSumBarrierSet lower upper) := by
  obtain ⟨Jpath, hpath⟩ :=
    candidate_exists_gap_rankinPairedBarrier_le_gaussianRelaxed
  let J := max 30 Jpath
  refine ⟨J, ?_⟩
  intro V hV
  obtain ⟨gap, hpath⟩ := hpath V hV
  refine ⟨gap, ?_⟩
  intro shell baseStart d m y hstart hd hy hσ t ht s hs hsep u v hfull
  dsimp only
  have hbaseThirty : 30 ≤ baseStart :=
    (le_max_left 30 Jpath).trans hstart
  have hpathStart : Jpath + (shell + 1) ≤ baseStart + d := by
    have hJpath : Jpath ≤ baseStart :=
      (le_max_right 30 Jpath).trans hstart
    omega
  have hdPos : 0 < d := by omega
  let lower := harperPairedSuffixLower
    (harper1144LogBallotLowerBarrier baseStart (d + m)) u
  let upper := harperPairedSuffixUpper
    (harper1144LogBallotUpperBarrier (d + m)) u
  let R : Fin m → Real := fun i ↦
    128 * ((d + i.val + 1 : Nat) : Real) + 2
  apply hpath shell (baseStart + d) m y hpathStart (by
      simpa only [add_assoc] using hy) hσ t ht s hs hsep lower upper R
  · intro x hx i
    simpa only [lower, upper, R] using
      abs_coordinates_le_of_mem_harperPairedSuffix_logBallot
        hdPos u v hfull x hx i
  · intro i
    have hmod := harperScheduled_suffixEnvelope_le_moderateWindow
      hbaseThirty (d + i.val)
    dsimp only [R]
    rw [show
      2 * (128 * ((d + i.val + 1 : Nat) : Real) + 2) + 5 =
          256 * (((d + i.val + 1 : Nat) : Real)) + 9 by ring]
    simpa only [add_assoc] using hmod

end Erdos.Problem1144
