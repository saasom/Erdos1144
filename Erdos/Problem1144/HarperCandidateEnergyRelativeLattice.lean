import Erdos.Problem1144.HarperCandidateEnergyRelativeCell
import Erdos.Problem1144.HarperShiftedLatticeAveraging

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos.Problem1144

/-! Natural-coherence relative-cell products and Haar-phase path selection. -/

theorem candidate_exists_gap_rankinRelativeShiftedPairCell_le :
    ∃ J : Nat, ∀ V : ℝ, 0 ≤ V → ∃ gap : Nat, ∀ shell j y : Nat, J + (shell + 1) ≤ j →
      Problem520.harperBlockEndpoint (j + gap + 1) ≤ y →
        ∀ hσ : 0 ≤ 4 * V / Real.log (y : ℝ), ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ phi : UnitAddCircle × UnitAddCircle, ∀ z : Int × Int,
                let delta := Problem520.harperScheduledRelativeIntervalWidth j
                let h := harperScheduledBivariateExpansionRadius j
                let a := ((z.1 : Real) +
                    harperUnitPhaseRepresentative phi.1) *
                  harperShiftedLatticePeriod delta h
                let b := ((z.2 : Real) +
                    harperUnitPhaseRepresentative phi.2) *
                  harperShiftedLatticePeriod delta h
                |a| + |b| + 3 ≤
                    (1 / 16 : Real) *
                      Real.sqrt (((2 ^ j : Nat) : Real)) →
                  (1 - 2 / Real.sqrt
                      (Problem520.harperScheduledStrongComparisonFrequency j)) ^
                        (2 : Nat) *
                      (harperRankinTwoHeightPrimeBlockVectorLaw y
                        (Problem520.harperScheduledPrimeBlock y j) (4 * V / Real.log (y : ℝ)) hσ t s).real
                          (harperShiftedPairCoreCell delta h phi z) ≤
                    (1 + 2 * delta) *
                      (candidateRankinMatchedGaussianLaw y
                        (Problem520.harperScheduledPrimeBlock y j) (4 * V / Real.log (y : ℝ)) hσ t s).real
                          (harperShiftedPairFullCell delta h phi z) := by
  obtain ⟨J, hJ⟩ :=
    candidate_exists_gap_rankinRelativeRectangleProbability_le
  refine ⟨J, ?_⟩
  intro V hV
  obtain ⟨gap, hJ⟩ := hJ V hV
  refine ⟨gap, ?_⟩
  intro shell j y hj hy hσ t ht s hs hsep phi z
  dsimp only
  intro hmoderate
  let delta := Problem520.harperScheduledRelativeIntervalWidth j
  let h := harperScheduledBivariateExpansionRadius j
  let a := ((z.1 : Real) + harperUnitPhaseRepresentative phi.1) *
    harperShiftedLatticePeriod delta h
  let b := ((z.2 : Real) + harperUnitPhaseRepresentative phi.2) *
    harperShiftedLatticePeriod delta h
  have hlocal := hJ shell j y hj hy hσ t ht s hs hsep a b hmoderate
  simpa only [delta, h, a, b, harperShiftedPairCoreCell,
    harperShiftedPairFullCell, harperShiftedCoreCell,
    harperShiftedFullCell, harperScheduledBivariateExpansionRadius]
    using hlocal

/-- The local comparisons multiply and sum over any finite active family of
shifted path cells.  This is the path-composition theorem before the purely
geometric choice of the active family. -/
theorem candidate_exists_gap_rankinRelativeShiftedFiniteUnion_le :
    ∃ J : Nat, ∀ V : ℝ, 0 ≤ V → ∃ gap : Nat, ∀ shell start n y : Nat,
      J + (shell + 1) ≤ start →
      Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
        ∀ hσ : 0 ≤ 4 * V / Real.log (y : ℝ), ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ phi : Fin n → UnitAddCircle × UnitAddCircle,
                ∀ active : Finset (Fin n → Int × Int),
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
                        Real.sqrt (((2 ^ j : Nat) : Real))) →
                  let delta : Fin n → Real := fun i ↦
                    Problem520.harperScheduledRelativeIntervalWidth
                      (start + i.val)
                  let h : Fin n → Real := fun i ↦
                    harperScheduledBivariateExpansionRadius (start + i.val)
                  let retention : Fin n → Real := fun i ↦
                    (1 - 2 / Real.sqrt
                      (Problem520.harperScheduledStrongComparisonFrequency
                        (start + i.val))) ^ (2 : Nat)
                  let loss : Fin n → Real := fun i ↦
                    1 + 2 * Problem520.harperScheduledRelativeIntervalWidth
                      (start + i.val)
                  (∏ i, retention i) *
                    (Measure.pi (fun i : Fin n ↦
                      harperRankinTwoHeightPrimeBlockVectorLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (start + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
                      (⋃ z ∈ active,
                        harperShiftedPairPathCoreCell delta h phi z) ≤
                  (∏ i, loss i) *
                    (Measure.pi (fun i : Fin n ↦
                      candidateRankinMatchedGaussianLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (start + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real
                      (⋃ z ∈ active,
                        harperShiftedPairPathFullCell delta h phi z) := by
  obtain ⟨Jlocal, hlocal⟩ :=
    candidate_exists_gap_rankinRelativeShiftedPairCell_le
  let J := max 4 Jlocal
  refine ⟨J, ?_⟩
  intro V hV
  obtain ⟨gap, hlocal⟩ := hlocal V hV
  refine ⟨gap, ?_⟩
  intro shell start n y hstart hy hσ t ht s hs hsep phi active hmoderate
  dsimp only
  let delta : Fin n → Real := fun i ↦
    Problem520.harperScheduledRelativeIntervalWidth (start + i.val)
  let h : Fin n → Real := fun i ↦
    harperScheduledBivariateExpansionRadius (start + i.val)
  let retention : Fin n → Real := fun i ↦
    (1 - 2 / Real.sqrt
      (Problem520.harperScheduledStrongComparisonFrequency
        (start + i.val))) ^ (2 : Nat)
  let loss : Fin n → Real := fun i ↦
    1 + 2 * Problem520.harperScheduledRelativeIntervalWidth
      (start + i.val)
  have hjFour (i : Fin n) : 4 ≤ start + i.val := by
    dsimp only [J] at hstart
    omega
  have hretention (i : Fin n) : 0 ≤ retention i := by
    dsimp only [retention]
    positivity
  have hloss (i : Fin n) : 0 ≤ loss i := by
    dsimp only [loss]
    have hd := Problem520.harperScheduledRelativeIntervalWidth_pos
      (start + i.val)
    linarith
  have hperiod (i : Fin n) :
      0 < harperShiftedLatticePeriod (delta i) (h i) := by
    dsimp only [delta, h, harperShiftedLatticePeriod]
    have hd := Problem520.harperScheduledRelativeIntervalWidth_pos
      (start + i.val)
    have hh := harperScheduledBivariateExpansionRadius_pos (start + i.val)
    positivity
  apply measureReal_biUnion_shiftedPairPathCoreCell_le_prod_mul_fullCell
    (rho := fun i : Fin n ↦
      harperRankinTwoHeightPrimeBlockVectorLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)
    (nu := fun i : Fin n ↦
      candidateRankinMatchedGaussianLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)
    retention loss delta h phi active hretention hloss hperiod
  intro z hz i
  have hj : Jlocal + (shell + 1) ≤ start + i.val := by
    dsimp only [J] at hstart
    omega
  have hyi :
      Problem520.harperBlockEndpoint (start + i.val + gap + 1) ≤ y := by
    exact (Problem520.strictMono_harperBlockEndpoint.monotone (by omega)).trans hy
  have hm := hmoderate z hz i
  simpa only [delta, h, retention, loss, mul_assoc] using
    hlocal shell (start + i.val) y hj hyi hσ t ht s hs hsep (phi i) (z i) hm

/-- Haar phase selection plus the finite disjoint-cell comparison.  The only
remaining input is geometric: for every phase, exhibit a finite moderate
family whose core cells cover the selected part of `A` and whose full cells
lie in the Gaussian guard `G`. -/
theorem candidate_exists_gap_rankinRelativeShiftedPath_le :
    ∃ J : Nat, ∀ V : ℝ, 0 ≤ V → ∃ gap : Nat, ∀ shell start n y : Nat,
      J + (shell + 1) ≤ start →
      Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
        ∀ hσ : 0 ≤ 4 * V / Real.log (y : ℝ), ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ A G : Set (Fin n → Real × Real), MeasurableSet A →
                (∀ phi : Fin n → UnitAddCircle × UnitAddCircle,
                  ∃ active : Finset (Fin n → Int × Int),
                    A ∩ harperShiftedPairPathCoreSet
                      (fun i ↦
                        Problem520.harperScheduledRelativeIntervalWidth
                          (start + i.val))
                      (fun i ↦ harperScheduledBivariateExpansionRadius
                        (start + i.val)) phi ⊆
                      ⋃ z ∈ active, harperShiftedPairPathCoreCell
                        (fun i ↦
                          Problem520.harperScheduledRelativeIntervalWidth
                            (start + i.val))
                        (fun i ↦ harperScheduledBivariateExpansionRadius
                          (start + i.val)) phi z ∧
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
                    (⋃ z ∈ active, harperShiftedPairPathFullCell
                      (fun i ↦
                        Problem520.harperScheduledRelativeIntervalWidth
                          (start + i.val))
                      (fun i ↦ harperScheduledBivariateExpansionRadius
                        (start + i.val)) phi z) ⊆ G) →
                let delta : Fin n → Real := fun i ↦
                  Problem520.harperScheduledRelativeIntervalWidth
                    (start + i.val)
                let h : Fin n → Real := fun i ↦
                  harperScheduledBivariateExpansionRadius (start + i.val)
                let coreFraction : Fin n × Bool → Real := fun p ↦
                  delta p.1 /
                    harperShiftedLatticePeriod (delta p.1) (h p.1)
                let retention : Fin n → Real := fun i ↦
                  (1 - 2 / Real.sqrt
                    (Problem520.harperScheduledStrongComparisonFrequency
                      (start + i.val))) ^ (2 : Nat)
                let loss : Fin n → Real := fun i ↦
                  1 + 2 * Problem520.harperScheduledRelativeIntervalWidth
                    (start + i.val)
                ((∏ i, retention i) * (∏ p, coreFraction p)) *
                    (Measure.pi (fun i : Fin n ↦
                      harperRankinTwoHeightPrimeBlockVectorLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (start + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real A ≤
                  (∏ i, loss i) *
                    (Measure.pi (fun i : Fin n ↦
                      candidateRankinMatchedGaussianLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (start + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s)).real G := by
  obtain ⟨J, hfinite⟩ :=
    candidate_exists_gap_rankinRelativeShiftedFiniteUnion_le
  refine ⟨J, ?_⟩
  intro V hV
  obtain ⟨gap, hfinite⟩ := hfinite V hV
  refine ⟨gap, ?_⟩
  intro shell start n y hstart hy hσ t ht s hs hsep A G hA hgeometry
  dsimp only
  let delta : Fin n → Real := fun i ↦
    Problem520.harperScheduledRelativeIntervalWidth (start + i.val)
  let h : Fin n → Real := fun i ↦
    harperScheduledBivariateExpansionRadius (start + i.val)
  let coreFraction : Fin n × Bool → Real := fun p ↦
    delta p.1 / harperShiftedLatticePeriod (delta p.1) (h p.1)
  let retention : Fin n → Real := fun i ↦
    (1 - 2 / Real.sqrt
      (Problem520.harperScheduledStrongComparisonFrequency
        (start + i.val))) ^ (2 : Nat)
  let loss : Fin n → Real := fun i ↦
    1 + 2 * Problem520.harperScheduledRelativeIntervalWidth
      (start + i.val)
  let rho : Fin n → Measure (Real × Real) := fun i ↦
    harperRankinTwoHeightPrimeBlockVectorLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s
  let nu : Fin n → Measure (Real × Real) := fun i ↦
    candidateRankinMatchedGaussianLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) (4 * V / Real.log (y : ℝ)) hσ t s
  have hdelta (i : Fin n) : 0 ≤ delta i := by
    exact (Problem520.harperScheduledRelativeIntervalWidth_pos _).le
  have hh (i : Fin n) : 0 ≤ h i := by
    exact (harperScheduledBivariateExpansionRadius_pos _).le
  have hperiod (i : Fin n) :
      0 < harperShiftedLatticePeriod (delta i) (h i) := by
    dsimp only [delta, h, harperShiftedLatticePeriod]
    exact add_pos_of_pos_of_nonneg
      (Problem520.harperScheduledRelativeIntervalWidth_pos _)
      (mul_nonneg (by norm_num)
        (harperScheduledBivariateExpansionRadius_pos _).le)
  have hretention (i : Fin n) : 0 ≤ retention i := by
    dsimp only [retention]
    positivity
  have hretentionProd : 0 ≤ ∏ i, retention i :=
    Finset.prod_nonneg fun i _hi ↦ hretention i
  have hloss (i : Fin n) : 0 ≤ loss i := by
    dsimp only [loss]
    have hd := Problem520.harperScheduledRelativeIntervalWidth_pos
      (start + i.val)
    linarith
  have hlossProd : 0 ≤ ∏ i, loss i :=
    Finset.prod_nonneg fun i _hi ↦ hloss i
  obtain ⟨phi, hphase⟩ :=
    exists_pairPhase_measureReal_shiftedPathCoreSet_ge
      (Measure.pi rho) hA delta h hdelta hh hperiod
  obtain ⟨active, hcover, hmoderate, hfull⟩ := hgeometry phi
  have hselected :
      (Measure.pi rho).real
          (A ∩ harperShiftedPairPathCoreSet delta h phi) ≤
        (Measure.pi rho).real
          (⋃ z ∈ active,
            harperShiftedPairPathCoreCell delta h phi z) :=
    measureReal_mono hcover (measure_ne_top _ _)
  have hcompare :=
    hfinite shell start n y hstart hy hσ t ht s hs hsep phi active hmoderate
  change
    ((∏ i, retention i) * (∏ p, coreFraction p)) *
        (Measure.pi rho).real A ≤
      (∏ i, loss i) * (Measure.pi nu).real G
  calc
    ((∏ i, retention i) * (∏ p, coreFraction p)) *
          (Measure.pi rho).real A =
        (∏ i, retention i) *
          ((∏ p, coreFraction p) * (Measure.pi rho).real A) := by ring
    _ ≤ (∏ i, retention i) *
          (Measure.pi rho).real
            (A ∩ harperShiftedPairPathCoreSet delta h phi) := by
      exact mul_le_mul_of_nonneg_left hphase hretentionProd
    _ ≤ (∏ i, retention i) *
          (Measure.pi rho).real
            (⋃ z ∈ active,
              harperShiftedPairPathCoreCell delta h phi z) := by
      exact mul_le_mul_of_nonneg_left hselected hretentionProd
    _ ≤ (∏ i, loss i) *
          (Measure.pi nu).real
            (⋃ z ∈ active,
              harperShiftedPairPathFullCell delta h phi z) := by
      simpa only [rho, nu, delta, h, retention, loss] using hcompare
    _ ≤ (∏ i, loss i) * (Measure.pi nu).real G := by
      exact mul_le_mul_of_nonneg_left
        (measureReal_mono hfull (measure_ne_top _ _)) hlossProd


end Erdos.Problem1144
