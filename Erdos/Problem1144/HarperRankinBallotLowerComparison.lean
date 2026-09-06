import Erdos.Problem1144.HarperRankinScheduledCDF
import Erdos.Problem1144.HarperBallotLowerComparison

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Lower ballot comparison for the Rankin-shifted walk

After discarding the fixed terminal gap needed to retain the shifted
variance, the Rankin-centered blocks obey the same reverse lattice-cell
comparison as the critical-line blocks.  The existing finite-slicing
argument then transfers the contracted Gaussian corridor with the same
fixed factor `3 / 4`.
-/

/-- On every sufficiently late moderate cell, a Rankin-shifted scheduled
block has at least `1 - (j+1)⁻²` times the mass of its variance-matched
Gaussian cell.  The only new loss is the fixed terminal gap that stabilizes
the shifted variance. -/
theorem
    exists_gap_one_sub_width_mul_gaussian_le_harperRankinScheduledCentralBandIntervalProbability
    (V : ℝ) (hV : 0 ≤ V) :
    ∃ gap J : ℕ, ∀ d j y : ℕ, J + d ≤ j →
      Problem520.harperBlockEndpoint (j + gap + 1) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            ∀ b : ℝ,
              |b| + 1 ≤ (1 / 4 : ℝ) *
                Real.sqrt (((2 ^ j : ℕ) : ℝ)) →
              (1 - Problem520.harperScheduledRelativeIntervalWidth j) *
                  (harperRankinGaussianBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y j)
                    (4 * V / Real.log (y : ℝ)) t t).real
                      (Ioc b
                        (b + Problem520.harperScheduledRelativeIntervalWidth j)) ≤
                (harperRankinCenteredLinearBlockLaw y
                  (Problem520.harperScheduledPrimeBlock y j)
                  (4 * V / Real.log (y : ℝ)) t t).real
                    (Ioc b
                      (b + Problem520.harperScheduledRelativeIntervalWidth j)) := by
  obtain ⟨gap, Jvar, hvar⟩ :=
    exists_gap_harperRankinScheduledCentralBandVarianceWindow V hV
  obtain ⟨Jbudget, hbudget⟩ := eventually_atTop.1
    Problem520.eventually_harperScheduledStrongBudget_le_width_mul_relativeGaussianMass
  refine ⟨gap, max Jvar Jbudget, ?_⟩
  intro d j y hj hy t htLower htUpper b hb
  have hjvar : Jvar + d ≤ j := by omega
  have hjbudget : Jbudget ≤ j := by omega
  have hyOne : 1 < y := by
    have hbase := Problem520.harperBlockEndpoint_ge_sixteen (j + gap + 1)
    omega
  have ha : 0 ≤ 4 * V / Real.log (y : ℝ) := by positivity
  have hvariance := hvar d j y hjvar hy t htLower htUpper
  let rho := harperRankinCenteredLinearBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j)
    (4 * V / Real.log (y : ℝ)) t t
  let nu := harperRankinGaussianBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j)
    (4 * V / Real.log (y : ℝ)) t t
  let delta := Problem520.harperScheduledRelativeIntervalWidth j
  have hdist : Problem520.harperCDFDistance rho nu ≤
      130 / Problem520.harperScheduledStrongComparisonFrequency j := by
    simpa only [rho, nu] using
      harperRankinScheduledBlockCDFDistance_le_strong y j ha t t hvariance.1
  have habs : |rho.real (Ioc b (b + delta)) -
      nu.real (Ioc b (b + delta))| ≤
        2 * Problem520.harperCDFDistance rho nu :=
    Problem520.abs_measureReal_Ioc_sub_le_two_mul_cdfDistance rho nu
      (by dsimp [delta]; linarith
        [Problem520.harperScheduledRelativeIntervalWidth_pos j])
  have hgaussian :
      (delta / 2) * Real.exp (-2 * (|b| + 1) ^ 2) ≤
        nu.real (Ioc b (b + delta)) := by
    dsimp only [nu, harperRankinGaussianBlockLaw]
    exact Problem520.gaussianReal_real_Ioc_ge_of_variance_quarter_half
      (v := harperRankinLinearBlockVarianceNNReal y
        (Problem520.harperScheduledPrimeBlock y j)
        (4 * V / Real.log (y : ℝ)) t t)
      (by simpa only [coe_harperRankinLinearBlockVarianceNNReal] using
        hvariance.1.le)
      (by
        simpa only [coe_harperRankinLinearBlockVarianceNNReal] using
          hvariance.2.le.trans (by norm_num : (3 / 8 : ℝ) ≤ 1 / 2))
      (by simpa only [delta] using
        Problem520.harperScheduledRelativeIntervalWidth_pos j)
      (by simpa only [delta] using
        Problem520.harperScheduledRelativeIntervalWidth_le_one j)
  have hbudgetj := hbudget j hjbudget b hb
  have herr : nu.real (Ioc b (b + delta)) -
      rho.real (Ioc b (b + delta)) ≤
        delta * nu.real (Ioc b (b + delta)) := by
    calc
      nu.real (Ioc b (b + delta)) - rho.real (Ioc b (b + delta)) ≤
          |rho.real (Ioc b (b + delta)) -
            nu.real (Ioc b (b + delta))| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      _ ≤ 2 * Problem520.harperCDFDistance rho nu := habs
      _ ≤ 2 * (130 /
          Problem520.harperScheduledStrongComparisonFrequency j) := by gcongr
      _ = 260 /
          Problem520.harperScheduledStrongComparisonFrequency j := by ring
      _ ≤ delta * ((delta / 2) *
          Real.exp (-2 * (|b| + 1) ^ 2)) := by
        simpa only [delta] using hbudgetj
      _ ≤ delta * nu.real (Ioc b (b + delta)) := by
        gcongr
        exact (Problem520.harperScheduledRelativeIntervalWidth_pos j).le
  dsimp only [rho, nu, delta] at herr ⊢
  linarith

/-- Uniform reverse comparison on every moderate product lattice cell for
the Rankin-shifted central-band walk. -/
theorem
    exists_gap_three_fourths_mul_gaussian_le_harperRankinScheduledCentralBandModerateCoordinateCell
    (V : ℝ) (hV : 0 ≤ V) :
    ∃ gap J : ℕ, ∀ d start : ℕ, J + d ≤ start → ∀ n y : ℕ,
      Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            ∀ z : Fin n → ℤ,
              (∀ i : Fin n,
                |(z i : ℝ) *
                    Problem520.harperScheduledRelativeIntervalWidth
                      (start + (i : ℕ))| + 1 ≤
                  (1 / 4 : ℝ) *
                    Real.sqrt (((2 ^ (start + (i : ℕ)) : ℕ) : ℝ))) →
              (3 / 4 : ℝ) *
                  (Measure.pi (fun i : Fin n =>
                    harperRankinGaussianBlockLaw y
                      (Problem520.harperScheduledPrimeBlock y
                        (start + (i : ℕ)))
                      (4 * V / Real.log (y : ℝ)) t t)).real
                    (Problem520.harperLatticeIocCell
                      (fun i : Fin n =>
                        Problem520.harperScheduledRelativeIntervalWidth
                          (start + (i : ℕ))) z) ≤
                (Measure.pi (fun i : Fin n =>
                  harperRankinCenteredLinearBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + (i : ℕ)))
                    (4 * V / Real.log (y : ℝ)) t t)).real
                  (Problem520.harperLatticeIocCell
                    (fun i : Fin n =>
                      Problem520.harperScheduledRelativeIntervalWidth
                        (start + (i : ℕ))) z) := by
  obtain ⟨gap, Jlocal, hlocal⟩ :=
    exists_gap_one_sub_width_mul_gaussian_le_harperRankinScheduledCentralBandIntervalProbability
      V hV
  refine ⟨gap, max Jlocal 4, ?_⟩
  intro d start hstart n y hy t htLower htUpper z hz
  have hstartLocal : Jlocal + d ≤ start := by omega
  have hstartFour : 4 ≤ start := by omega
  let rho : Fin n → Measure ℝ := fun i =>
    harperRankinCenteredLinearBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
      (4 * V / Real.log (y : ℝ)) t t
  let nu : Fin n → Measure ℝ := fun i =>
    harperRankinGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
      (4 * V / Real.log (y : ℝ)) t t
  let delta : Fin n → ℝ := fun i =>
    Problem520.harperScheduledRelativeIntervalWidth (start + (i : ℕ))
  have hendpoint (i : Fin n) :
      Problem520.harperBlockEndpoint
          (start + (i : ℕ) + gap + 1) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans hy
  have hcoord (i : Fin n) :
      (1 - delta i) *
          (nu i).real (Ioc ((z i : ℝ) * delta i)
            ((z i : ℝ) * delta i + delta i)) ≤
        (rho i).real (Ioc ((z i : ℝ) * delta i)
          ((z i : ℝ) * delta i + delta i)) := by
    exact hlocal d (start + (i : ℕ)) y (by omega) (hendpoint i)
      t htLower htUpper ((z i : ℝ) * delta i)
      (by simpa only [delta] using hz i)
  rw [Problem520.harperLatticeIocCell,
    Problem520.measureReal_pi_harperCoordinateIocCell,
    Problem520.measureReal_pi_harperCoordinateIocCell]
  have hprodCoord :
      (∏ i : Fin n, (1 - delta i) *
        (nu i).real (Ioc ((z i : ℝ) * delta i)
          ((z i : ℝ) * delta i + delta i))) ≤
        ∏ i : Fin n,
          (rho i).real (Ioc ((z i : ℝ) * delta i)
            ((z i : ℝ) * delta i + delta i)) := by
    exact Finset.prod_le_prod
      (fun i _hi => mul_nonneg
        (sub_nonneg.mpr
          (Problem520.harperScheduledRelativeIntervalWidth_le_one _))
        measureReal_nonneg)
      (fun i _hi => hcoord i)
  have hfactor : (3 / 4 : ℝ) ≤ ∏ i : Fin n, (1 - delta i) := by
    simpa only [delta] using
      three_fourths_le_prod_one_sub_harperScheduledRelativeIntervalWidth
        start n hstartFour
  have hnuNonneg : 0 ≤ ∏ i : Fin n,
      (nu i).real (Ioc ((z i : ℝ) * delta i)
        ((z i : ℝ) * delta i + delta i)) :=
    Finset.prod_nonneg fun i _hi => measureReal_nonneg
  calc
    (3 / 4 : ℝ) * ∏ i : Fin n,
        (nu i).real (Ioc ((z i : ℝ) * delta i)
          ((z i : ℝ) * delta i + delta i)) ≤
        (∏ i : Fin n, (1 - delta i)) *
          ∏ i : Fin n, (nu i).real
            (Ioc ((z i : ℝ) * delta i)
              ((z i : ℝ) * delta i + delta i)) :=
      mul_le_mul_of_nonneg_right hfactor hnuNonneg
    _ = ∏ i : Fin n, (1 - delta i) *
        (nu i).real (Ioc ((z i : ℝ) * delta i)
          ((z i : ℝ) * delta i + delta i)) := by
      rw [Finset.prod_mul_distrib]
    _ ≤ _ := hprodCoord

/-- Reverse finite-slicing comparison for the full shifted path. -/
theorem
    exists_gap_three_fourths_mul_gaussian_contractedBarrier_le_harperRankinScheduledCentralBandBarrier
    (V : ℝ) (hV : 0 ≤ V) :
    ∃ gap J : ℕ, ∀ d start : ℕ, J + d ≤ start → ∀ n y : ℕ,
      Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            ∀ lower upper : Fin n → ℝ,
              (3 / 4 : ℝ) *
                  (Measure.pi (fun i : Fin n =>
                    harperRankinGaussianBlockLaw y
                      (Problem520.harperScheduledPrimeBlock y
                        (start + (i : ℕ)))
                      (4 * V / Real.log (y : ℝ)) t t)).real
                    (Problem520.harperPartialSumBarrierSet
                        (fun k => lower k +
                          Problem520.harperCumulativeCellWidth
                            (Problem520.harperScheduledRelativeCellWidth
                              start n) k)
                        (fun k => upper k -
                          Problem520.harperCumulativeCellWidth
                            (Problem520.harperScheduledRelativeCellWidth
                              start n) k) ∩
                      Problem520.harperCoordinateBox
                        (Problem520.harperScheduledModerateRadius start n)) ≤
                (Measure.pi (fun i : Fin n =>
                  harperRankinCenteredLinearBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + (i : ℕ)))
                    (4 * V / Real.log (y : ℝ)) t t)).real
                  (Problem520.harperPartialSumBarrierSet lower upper) := by
  obtain ⟨gap, Jcell, hcell⟩ :=
    exists_gap_three_fourths_mul_gaussian_le_harperRankinScheduledCentralBandModerateCoordinateCell
      V hV
  refine ⟨gap, Jcell, ?_⟩
  intro d start hstart n y hy t htLower htUpper lower upper
  let delta := Problem520.harperScheduledRelativeCellWidth start n
  let R := Problem520.harperScheduledModerateRadius start n
  let lower' : Fin n → ℝ := fun k =>
    lower k + Problem520.harperCumulativeCellWidth delta k
  let upper' : Fin n → ℝ := fun k =>
    upper k - Problem520.harperCumulativeCellWidth delta k
  apply const_mul_measureReal_inter_contractedBarrier_box_le_barrier
    (P := Measure.pi (fun i : Fin n =>
      harperRankinCenteredLinearBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
        (4 * V / Real.log (y : ℝ)) t t))
    (Q := Measure.pi (fun i : Fin n =>
      harperRankinGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
        (4 * V / Real.log (y : ℝ)) t t))
    (C := (3 / 4 : ℝ)) (delta := delta) (R := R)
    (lower := lower) (upper := upper) (by norm_num)
    (Problem520.harperScheduledRelativeCellWidth_pos start n)
  intro z hz
  apply hcell d start hstart n y hy t htLower htUpper z
  intro i
  have hmoderate :=
    Problem520.abs_scheduledLatticeCell_lowerCorner_add_one_le_of_mem_activeSlice
      (start := start) (n := n) (lower := lower') (upper := upper')
      (by simpa only [delta, R, lower', upper'] using hz) i
  simpa only [Problem520.harperScheduledRelativeCellWidth,
    Problem520.harperScheduledModerateThreshold] using hmoderate

#print axioms
  Erdos.Problem1144.exists_gap_one_sub_width_mul_gaussian_le_harperRankinScheduledCentralBandIntervalProbability
#print axioms
  Erdos.Problem1144.exists_gap_three_fourths_mul_gaussian_le_harperRankinScheduledCentralBandModerateCoordinateCell
#print axioms
  Erdos.Problem1144.exists_gap_three_fourths_mul_gaussian_contractedBarrier_le_harperRankinScheduledCentralBandBarrier

end

end Problem1144
end Erdos
