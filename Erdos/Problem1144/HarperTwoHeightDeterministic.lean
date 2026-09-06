import Erdos.Problem1144.HarperTwoHeightTilt

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Deterministic estimates after two-height prefix cancellation

The simultaneous ballot probability has already been removed in
`HarperTwoHeightTilt`.  This module bounds the deterministic likelihood cost
of the removed prefix and prepares the complementary correlation for the
remaining separation-strip argument.
-/

/-- The scheduled vertical drift differs from the diagonal mean of the same
prime prefix by an absolute constant.  This is just the summable mesh error;
it contains no probability estimate. -/
theorem exists_harperScheduledVerticalCumulativeDrift_diagonal_close :
    ∃ J : Nat, ∀ start n y : Nat, J ≤ start →
      Problem520.harperBlockEndpoint (start + n) ≤ y →
        ∀ t : Real, ∀ k : Fin n,
          |Problem520.harperScheduledVerticalCumulativeDrift
                y start n t k -
              Problem520.harperLogMainBlockMean y
                (Problem520.harperScheduledPrimeRangeFrom
                  y start (k.val + 1)) t t| ≤
            (9 / 64 : Real) := by
  obtain ⟨J, hperturb⟩ :=
    Problem520.exists_harperScheduledMovingHeightMainMeanPerturbation
  refine ⟨J, ?_⟩
  intro start n y hstart hy t k
  have hyi : ∀ i : Fin n,
      Problem520.harperBlockEndpoint (start + (i : Nat) + 1) ≤ y := by
    intro i
    exact (Problem520.monotone_harperBlockEndpoint (by omega)).trans hy
  have hpoint : ∀ i : Fin n,
      |Problem520.harperScheduledMainMeanVectorVarying y start n t
            (Problem520.harperScheduledVerticalCheckpoint start n t) i -
          Problem520.harperLogMainBlockMean y
            (Problem520.harperScheduledPrimeBlock y
              (start + (i : Nat))) t t| ≤
        (9 / 2 : Real) *
          ((1 : Real) / (64 * ((((i.val + 1 : Nat) : Real) ^ 2)))) := by
    intro i
    simpa only [Problem520.harperScheduledMainMeanVectorVarying] using
      hperturb 0 (start + (i : Nat)) y (by simpa using (show
        J ≤ start + (i : Nat) by omega)) (hyi i)
        t (Problem520.harperScheduledVerticalCheckpoint start n t i)
        ((1 : Real) / (64 * ((((i.val + 1 : Nat) : Real) ^ 2))))
        (by positivity)
        (Problem520.harperScheduledVerticalCheckpoint_refinedOffDiagonalCondition
          start n t i)
  have hsum :
      |(∑ i ∈ Finset.Iic k,
          Problem520.harperScheduledMainMeanVectorVarying y start n t
            (Problem520.harperScheduledVerticalCheckpoint start n t) i) -
          ∑ i ∈ Finset.Iic k,
            Problem520.harperLogMainBlockMean y
              (Problem520.harperScheduledPrimeBlock y
                (start + (i : Nat))) t t| ≤
        (9 / 64 : Real) := by
    calc
      |(∑ i ∈ Finset.Iic k,
          Problem520.harperScheduledMainMeanVectorVarying y start n t
            (Problem520.harperScheduledVerticalCheckpoint start n t) i) -
          ∑ i ∈ Finset.Iic k,
            Problem520.harperLogMainBlockMean y
              (Problem520.harperScheduledPrimeBlock y
                (start + (i : Nat))) t t| =
          |∑ i ∈ Finset.Iic k,
            (Problem520.harperScheduledMainMeanVectorVarying y start n t
                (Problem520.harperScheduledVerticalCheckpoint start n t) i -
              Problem520.harperLogMainBlockMean y
                (Problem520.harperScheduledPrimeBlock y
                  (start + (i : Nat))) t t)| := by
            rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i ∈ Finset.Iic k,
          |Problem520.harperScheduledMainMeanVectorVarying y start n t
              (Problem520.harperScheduledVerticalCheckpoint start n t) i -
            Problem520.harperLogMainBlockMean y
              (Problem520.harperScheduledPrimeBlock y
                (start + (i : Nat))) t t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Iic k,
          (9 / 2 : Real) *
            ((1 : Real) / (64 * ((((i.val + 1 : Nat) : Real) ^ 2)))) :=
          Finset.sum_le_sum fun i _hi => hpoint i
      _ = (9 / 2 : Real) *
          (∑ i ∈ Finset.Iic k,
            ((1 : Real) / (64 * ((((i.val + 1 : Nat) : Real) ^ 2))))) := by
          rw [Finset.mul_sum]
      _ ≤ (9 / 2 : Real) * (1 / 32 : Real) :=
          mul_le_mul_of_nonneg_left
            (Problem520.sum_Iic_harperScheduledVerticalScaleBudget_le_one_thirtyTwo k)
            (by norm_num)
      _ = (9 / 64 : Real) := by norm_num
  have hrange :
      (∑ i ∈ Finset.Iic k,
          Problem520.harperLogMainBlockMean y
            (Problem520.harperScheduledPrimeBlock y
              (start + (i : Nat))) t t) =
        Problem520.harperLogMainBlockMean y
          (Problem520.harperScheduledPrimeRangeFrom
            y start (k.val + 1)) t t := by
    rw [Problem520.sum_Iic_eq_sum_fin_prefix
      (fun q => Problem520.harperLogMainBlockMean y
        (Problem520.harperScheduledPrimeBlock y (start + q)) t t) k]
    rw [show
      (∑ i : Fin (k.val + 1),
          Problem520.harperLogMainBlockMean y
            (Problem520.harperScheduledPrimeBlock y
              (start + (i : Nat))) t t) =
        ∑ q ∈ Finset.range (k.val + 1),
          Problem520.harperLogMainBlockMean y
            (Problem520.harperScheduledPrimeBlock y (start + q)) t t by
      simpa using (Fin.sum_univ_eq_sum_range
        (fun q : Nat => Problem520.harperLogMainBlockMean y
          (Problem520.harperScheduledPrimeBlock y (start + q)) t t)
        (k.val + 1))]
    exact Problem520.sum_harperLogMainBlockMean_eq_rangeFrom
      y start (k.val + 1) t t
  unfold Problem520.harperScheduledVerticalCumulativeDrift
  rw [hrange] at hsum
  exact hsum

/-- Reciprocal mass is additive over the consecutive scheduled prime union. -/
theorem sum_inv_harperScheduledPrimeRangeFrom_eq
    (y start m : Nat) :
    (∑ p ∈ Problem520.harperScheduledPrimeRangeFrom y start m,
        (p.1 : Real)⁻¹) =
      ∑ i : Fin m,
        Problem520.harperScheduledReciprocalMass y
          (start + (i : Nat)) := by
  unfold Problem520.harperScheduledPrimeRangeFrom
    Problem520.harperScheduledReciprocalMass
  rw [Finset.sum_biUnion
    (Problem520.pairwiseDisjoint_harperScheduledPrimeBlock_add
      y start m)]
  exact (Fin.sum_univ_eq_sum_range
    (fun i : Nat =>
      ∑ p ∈ Problem520.harperScheduledPrimeBlock y (start + i),
        (p.1 : Real)⁻¹) m).symm

/-- The exact prefix likelihood exponent grows by only `log 2` per scheduled
block, up to one absolute additive constant.  This is the sharp deterministic
cancellation needed before the separation-strip estimate. -/
theorem exists_harperCentralPrefixLikelihoodExponent_le :
    ∃ C ≥ 0, ∃ J : Nat,
      ∀ start n y : Nat, J + 1 ≤ start →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
          ∀ s ∈ harperLowerVerticalBand, ∀ k : Fin n,
            let P := Problem520.harperScheduledPrimeRangeFrom
              y start (k.val + 1)
            let R := (4 / 3 : Real) *
              (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
            let Q := ∑ p ∈ P,
              let x : Real := (p.1 : Real)⁻¹
              x - x ^ (2 : Nat)
            2 * (3 +
                Problem520.harperLogMainBlockMean y P s s + R) - Q ≤
              ((k.val + 1 : Nat) : Real) * Real.log 2 + C := by
  obtain ⟨K, hK, Jdrift, hdrift⟩ :=
    Problem520.exists_harperScheduledCentralBandVerticalCumulativeDrift_constant_bound
  obtain ⟨Jmesh, hmesh⟩ :=
    exists_harperScheduledVerticalCumulativeDrift_diagonal_close
  let C : Real := 10 + 3 * K
  let J := max Jdrift Jmesh
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, J, ?_⟩
  intro start n y hstart hy s hs k
  dsimp only
  let m : Nat := k.val + 1
  let P := Problem520.harperScheduledPrimeRangeFrom y start m
  let R : Real := (4 / 3 : Real) *
    (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
  let Q : Real := ∑ p ∈ P,
    let x : Real := (p.1 : Real)⁻¹
    x - x ^ (2 : Nat)
  let T : Real := ∑ i ∈ Finset.Iic k,
    Problem520.harperScheduledReciprocalMass y (start + (i : Nat))
  let V : Real := Problem520.harperScheduledVerticalCumulativeDrift
    y start n s k
  let M : Real := Problem520.harperLogMainBlockMean y P s s
  have hstartDrift : Jdrift + 1 ≤ start := by
    have : Jdrift ≤ J := le_max_left _ _
    omega
  have hstartMesh : Jmesh ≤ start := by
    have : Jmesh ≤ J := le_max_right _ _
    omega
  have hs' : (1 / 3 : Real) ≤ s ∧ s ≤ 1 / 2 := hs
  have hsNonneg : 0 ≤ s := by linarith
  have habs : |s| = s := abs_of_nonneg hsNonneg
  have hsLower : (1 / 2 : Real) ^ (1 + 1) < |s| := by
    rw [habs]
    norm_num
    linarith
  have hsUpper : |s| ≤ (1 / 2 : Real) ^ 1 := by
    rw [habs]
    norm_num
    exact hs'.2
  have hcentral := hdrift 1 start n y hstartDrift hy s
    hsLower hsUpper k
  have hT : |T - (m : Real) * Real.log 2| ≤ K := by
    simpa only [T, m] using hcentral.1
  have hV : |V - (m : Real) * Real.log 2| ≤ K := by
    simpa only [V, m] using hcentral.2
  have hVM : |V - M| ≤ (9 / 64 : Real) := by
    simpa only [V, M, P, m] using
      hmesh start n y hstartMesh hy s k
  have hMupper : M ≤ (m : Real) * Real.log 2 + K + 9 / 64 := by
    have hVupper := le_of_abs_le hV
    have hdiff := neg_le_of_abs_le hVM
    linarith
  have hTlower : (m : Real) * Real.log 2 - K ≤ T := by
    linarith [neg_le_of_abs_le hT]
  have hTP :
      (∑ p ∈ P, (p.1 : Real)⁻¹) = T := by
    rw [sum_inv_harperScheduledPrimeRangeFrom_eq y start m]
    rw [← Problem520.sum_Iic_eq_sum_fin_prefix
      (fun q => Problem520.harperScheduledReciprocalMass y (start + q)) k]
  have hSq :
      (∑ p ∈ P, (p.1 : Real)⁻¹ ^ (2 : Nat)) ≤ 1 := by
    calc
      (∑ p ∈ P, (p.1 : Real)⁻¹ ^ (2 : Nat)) ≤
          ∑ p : Problem520.HarperPrimeIndex y,
            (p.1 : Real)⁻¹ ^ (2 : Nat) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg P.subset_univ
          (fun p _hp _hnot => by positivity)
      _ = harperPrimeSquareBudget y := by
        rfl
      _ ≤ 1 := harperPrimeSquareBudget_le_one y
  have hQeq :
      Q = (∑ p ∈ P, (p.1 : Real)⁻¹) -
        ∑ p ∈ P, (p.1 : Real)⁻¹ ^ (2 : Nat) := by
    dsimp [Q]
    rw [Finset.sum_sub_distrib]
  have hQlower : (m : Real) * Real.log 2 - K - 1 ≤ Q := by
    rw [hQeq, hTP]
    linarith
  have hR : R ≤ 4 / 3 := by
    simpa only [R, Problem520.harperScheduledLogTaylorAllowance] using
      Problem520.harperScheduledLogTaylorAllowance_le_four_thirds start
  change 2 * (3 + M + R) - Q ≤
    (m : Real) * Real.log 2 + C
  dsimp [C]
  linarith

/-- Exponential form of the preceding estimate: a ballot prefix of `m`
scheduled blocks costs at most an absolute constant times `2^m`. -/
theorem exists_harperCentralPrefixLikelihoodBudget_le_powTwo :
    ∃ B > 0, ∃ J : Nat,
      ∀ start n y : Nat, J + 1 ≤ start →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
          ∀ s ∈ harperLowerVerticalBand, ∀ k : Fin n,
            let P := Problem520.harperScheduledPrimeRangeFrom
              y start (k.val + 1)
            let R := (4 / 3 : Real) *
              (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
            let Q := ∑ p ∈ P,
              let x : Real := (p.1 : Real)⁻¹
              x - x ^ (2 : Nat)
            Real.exp
                (2 * (3 +
                  Problem520.harperLogMainBlockMean y P s s + R) - Q) ≤
              B * (2 : Real) ^ (k.val + 1) := by
  obtain ⟨C, hC, J, hbound⟩ :=
    exists_harperCentralPrefixLikelihoodExponent_le
  refine ⟨Real.exp C, Real.exp_pos C, J, ?_⟩
  intro start n y hstart hy s hs k
  have h := hbound start n y hstart hy s hs k
  dsimp only at h ⊢
  calc
    Real.exp
        (2 * (3 + Problem520.harperLogMainBlockMean y
          (Problem520.harperScheduledPrimeRangeFrom
            y start (k.val + 1)) s s +
          (4 / 3 : Real) *
            (Real.sqrt
              (Problem520.harperBlockEndpoint start : Real))⁻¹) -
          ∑ p ∈ Problem520.harperScheduledPrimeRangeFrom
              y start (k.val + 1),
            ((p.1 : Real)⁻¹ - (p.1 : Real)⁻¹ ^ (2 : Nat))) ≤
      Real.exp (((k.val + 1 : Nat) : Real) * Real.log 2 + C) :=
        Real.exp_le_exp.mpr h
    _ = Real.exp C * (2 : Real) ^ (k.val + 1) := by
      rw [Real.exp_add]
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : Real) < 2)]
      ring

/-- Pointwise deterministic endpoint after prefix cancellation.  The random
simultaneous-ballot term is gone, and its entire cost is `B * 2^m`; only the
correlation on the complementary primes remains. -/
theorem exists_harperCentralLowerBallot_correlation_probability_le_powTwo_compl :
    ∃ B > 0, ∃ J : Nat,
      ∀ start n y : Nat, J + 1 ≤ start →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand, ∀ k : Fin n,
              let P := Problem520.harperScheduledPrimeRangeFrom
                y start (k.val + 1)
              harperTwoHeightCorrelation y t s *
                  (harperTwoHeightCubeLaw y t s).real
                    (harperCentralLowerBallotCubeEvent y start n t ∩
                      harperCentralLowerBallotCubeEvent y start n s) ≤
                B * (2 : Real) ^ (k.val + 1) *
                  harperSubsetCorrelation y Pᶜ t s := by
  obtain ⟨B, hB, J, hbudget⟩ :=
    exists_harperCentralPrefixLikelihoodBudget_le_powTwo
  refine ⟨B, hB, J, ?_⟩
  intro start n y hstart hy t ht s hs k
  dsimp only
  have hpoint :=
    harperCentralLowerBallot_correlation_probability_le_prefix
      y start n t s k
  have hcost := hbudget start n y hstart hy s hs k
  dsimp only at hpoint hcost
  exact hpoint.trans (mul_le_mul_of_nonneg_right hcost
    (harperSubsetCorrelation_pos y
      (Problem520.harperScheduledPrimeRangeFrom
        y start (k.val + 1))ᶜ t s).le)

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.exists_harperScheduledVerticalCumulativeDrift_diagonal_close
#print axioms Erdos.Problem1144.exists_harperCentralPrefixLikelihoodExponent_le
#print axioms Erdos.Problem1144.exists_harperCentralPrefixLikelihoodBudget_le_powTwo
#print axioms Erdos.Problem1144.exists_harperCentralLowerBallot_correlation_probability_le_powTwo_compl
