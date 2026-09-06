import Erdos.Problem1144.HarperCandidateEnergyReverseUniform
import Erdos.Problem1144.HarperCandidateEnergyNormalizerGraph

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

namespace Erdos.Problem1144
noncomputable section

/-- Absolute-start form of the actual shifted lower ballot estimate. -/
theorem candidate_exists_uniform_start_rankinLogBallot_product_lower
    :
    ∃ J : ℕ, ∀ V : ℝ, 0 ≤ V → ∃ gap : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n →
      ∀ y : ℕ,
        Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            (3 / 16 : ℝ) *
                Real.exp
                  (-2 - harper1144GaussianLogFenceCertificateBudget) /
                  Real.sqrt (n : ℝ) ≤
              (Measure.pi (fun i : Fin n =>
                harperRankinCenteredLinearBlockLaw y
                  (Problem520.harperScheduledPrimeBlock y
                    (start + (i : ℕ)))
                  (4 * V / Real.log (y : ℝ)) t t)).real
                (Problem520.harperPartialSumBarrierSet
                  (harper1144LogBallotLowerBarrier start n)
                  (harper1144LogBallotUpperBarrier n)) := by
  obtain ⟨Jtransfer, htransfer⟩ := candidate_exists_uniform_start_rankinReverseBarrier
  obtain ⟨Jvar, hvar⟩ := candidate_exists_uniform_start_rankinVarianceWindow
  let J : ℕ := max 30 (max (Jtransfer + 1) (Jvar + 1))
  refine ⟨J, ?_⟩
  intro V hV
  obtain ⟨gapTransfer, htransfer⟩ := htransfer V hV
  obtain ⟨gapVar, hvar⟩ := hvar V hV
  let gap := max gapTransfer gapVar
  refine ⟨gap, ?_⟩
  intro start hstart n hn y hy t ht
  have hstart30 : 30 ≤ start :=
    (le_max_left 30 (max (Jtransfer + 1) (Jvar + 1))).trans hstart
  have hstartTransfer : Jtransfer + 1 ≤ start :=
    (le_max_of_le_right
      (le_max_left (Jtransfer + 1) (Jvar + 1))).trans hstart
  have hstartVar : Jvar + 1 ≤ start :=
    (le_max_of_le_right
      (le_max_right (Jtransfer + 1) (Jvar + 1))).trans hstart
  have hyTransfer :
      Problem520.harperBlockEndpoint (start + n + gapTransfer) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (by
      dsimp only [gap]
      omega)).trans hy
  have htBounds : (1 / 3 : ℝ) ≤ t ∧ t ≤ (1 / 2 : ℝ) := ht
  have htPositive : 0 < t := by linarith
  have htLower : (1 / 2 : ℝ) ^ (1 + 1) < |t| := by
    rw [abs_of_pos htPositive]
    norm_num
    linarith
  have htUpper : |t| ≤ (1 / 2 : ℝ) ^ (1 : ℕ) := by
    rw [abs_of_pos htPositive]
    norm_num
    exact htBounds.2
  let variance : Fin n → NNReal := fun i =>
    harperRankinLinearBlockVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y (start + (i : ℕ)))
      (4 * V / Real.log (y : ℝ)) t t
  let Q : Measure (Fin n → ℝ) :=
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
  have hvariance (i : Fin n) :
      (1 / 4 : ℝ) < (variance i : ℝ) ∧
        (variance i : ℝ) < 3 / 8 := by
    have hfar :
        Problem520.harperBlockEndpoint
            (start + (i : ℕ) + gapVar + 1) ≤ y := by
      apply (Problem520.monotone_harperBlockEndpoint ?_).trans hy
      dsimp only [gap]
      omega
    simpa only [variance, coe_harperRankinLinearBlockVarianceNNReal] using
      hvar 1 (start + (i : ℕ)) y (by omega) hfar t htLower htUpper
  have hlower : ∀ i, (1 / 4 : NNReal) ≤ variance i := by
    intro i
    exact_mod_cast (hvariance i).1.le
  have hupper : ∀ i, variance i ≤ (1 / 2 : NNReal) := by
    intro i
    exact_mod_cast (hvariance i).2.le.trans
      (by norm_num : (3 / 8 : ℝ) ≤ 1 / 2)
  have hcore :
      Real.exp
            (-2 - harper1144GaussianLogFenceCertificateBudget) /
          (4 * Real.sqrt (n : ℝ)) ≤
        Q.real (harper1144GaussianLogBallotCoreEvent n) := by
    simpa only [Q] using
      exp_neg_certificateBudget_div_sqrt_le_gaussianLogBallotCore
        n hn variance hlower hupper
  have hinter :
      Real.exp
            (-2 - harper1144GaussianLogFenceCertificateBudget) /
          (4 * Real.sqrt (n : ℝ)) ≤
        Q.real
          (harper1144ContractedGaussianLogBallotEvent start n ∩
            Problem520.harperCoordinateBox
              (Problem520.harperScheduledModerateRadius start n)) :=
    hcore.trans (measureReal_mono
      (harper1144GaussianLogBallotCoreEvent_subset_contracted_inter_box
        hstart30))
  have hmain := htransfer 1 start hstartTransfer n y hyTransfer t
    htLower htUpper
      (harper1144LogBallotLowerBarrier start n)
      (harper1144LogBallotUpperBarrier n)
  have hmain' :
      (3 / 4 : ℝ) *
          Q.real
            (harper1144ContractedGaussianLogBallotEvent start n ∩
              Problem520.harperCoordinateBox
                (Problem520.harperScheduledModerateRadius start n)) ≤
        (Measure.pi (fun i : Fin n =>
          harperRankinCenteredLinearBlockLaw y
            (Problem520.harperScheduledPrimeBlock y
              (start + (i : ℕ)))
            (4 * V / Real.log (y : ℝ)) t t)).real
          (Problem520.harperPartialSumBarrierSet
            (harper1144LogBallotLowerBarrier start n)
            (harper1144LogBallotUpperBarrier n)) := by
    simpa only [Q, variance, harperRankinGaussianBlockLaw,
      harper1144ContractedGaussianLogBallotEvent] using hmain
  calc
    (3 / 16 : ℝ) *
          Real.exp
            (-2 - harper1144GaussianLogFenceCertificateBudget) /
          Real.sqrt (n : ℝ) =
        (3 / 4 : ℝ) *
          (Real.exp
              (-2 - harper1144GaussianLogFenceCertificateBudget) /
            (4 * Real.sqrt (n : ℝ))) := by ring
    _ ≤ (3 / 4 : ℝ) *
        Q.real
          (harper1144ContractedGaussianLogBallotEvent start n ∩
            Problem520.harperCoordinateBox
              (Problem520.harperScheduledModerateRadius start n)) := by
      gcongr
    _ ≤ _ := hmain'

/-- Absolute-start form of the actual shifted lower ballot estimate. -/
theorem candidate_exists_uniform_start_rankinLogBallot_cube_lower
    :
    ∃ J : ℕ, ∀ V : ℝ, 0 ≤ V → ∃ gap : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n →
      ∀ y : ℕ,
        Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            (3 / 16 : ℝ) *
                Real.exp
                  (-2 - harper1144GaussianLogFenceCertificateBudget) /
                  Real.sqrt (n : ℝ) ≤
              (harperRankinTiltedCubeLaw y
                (4 * V / Real.log (y : ℝ)) t).real
                (harperRankinLogBallotCubeEvent y start n
                  (4 * V / Real.log (y : ℝ)) t) := by
  obtain ⟨J, hproduct⟩ := candidate_exists_uniform_start_rankinLogBallot_product_lower
  refine ⟨J, ?_⟩
  intro V hV
  obtain ⟨gap, hproduct⟩ := hproduct V hV
  refine ⟨gap, ?_⟩
  intro start hstart n hn y hy t ht
  rw [harperRankinLogBallotCubeEvent,
    harperRankinTiltedCubeLaw_real_preimage_centeredBlockVector_eq_pi
      y start n (4 * V / Real.log (y : ℝ)) t
      (Problem520.harperPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start n)
        (harper1144LogBallotUpperBarrier n))
      (Problem520.measurableSet_harperPartialSumBarrierSet _ _)]
  exact hproduct start hstart n hn y hy t ht

/-- Absolute-start form of the actual shifted lower ballot estimate. -/
theorem candidate_exists_uniform_start_rankinLogBallot_criticalScale
    :
    ∃ J : ℕ, ∀ V : ℝ, 0 ≤ V → ∃ gap : ℕ,
      ∀ start : ℕ, J ≤ start → ∀ n y : ℕ, 0 < n → 4 ≤ y →
        Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            candidateRankinBallotConstant * harperInitialCriticalScale y ≤
              (harperRankinTiltedCubeLaw y
                (4 * V / Real.log (y : ℝ)) t).real
                (harperRankinLogBallotCubeEvent y start n
                  (4 * V / Real.log (y : ℝ)) t) := by
  obtain ⟨J, hone⟩ := candidate_exists_uniform_start_rankinLogBallot_cube_lower
  refine ⟨J, ?_⟩
  intro V hV
  obtain ⟨gap, hone⟩ := hone V hV
  let c : ℝ := (3 / 16 : ℝ) *
    Real.exp (-2 - harper1144GaussianLogFenceCertificateBudget)
  refine ⟨gap, ?_⟩
  intro start hstart n y hn hy4 hendpoint t ht
  have hendpointBase :
      Problem520.harperBlockEndpoint (start + n) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans hendpoint
  let L : ℝ := 1 + Problem520.logLogNat y
  have hL : 0 < L := by
    dsimp only [L]
    exact Problem520.one_add_logLogNat_pos_of_four_le hy4
  have hindex := half_index_le_logLogNat_of_harperBlockEndpoint_le
    hendpointBase
  have hnL : (n : ℝ) ≤ 4 * L := by
    push_cast at hindex
    have hstartR : 0 ≤ (start : ℝ) := by positivity
    have hnHalf : (n : ℝ) / 2 ≤ Problem520.logLogNat y := by
      nlinarith
    have hnR' : 0 < (n : ℝ) := by exact_mod_cast hn
    dsimp only [L]
    nlinarith
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt L := by
    calc
      Real.sqrt (n : ℝ) ≤ Real.sqrt (4 * L) :=
        Real.sqrt_le_sqrt hnL
      _ = 2 * Real.sqrt L := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
  have hinv : (2 * Real.sqrt L)⁻¹ ≤
      (Real.sqrt (n : ℝ))⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (Real.sqrt_pos.2 hnR) hsqrt
  have hcritical : harperInitialCriticalScale y / 2 ≤
      (Real.sqrt (n : ℝ))⁻¹ := by
    have hrewrite : harperInitialCriticalScale y = (Real.sqrt L)⁻¹ := by
      unfold harperInitialCriticalScale
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hL.le]
      congr 2
      ring
    rw [hrewrite]
    have hsqrtL : Real.sqrt L ≠ 0 := (Real.sqrt_pos.2 hL).ne'
    calc
      (Real.sqrt L)⁻¹ / 2 = (2 * Real.sqrt L)⁻¹ := by
        field_simp
      _ ≤ (Real.sqrt (n : ℝ))⁻¹ := hinv
  have hraw := hone start hstart n hn y hendpoint t ht
  calc
    candidateRankinBallotConstant * harperInitialCriticalScale y =
        c * (harperInitialCriticalScale y / 2) := by
      dsimp only [candidateRankinBallotConstant, c]
      ring
    _ ≤ c * (Real.sqrt (n : ℝ))⁻¹ := by
      gcongr
    _ = (3 / 16 : ℝ) *
          Real.exp (-2 - harper1144GaussianLogFenceCertificateBudget) /
            Real.sqrt (n : ℝ) := by
      dsimp only [c]
      rw [div_eq_mul_inv]
      ring
    _ ≤ _ := hraw

/-- A fixed absolute starting index supports the actual Rankin graph and
its polynomial first moment. Only the terminal gap depends on `V`. -/
theorem candidate_exists_uniform_start_rankinLogBallotGraph_firstMoment :
    ∃ J : ℕ, ∀ V : ℝ, 0 ≤ V → ∃ gap : ℕ, ∀ start n y : ℕ,
      J ≤ start → 0 < n → 4 ≤ y →
      Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
      (1 + 4 * V) * Real.log 4 ≤ Real.log y →
        (candidateRankinNormalizerConstant * candidateRankinBallotConstant /
          (15 * (1 + 4 * V))) * harperInitialCriticalScale y ≤
          ∫ omega, harperRankinRestrictedGraphEnergy y (4 * V / Real.log y)
            (harperRankinLogBallotGraph y start n (4 * V / Real.log y)) omega ∂Problem520.μ := by
  obtain ⟨J, hone⟩ := candidate_exists_uniform_start_rankinLogBallot_criticalScale
  refine ⟨J, ?_⟩
  intro V hV
  obtain ⟨gap, hone⟩ := hone V hV
  refine ⟨gap, ?_⟩
  intro start n y hstart hn hy hcut hsize
  exact candidate_rankinRestrictedGraph_firstMoment_polynomial_of_probabilities hV hy hsize
    (measurableSet_harperRankinLogBallotGraph y start n _)
    (fun t => harperRankinLogBallotCubeEvent y start n (4 * V / Real.log y) t)
    (fun t omega => Iff.rfl) candidateRankinBallotConstant_pos.le
    (harperInitialCriticalScale_pos hy).le
    (fun t ht => hone start hstart n y hn hy hcut t ht)

end
end Erdos.Problem1144
