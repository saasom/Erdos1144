import Erdos.Problem1144.HarperCandidateEnergyNormalizerEffective
import Erdos.Problem1144.HarperRankinRestrictedGraph

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- The already proved one-height probability constant is absolute: the
Rankin parameter changes only the starting index and terminal gap. -/
noncomputable def candidateRankinBallotConstant : ℝ :=
  (3 / 32) * Real.exp (-2 - harper1144GaussianLogFenceCertificateBudget)

theorem candidateRankinBallotConstant_pos : 0 < candidateRankinBallotConstant := by
  unfold candidateRankinBallotConstant
  positivity

/-- Explicit absolute coefficient in the shifted one-height theorem. -/
theorem candidate_rankinLogBallot_cube_ge_absolute_criticalScale
    (V : ℝ) (hV : 0 ≤ V) :
    ∃ gap J : ℕ,
      ∀ start : ℕ, J ≤ start → ∀ n y : ℕ, 0 < n → 4 ≤ y →
        Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            candidateRankinBallotConstant * harperInitialCriticalScale y ≤
              (harperRankinTiltedCubeLaw y
                (4 * V / Real.log (y : ℝ)) t).real
                (harperRankinLogBallotCubeEvent y start n
                  (4 * V / Real.log (y : ℝ)) t) := by
  obtain ⟨gap, J, hone⟩ :=
    exists_gap_harperRankinLogBallotFixedStart_cube_lower V hV
  let c : ℝ := (3 / 16 : ℝ) *
    Real.exp (-2 - harper1144GaussianLogFenceCertificateBudget)
  refine ⟨gap, J, ?_⟩
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


/-- The restricted first moment loses only one polynomial factor in the
Rankin parameter, once the effective cutoff is available. -/
theorem candidate_rankinRestrictedGraph_firstMoment_polynomial_of_probabilities
    {V : ℝ} (hV : 0 ≤ V) {y : ℕ} (hy : 4 ≤ y)
    (hsize : (1 + 4 * V) * Real.log 4 ≤ Real.log y)
    {G : Set (ℝ × Problem520.Omega)} (hG : MeasurableSet G)
    (A : ℝ → Set (Problem520.HarperPrimeCube y))
    (hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t)
    {delta K : ℝ} (hdelta : 0 ≤ delta) (hK : 0 ≤ K)
    (hprob : ∀ t ∈ harperLowerVerticalBand,
      delta * K ≤
        (harperRankinTiltedCubeLaw y
          (4 * V / Real.log (y : ℝ)) t).real (A t)) :
    (candidateRankinNormalizerConstant * delta / (15 * (1 + 4 * V))) * K ≤
      ∫ omega,
        harperRankinRestrictedGraphEnergy y
          (4 * V / Real.log (y : ℝ)) G omega ∂Problem520.μ := by
  let a : ℝ := 4 * V / Real.log (y : ℝ)
  let cV : ℝ := candidateRankinNormalizerConstant / (2 * (1 + 4 * V))
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hnormalizer : cV ≤
      harperRankinPrimeEnergyNormalizer y a / Real.log (y : ℝ) := by
    rw [le_div_iff₀ hlog]
    have h := candidate_rankinNormalizer_lower_polynomial hV hy hsize
    simpa only [cV, a, div_mul_eq_mul_div, mul_comm] using h
  have hprobInt := integrableOn_harperRankinTiltedCubeLaw_real_of_graph
    a hG A hsection
  have hconstInt : IntegrableOn (fun _t : ℝ ↦ delta * K)
      harperLowerVerticalBand := integrableOn_const (by
    simp [harperLowerVerticalBand, Real.volume_Icc])
  have hintegral : (delta * K) / 6 ≤
      ∫ t in harperLowerVerticalBand,
        (harperRankinTiltedCubeLaw y a t).real (A t) := by
    have hmono := setIntegral_mono_on hconstInt hprobInt
      measurableSet_harperLowerVerticalBand (by
        intro t ht
        simpa only [a] using hprob t ht)
    calc
      (delta * K) / 6 =
          ∫ _t in harperLowerVerticalBand, delta * K := by
        norm_num [harperLowerVerticalBand, Real.volume_Icc] <;> ring
      _ ≤ _ := hmono
  rw [integral_harperRankinRestrictedGraphEnergy_eq_tiltedProbabilities
    a hG A hsection]
  have hcV : 0 ≤ cV := div_nonneg candidateRankinNormalizerConstant_pos.le (by positivity)
  have hprobNonneg : 0 ≤ (delta * K) / 6 := by positivity
  have hnormalizerNonneg :
      0 ≤ harperRankinPrimeEnergyNormalizer y a / Real.log (y : ℝ) :=
    hcV.trans hnormalizer
  calc
    (candidateRankinNormalizerConstant * delta / (15 * (1 + 4 * V))) * K =
        (4 / 5 : ℝ) * cV * ((delta * K) / 6) := by
      dsimp only [cV]
      field_simp
      ring
    _ ≤ (4 / 5 : ℝ) *
          (harperRankinPrimeEnergyNormalizer y a / Real.log (y : ℝ)) *
            ((delta * K) / 6) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnormalizer (by norm_num)) hprobNonneg
    _ ≤ (4 / 5 : ℝ) *
          (harperRankinPrimeEnergyNormalizer y a / Real.log (y : ℝ)) *
            ∫ t in harperLowerVerticalBand,
              (harperRankinTiltedCubeLaw y a t).real (A t) := by
      exact mul_le_mul_of_nonneg_left hintegral
        (mul_nonneg (by norm_num) hnormalizerNonneg)

/-- An unconditional literal ballot graph with an explicit polynomial first
moment. Only the cutoff threshold and graph indices depend on `V`; the two
numerator constants are absolute. -/
theorem candidate_exists_rankinLogBallotGraph_firstMoment_polynomial
    (V : ℝ) (hV : 0 ≤ V) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → 4 ≤ y →
      let a : ℝ := 4 * V / Real.log (y : ℝ)
      ∃ G : Set (ℝ × Problem520.Omega), MeasurableSet G ∧
        (∀ omega,
          harperRankinRestrictedGraphEnergy y a G omega ≤
            harperSquarefreeShiftedNormalizedEnergy y a omega) ∧
        Integrable (harperRankinRestrictedGraphEnergy y a G) Problem520.μ ∧
        (candidateRankinNormalizerConstant * candidateRankinBallotConstant /
          (15 * (1 + 4 * V))) * harperInitialCriticalScale y ≤
          ∫ omega, harperRankinRestrictedGraphEnergy y a G omega ∂Problem520.μ := by
  obtain ⟨gap, J, hone⟩ := candidate_rankinLogBallot_cube_ge_absolute_criticalScale V hV
  obtain ⟨Ylog, hYlog⟩ := exists_nat_gt
    (Real.exp (max (4 * V) ((1 + 4 * V) * Real.log 4)))
  let Yroom : ℕ := Problem520.harperBlockEndpoint (J + gap + 1)
  let Y : ℕ := max 4 (max Ylog Yroom)
  refine ⟨Y, ?_⟩
  intro y hyY hy4
  have hyLog : Ylog ≤ y :=
    (le_max_left Ylog Yroom).trans
      ((le_max_right 4 (max Ylog Yroom)).trans hyY)
  have hyRoom : Yroom ≤ y :=
    (le_max_right Ylog Yroom).trans
      ((le_max_right 4 (max Ylog Yroom)).trans hyY)
  let a : ℝ := 4 * V / Real.log (y : ℝ)
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hexpY : Real.exp (4 * V) < (y : ℝ) := by
    exact (Real.exp_le_exp.mpr (le_max_left _ _)).trans_lt
      (hYlog.trans_le (by exact_mod_cast hyLog))
  have hfourVlog : 4 * V < Real.log (y : ℝ) := by
    rw [← Real.exp_lt_exp]
    simpa only [Real.exp_log (by positivity : (0 : ℝ) < y)] using hexpY
  have hsize : (1 + 4 * V) * Real.log 4 ≤ Real.log (y : ℝ) := by
    have hlarge : Real.exp ((1 + 4 * V) * Real.log 4) < (y : ℝ) :=
      (Real.exp_le_exp.mpr (le_max_right _ _)).trans_lt
        (hYlog.trans_le (by exact_mod_cast hyLog))
    exact (Real.lt_log_iff_exp_lt (by positivity)).mpr hlarge |>.le
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    exact (div_le_one hlog).2 hfourVlog.le
  have hroom : J + gap + 5 ≤ Problem520.harperAvailableLogScale y := by
    have hendpoint : Problem520.harperBlockEndpoint (J + gap + 1) ≤ y :=
      hyRoom
    have h := Problem520.add_four_le_harperAvailableLogScale_of_blockEndpoint_le
      hendpoint
    omega
  let n : ℕ := Problem520.harperEconomicalPathLength y J gap
  have hn : 0 < n := by
    dsimp only [n]
    exact Problem520.harperEconomicalPathLength_pos hroom
  have hyne : y ≠ 0 := by omega
  have hfit : Problem520.harperEconomicalStart J gap + 4 ≤
      Problem520.harperAvailableLogScale y := by
    simp only [Problem520.harperEconomicalStart]
    omega
  have hendpoint : Problem520.harperBlockEndpoint (J + n + gap) ≤ y := by
    have h := Problem520.harperBlockEndpoint_economicalStart_add_le
      hyne hfit (m := n) le_rfl
    simpa only [Problem520.harperEconomicalStart, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using h
  let G : Set (ℝ × Problem520.Omega) :=
    harperRankinLogBallotGraph y J n a
  let A : ℝ → Set (Problem520.HarperPrimeCube y) := fun t ↦
    harperRankinLogBallotCubeEvent y J n a t
  have hG : MeasurableSet G := by
    simpa only [G] using measurableSet_harperRankinLogBallotGraph y J n a
  have hprob : ∀ t ∈ harperLowerVerticalBand,
      candidateRankinBallotConstant * harperInitialCriticalScale y ≤
        (harperRankinTiltedCubeLaw y a t).real (A t) := by
    intro t ht
    simpa only [a, A] using
      hone J le_rfl n y hn hy4 hendpoint t ht
  refine ⟨G, hG, ?_, ?_, ?_⟩
  · intro omega
    exact harperRankinRestrictedGraphEnergy_le_shiftedNormalized
      (by omega) ha ha1 hG omega
  · exact integrable_harperRankinRestrictedGraphEnergy a hG
  · simpa only [a] using
      candidate_rankinRestrictedGraph_firstMoment_polynomial_of_probabilities
        hV hy4 hsize hG A (fun t omega ↦ Iff.rfl) candidateRankinBallotConstant_pos.le
          (harperInitialCriticalScale_pos hy4).le hprob

end Erdos.Problem1144
