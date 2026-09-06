import Erdos.Problem1144.HarperCandidateCovarianceGrowingHeight
import Erdos.Problem520.HarperMovingHeightCumulative

open Set Filter Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace Erdos.Problem1144

noncomputable section

/-! Actual variance and cumulative drift bounds throughout the growing
frequency window supplied by the retained strong-PNT error. -/

/-- Quarter-to-half block variance uniformly over the full growing window. -/
theorem candidate_exists_growingHeight_variance_quarter_half :
    ∃ J : ℕ, ∀ start j M y : ℕ, J ≤ start → start ≤ j →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start →
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
      |u - t| * Real.log (Problem520.harperBlockEndpoint (j + 1) : ℝ) ≤ (1 / 64 : ℝ) →
      (1 / 4 : ℝ) < Problem520.harperLinearBlockVariance y
        (Problem520.harperScheduledPrimeBlock y j) t u ∧
      Problem520.harperLinearBlockVariance y
        (Problem520.harperScheduledPrimeBlock y j) t u < (1 / 2 : ℝ) := by
  obtain ⟨K, hK, Jo, ho⟩ := candidate_exists_growingHeight_oscillation_bound
  have hsmall : ∀ᶠ j : ℕ in atTop,
      (1 / 2 : ℝ) ^ j + K * (1 / 2 : ℝ) ^ (2 * j) < (1 / 1000 : ℝ) := by
    have hq : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hq2 : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ (2 * j)) atTop (𝓝 0) := by
      convert hq.pow 2 using 1
      · funext j
        rw [← pow_mul, Nat.mul_comm]
      · norm_num
    have h := hq.add (hq2.const_mul K)
    simpa only [mul_zero, add_zero] using
      (tendsto_order.mp h).2 (1 / 1000 : ℝ) (by norm_num)
  obtain ⟨Js, hs⟩ := Filter.eventually_atTop.mp hsmall
  obtain ⟨Jmass, hmass⟩ := Problem520.exists_eventually_harperScheduledPrimeBlock_inv_close_log_two
    (by norm_num : (0 : ℝ) < 1 / 1000)
  obtain ⟨Jloss, hloss⟩ := Problem520.exists_eventually_harperScheduledVarianceBiasLoss_lt
    (by norm_num : (0 : ℝ) < 1 / 1000)
  obtain ⟨Jinv, hinv⟩ := Problem520.exists_eventually_harperScheduledPrimeBlock_inv_bounds
  refine ⟨max Jo (max Js (max Jmass (max Jloss Jinv))), ?_⟩
  intro start j M y hstart hsj hM hy t htlo hthi u hu
  have hosc := (ho start j M y (by omega) hsj hM hy t htlo hthi).trans_lt (hs j (by omega))
  have hrec := hmass j (by omega) y hy
  have hbias := hloss j (by omega) y hy t
  have hbias0 := Problem520.harperScheduledVarianceBiasLoss_nonneg y j t
  have hdiag : (1 / 3 : ℝ) < Problem520.harperLinearBlockVariance y
      (Problem520.harperScheduledPrimeBlock y j) t t ∧
      Problem520.harperLinearBlockVariance y
        (Problem520.harperScheduledPrimeBlock y j) t t < (3 / 8 : ℝ) := by
    rw [Problem520.harperScheduledDiagonalVariance_eq_cosineMass_sub_biasLoss,
      Problem520.sum_harperScheduledPrimeBlock_cos_sq_div]
    change |Problem520.harperScheduledOscillationMass y j (2 * t)| < _ at hosc
    have hoL := neg_lt_of_abs_lt hosc
    have hoU := lt_of_abs_lt hosc
    have hrL := neg_lt_of_abs_lt hrec
    have hrU := lt_of_abs_lt hrec
    unfold Problem520.harperScheduledOscillationMass at hoL hoU
    constructor <;> nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  have hperturb := Problem520.abs_harperScheduledLinearBlockVariance_sub_diagonal_le_three_mul
    y j t u (1 / 64 : ℝ) (by norm_num) (hinv j (by omega) y hy).2 hu
  have hlo := neg_le_of_abs_le hperturb
  have hhi := le_of_abs_le hperturb
  constructor <;> nlinarith [hdiag.1, hdiag.2]

/-- Uniform cumulative diagonal log drift, with an absolute additive error
independent of the growing height, the prefix length and the Euler cutoff. -/
theorem candidate_exists_growingHeight_diagonalDrift_close :
    ∃ D ≥ 0, ∃ J : ℕ, ∀ start n M y : ℕ, J ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start →
      Problem520.harperBlockEndpoint (start + n) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
      |Problem520.harperLogMainBlockMean y
        (Problem520.harperScheduledPrimeRangeFrom y start n) t t - (n : ℝ) * Real.log 2| ≤ D := by
  obtain ⟨K, hK, Jo, ho⟩ := candidate_exists_growingHeight_oscillation_bound
  obtain ⟨c, hc, C, hC, Jb, hb⟩ := Problem520.exists_harperScheduledCumulativeReciprocalSquareBounds
  let R := ∑' j : ℕ, Problem520.harperScheduledReciprocalEnvelope c C j
  let Q := ∑' j : ℕ, Problem520.harperScheduledSquareEnvelope j
  have hR : 0 ≤ R := tsum_nonneg (Problem520.harperScheduledReciprocalEnvelope_nonneg hC.le)
  have hQ : 0 ≤ Q := tsum_nonneg Problem520.harperScheduledSquareEnvelope_nonneg
  refine ⟨R + (1 + K) + 2 * Q, by positivity, max Jo Jb, ?_⟩
  intro start n M y hstart hM hy t htlo hthi
  have hbase := hb start n y (by omega) hy
  have hrec := hbase.1.trans (Problem520.harperScheduledErrorTail_le_tsum
    (Problem520.harperScheduledReciprocalEnvelope_nonneg hC.le)
    (Problem520.summable_harperScheduledReciprocalEnvelope hc hC.le) start)
  have hsq := hbase.2.trans (Problem520.harperScheduledErrorTail_le_tsum
    Problem520.harperScheduledSquareEnvelope_nonneg
    Problem520.summable_harperScheduledSquareEnvelope start)
  have hosc : (∑ i : Fin n,
      |Problem520.harperScheduledOscillationMass y (start + i.val) (2 * t)|) ≤ 2 * (1 + K) := by
    calc
      _ ≤ ∑ i : Fin n, (1 + K) * (1 / 2 : ℝ) ^ i.val := by
        apply Finset.sum_le_sum
        intro i hi
        have h := ho start (start + i.val) M y (by omega) (by omega) hM
          ((Problem520.monotone_harperBlockEndpoint (by omega)).trans hy) t htlo hthi
        have hpow1 : (1 / 2 : ℝ) ^ (start + i.val) ≤ (1 / 2 : ℝ) ^ i.val :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        have hpow2 : (1 / 2 : ℝ) ^ (2 * (start + i.val)) ≤ (1 / 2 : ℝ) ^ i.val :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hpow2 hK])
      _ = (1 + K) * ∑ i : Fin n, (1 / 2 : ℝ) ^ i.val := by rw [Finset.mul_sum]
      _ ≤ (1 + K) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (1 / 2 : ℝ) ^ i) n]
        exact sum_geometric_two_le n
      _ = _ := by ring
  have hcor : (∑ i : Fin n, Problem520.harperScheduledDiagonalCorrection y (start + i.val) t) ≤
      2 * Q := by
    calc
      _ ≤ ∑ i : Fin n, 2 * Problem520.harperScheduledSquareMass y (start + i.val) :=
        Finset.sum_le_sum fun i hi => Problem520.harperScheduledDiagonalCorrection_le_twice_squareMass y _ t
      _ = 2 * ∑ i : Fin n, Problem520.harperScheduledSquareMass y (start + i.val) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hcor0 : 0 ≤ ∑ i : Fin n, Problem520.harperScheduledDiagonalCorrection y (start + i.val) t :=
    Finset.sum_nonneg fun i hi => Problem520.harperScheduledDiagonalCorrection_nonneg y _ t
  have hid : Problem520.harperLogMainBlockMean y
      (Problem520.harperScheduledPrimeRangeFrom y start n) t t =
      (∑ i : Fin n, Problem520.harperScheduledReciprocalMass y (start + i.val)) +
      (1 / 2 : ℝ) * (∑ i : Fin n, Problem520.harperScheduledOscillationMass y (start + i.val) (2 * t)) -
      ∑ i : Fin n, Problem520.harperScheduledDiagonalCorrection y (start + i.val) t := by
    rw [← Problem520.sum_harperLogMainBlockMean_eq_rangeFrom,
      ← Fin.sum_univ_eq_sum_range (fun i : ℕ => Problem520.harperLogMainBlockMean y
        (Problem520.harperScheduledPrimeBlock y (start + i)) t t) n]
    simp only [Problem520.harperScheduledDiagonalMainMean_eq,
      Problem520.harperScheduledReciprocalMass, Problem520.harperScheduledOscillationMass,
      Problem520.harperScheduledDiagonalCorrection]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hoscAbs : |∑ i : Fin n, Problem520.harperScheduledOscillationMass y (start + i.val) (2 * t)| ≤
      2 * (1 + K) := (Finset.abs_sum_le_sum_abs _ _).trans hosc
  rw [hid, abs_le]
  rw [abs_le] at hrec hoscAbs
  change -R ≤ _ ∧ _ ≤ R at hrec
  constructor <;> linarith [hrec.1, hrec.2, hoscAbs.1, hoscAbs.2]

end

end Erdos.Problem1144
