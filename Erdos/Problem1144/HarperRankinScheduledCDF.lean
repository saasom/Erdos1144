import Erdos.Problem1144.HarperRankinBlockLaw
import Erdos.Problem520.HarperScheduledCDFStrong

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators Interval

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Scheduled Gaussian replacement for Rankin-shifted blocks

The shifted one-prime law has the same cubic envelope and a no-larger
quartic budget than the critical-line law.  Consequently the existing
doubly-exponential Fejér frequency gives the same summable one-block
Kolmogorov error.  The only new numerical input is the shifted variance
lower bound `> 1/4`, supplied by `HarperRankinVarianceWindow`.
-/

/-- Explicit low-frequency characteristic comparison for a shifted
scheduled block. -/
theorem norm_charFun_harperRankinScheduledBlockLaw_sub_gaussian_le_explicit
    (y j : ℕ) {a : ℝ} (ha : 0 ≤ a) (t u T v : ℝ)
    (hv : |v| ≤ T)
    (hfrequency : 2 * T ≤
      Real.sqrt (Problem520.harperBlockEndpoint j : ℝ)) :
    ‖charFun (harperRankinCenteredLinearBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) a t u) v -
        charFun (harperRankinGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) a t u) v‖ ≤
      (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
        (16 * |v| ^ 3 + (1 / 2 : ℝ) * |v| ^ 4) := by
  let S := Problem520.harperScheduledPrimeBlock y j
  have hsmall : ∀ p ∈ S,
      |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) ≤ 1 := by
    intro p hpS
    have hpA := (Problem520.mem_harperScheduledPrimeBlock p).mp hpS |>.1
    have hp0 : 0 < p.1 := by
      have := Problem520.sixteen_le_prime_of_mem_harperScheduledPrimeBlock hpS
      omega
    have hpR : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hp0
    have hsqrtp : 0 < Real.sqrt (p.1 : ℝ) := Real.sqrt_pos.2 hpR
    have hsqrtMono :
        Real.sqrt (Problem520.harperBlockEndpoint j : ℝ) ≤
          Real.sqrt (p.1 : ℝ) := by
      exact Real.sqrt_le_sqrt (by exact_mod_cast hpA.le)
    have htwo : 2 * |v| ≤ Real.sqrt (p.1 : ℝ) := by
      calc
        2 * |v| ≤ 2 * T := mul_le_mul_of_nonneg_left hv (by norm_num)
        _ ≤ Real.sqrt (Problem520.harperBlockEndpoint j : ℝ) := hfrequency
        _ ≤ Real.sqrt (p.1 : ℝ) := hsqrtMono
    rw [show |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) =
        (2 * |v|) / Real.sqrt (p.1 : ℝ) by ring]
    exact (div_le_one hsqrtp).2 htwo
  have hquad : ∀ p ∈ S,
      harperRankinPrimeGaussianQuadratic p.1 a t u v ≤ 1 / 2 := by
    intro p hpS
    have hpA := (Problem520.mem_harperScheduledPrimeBlock p).mp hpS |>.1
    have hp0 : 0 < p.1 := by
      have := Problem520.sixteen_le_prime_of_mem_harperScheduledPrimeBlock hpS
      omega
    have hpR : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hp0
    have hsqrtMono :
        Real.sqrt (Problem520.harperBlockEndpoint j : ℝ) ≤
          Real.sqrt (p.1 : ℝ) := by
      exact Real.sqrt_le_sqrt (by exact_mod_cast hpA.le)
    have hvroot : |v| ≤ Real.sqrt (p.1 : ℝ) := by
      calc
        |v| ≤ T := hv
        _ ≤ 2 * T := by
          have hT : 0 ≤ T := (abs_nonneg v).trans hv
          linarith
        _ ≤ Real.sqrt (Problem520.harperBlockEndpoint j : ℝ) := hfrequency
        _ ≤ Real.sqrt (p.1 : ℝ) := hsqrtMono
    have hvSq : v ^ 2 ≤ (p.1 : ℝ) := by
      rw [← Real.sq_sqrt hpR.le, ← sq_abs v]
      exact pow_le_pow_left₀ (abs_nonneg v) hvroot 2
    have hvar := harperRankinCenteredLinearPrimeVariance_le_inv
      (show 1 ≤ p.1 by omega) ha t u
    unfold harperRankinPrimeGaussianQuadratic
    calc
      v ^ 2 * harperRankinCenteredLinearPrimeVariance p.1 a t u / 2 ≤
          v ^ 2 * (p.1 : ℝ)⁻¹ / 2 := by gcongr
      _ ≤ 1 / 2 := by
        rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
        rw [mul_inv_le_iff₀ hpR]
        simpa using hvSq
  have hbase :=
    norm_harperRankinScheduledBlockCharacteristic_sub_gaussian_le
      y j ha t u v hsmall hquad
  rw [← charFun_harperRankinCenteredLinearBlockLaw,
    ← charFun_harperRankinGaussianBlockLaw,
    sum_harperRankinPrimeGaussianQuadratic_sq_eq_quartic] at hbase
  have hbudget :=
    harperRankinBlockGaussianQuarticBudget_scheduled_le y j ha t u
  calc
    ‖charFun (harperRankinCenteredLinearBlockLaw y S a t u) v -
        charFun (harperRankinGaussianBlockLaw y S a t u) v‖ ≤
      16 * |v| ^ 3 *
          (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ +
        harperRankinBlockGaussianQuarticBudget y S a t u * |v| ^ 4 :=
      hbase
    _ ≤ 16 * |v| ^ 3 *
          (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ +
        ((1 / 2 : ℝ) *
          (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹) *
            |v| ^ 4 := by gcongr
    _ = (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
        (16 * |v| ^ 3 + (1 / 2 : ℝ) * |v| ^ 4) := by ring

/-- Explicit shifted Esseen discrepancy integral. -/
theorem harperRankinScheduledBlockEsseenIntegral_le_explicit
    (y j : ℕ) {a : ℝ} (ha : 0 ≤ a) (t u T : ℝ)
    (hT : 0 ≤ T)
    (hfrequency : 2 * T ≤
      Real.sqrt (Problem520.harperBlockEndpoint j : ℝ)) :
    Problem520.harperEsseenIntegral
        (charFun (harperRankinCenteredLinearBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) a t u))
        (charFun (harperRankinGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) a t u)) T ≤
      (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
        (32 * T ^ 3 + T ^ 4) := by
  have hbase := Problem520.harperEsseenIntegral_le_of_cubic_quartic
    (φ := charFun (harperRankinCenteredLinearBlockLaw y
      (Problem520.harperScheduledPrimeBlock y j) a t u))
    (ψ := charFun (harperRankinGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y j) a t u))
    (A := 16 *
      (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹)
    (B := (1 / 2 : ℝ) *
      (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹)
    continuous_charFun continuous_charFun
    (by positivity) (by positivity) hT
    (fun v hv ↦ by
      have h :=
        norm_charFun_harperRankinScheduledBlockLaw_sub_gaussian_le_explicit
          y j ha t u T v hv hfrequency
      calc
        ‖charFun (harperRankinCenteredLinearBlockLaw y
              (Problem520.harperScheduledPrimeBlock y j) a t u) v -
            charFun (harperRankinGaussianBlockLaw y
              (Problem520.harperScheduledPrimeBlock y j) a t u) v‖ ≤
            (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
              (16 * |v| ^ 3 + (1 / 2 : ℝ) * |v| ^ 4) := h
        _ = (16 *
              (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹) *
                |v| ^ 3 +
            ((1 / 2 : ℝ) *
              (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹) *
                |v| ^ 4 := by ring)
  calc
    Problem520.harperEsseenIntegral
        (charFun (harperRankinCenteredLinearBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) a t u))
        (charFun (harperRankinGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) a t u)) T ≤
      2 * T *
        ((16 * (Real.sqrt
          (Problem520.harperBlockEndpoint j : ℝ))⁻¹) * T ^ 2 +
          ((1 / 2 : ℝ) * (Real.sqrt
            (Problem520.harperBlockEndpoint j : ℝ))⁻¹) * T ^ 3) := hbase
    _ = (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
        (32 * T ^ 3 + T ^ 4) := by ring

theorem integrableOn_harperRankinScheduledBlockLawEsseenIntegrand
    (y j : ℕ) {a : ℝ} (ha : 0 ≤ a) (t u T : ℝ)
    (hT : 0 ≤ T)
    (hfrequency : 2 * T ≤
      Real.sqrt (Problem520.harperBlockEndpoint j : ℝ)) :
    IntegrableOn
      (Problem520.harperEsseenIntegrand
        (charFun (harperRankinCenteredLinearBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) a t u))
        (charFun (harperRankinGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) a t u)))
      (Icc (-T) T) := by
  refine Problem520.integrableOn_harperEsseenIntegrand_of_cubic_quartic
    continuous_charFun continuous_charFun
    (A := 16 *
      (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹)
    (B := (1 / 2 : ℝ) *
      (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹)
    (by positivity) (by positivity) hT ?_
  intro v hv
  have h :=
    norm_charFun_harperRankinScheduledBlockLaw_sub_gaussian_le_explicit
      y j ha t u T v hv hfrequency
  calc
    ‖charFun (harperRankinCenteredLinearBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) a t u) v -
        charFun (harperRankinGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) a t u) v‖ ≤
      (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
        (16 * |v| ^ 3 + (1 / 2 : ℝ) * |v| ^ 4) := h
    _ = (16 *
          (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹) * |v| ^ 3 +
        ((1 / 2 : ℝ) *
          (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹) * |v| ^ 4 := by
      ring

/-- Shifted smoothed-CDF comparison at one scheduled block. -/
theorem abs_harperRankinScheduledBlockSmooth_sub_gaussian_le
    (y j : ℕ) {a : ℝ} (ha : 0 ≤ a) (t u T : ℝ)
    (hT : 0 < T)
    (hfrequency : 2 * T ≤
      Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))
    (x : ℝ) :
    |Problem520.harperSmooth (Problem520.harperFejerMeasureScaled T)
          (cdf (harperRankinCenteredLinearBlockLaw y
            (Problem520.harperScheduledPrimeBlock y j) a t u)) x -
        Problem520.harperSmooth (Problem520.harperFejerMeasureScaled T)
          (cdf (harperRankinGaussianBlockLaw y
            (Problem520.harperScheduledPrimeBlock y j) a t u)) x| ≤
      (2 * Real.pi)⁻¹ *
        (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
          (32 * T ^ 3 + T ^ 4) := by
  let mu := harperRankinCenteredLinearBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j) a t u
  let nu := harperRankinGaussianBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j) a t u
  have hidentity :=
    harperRankinCenteredLinearBlock_fejerSmoothedCDFIdentity y
      (Problem520.harperScheduledPrimeBlock y j) a t u hT
  have hInt := integrableOn_harperRankinScheduledBlockLawEsseenIntegrand
    y j ha t u T hT.le hfrequency
  have hsmooth := Problem520.abs_harperSmooth_fejer_sub_le_of_identity
    mu nu T (by simpa only [mu, nu] using hidentity)
      (by simpa only [mu, nu] using hInt) x
  have hEsseen := harperRankinScheduledBlockEsseenIntegral_le_explicit
    y j ha t u T hT.le hfrequency
  change |Problem520.harperSmooth (Problem520.harperFejerMeasureScaled T)
      (cdf mu) x -
      Problem520.harperSmooth (Problem520.harperFejerMeasureScaled T)
        (cdf nu) x| ≤ _
  exact hsmooth.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hEsseen
        (by positivity : 0 ≤ (2 * Real.pi)⁻¹))

theorem inv_sqrt_le_two_of_one_fourth_lt
    {v : ℝ} (hv : (1 / 4 : ℝ) < v) :
    (Real.sqrt v)⁻¹ ≤ 2 := by
  have hquarter : (1 / 2 : ℝ) ^ 2 ≤ v := by nlinarith
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt v :=
    (Real.le_sqrt' (by norm_num)).2 hquarter
  have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hsqrt
  norm_num at hinv ⊢
  exact hinv

/-- Complete shifted one-block Kolmogorov comparison at the strong scheduled
frequency. -/
theorem harperRankinScheduledBlockCDFDistance_le_strong
    (y j : ℕ) {a : ℝ} (ha : 0 ≤ a) (t u : ℝ)
    (hvariance : (1 / 4 : ℝ) <
      harperRankinLinearBlockVariance y
        (Problem520.harperScheduledPrimeBlock y j) a t u) :
    Problem520.harperCDFDistance
        (harperRankinCenteredLinearBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) a t u)
        (harperRankinGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) a t u) ≤
      130 / Problem520.harperScheduledStrongComparisonFrequency j := by
  let T := Problem520.harperScheduledStrongComparisonFrequency j
  let V := harperRankinLinearBlockVariance y
    (Problem520.harperScheduledPrimeBlock y j) a t u
  let mu := harperRankinCenteredLinearBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j) a t u
  let nu := harperRankinGaussianBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j) a t u
  let M : ℝ := (Real.sqrt V)⁻¹
  let epsilon : ℝ := (2 * Real.pi)⁻¹ *
    (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
      (32 * T ^ 3 + T ^ 4)
  have hT : 0 < T := Problem520.harperScheduledStrongComparisonFrequency_pos j
  have hfrequency : 2 * T ≤
      Real.sqrt (Problem520.harperBlockEndpoint j : ℝ) :=
    Problem520.harperScheduledStrongComparisonFrequency_condition j
  have hvarianceNN :
      harperRankinLinearBlockVarianceNNReal y
        (Problem520.harperScheduledPrimeBlock y j) a t u ≠ 0 := by
    intro hzero
    have hcoezero : V = 0 := by
      simpa only [V, coe_harperRankinLinearBlockVarianceNNReal] using
        congrArg ((↑·) : NNReal → ℝ) hzero
    linarith
  have hLip : ∀ x z, |cdf nu x - cdf nu z| ≤ M * |x - z| := by
    intro x z
    dsimp [nu, M, V, harperRankinGaussianBlockLaw]
    exact Problem520.abs_cdf_gaussianReal_sub_le_inv_sqrt
      0 hvarianceNN x z
  have hsmooth : ∀ x,
      |Problem520.harperSmooth (Problem520.harperFejerMeasureScaled T)
          (cdf mu) x -
        Problem520.harperSmooth (Problem520.harperFejerMeasureScaled T)
          (cdf nu) x| ≤ epsilon := by
    intro x
    dsimp [mu, nu, epsilon]
    exact abs_harperRankinScheduledBlockSmooth_sub_gaussian_le
      y j ha t u T hT hfrequency x
  have hbase := Problem520.harperCDFDistance_le_of_smooth_le
    mu nu (Problem520.harperFejerMeasureScaled T)
    (M := M) (δ := 8 / T) (α := (1 / 4 : ℝ)) (ε := epsilon)
    hLip (by dsimp [M, V]; positivity) (by positivity) (by norm_num)
    (Problem520.harperFejerMeasureScaled_tail_le_quarter hT) hsmooth
  have hkernel :=
    Problem520.harperScheduledStrongComparisonFrequency_kernel_budget j
  have hkernel' :
      (2 * Real.pi)⁻¹ *
          (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
            (32 * T ^ 3 + T ^ 4) ≤ 33 / T := by
    calc
      (2 * Real.pi)⁻¹ *
          (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
            (32 * T ^ 3 + T ^ 4) =
        (2 * Real.pi)⁻¹ *
          ((Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
            (32 * T ^ 3 + T ^ 4)) := by ring
      _ ≤ (2 * Real.pi)⁻¹ * (33 / T) := by gcongr
      _ ≤ 1 * (33 / T) := by
        gcongr
        exact Problem520.fejer_coefficient_le_one
      _ = 33 / T := by ring
  have hvarinv : M ≤ 2 := by
    dsimp [M, V]
    exact inv_sqrt_le_two_of_one_fourth_lt hvariance
  have hvarianceTerm : 16 * M / T ≤ 32 / T := by
    rw [div_le_div_iff_of_pos_right hT]
    nlinarith
  change Problem520.harperCDFDistance mu nu ≤ _
  calc
    Problem520.harperCDFDistance mu nu ≤
        (epsilon + 2 * M * (8 / T)) /
          (1 - 2 * (1 / 4 : ℝ)) := hbase
    _ = 2 * (epsilon + 16 * M / T) := by ring
    _ ≤ 2 * (33 / T + 32 / T) := by
      gcongr
    _ = 130 / T := by ring
    _ = 130 / Problem520.harperScheduledStrongComparisonFrequency j := rfl

/-- Along any retained consecutive path, the total interval-probability
replacement error is summable and independent of the path length.  The fixed
gap is exactly the finite collection of top blocks discarded to stabilize the
Rankin variance. -/
theorem exists_gap_sum_harperRankinScheduledCentralBandCDFDistance_le
    (V : ℝ) (hV : 0 ≤ V) :
    ∃ gap J : ℕ, ∀ d start n y : ℕ, J + d ≤ start →
      Problem520.harperBlockEndpoint (start + n + gap) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
          (∑ k ∈ Finset.range n,
            2 * Problem520.harperCDFDistance
              (harperRankinCenteredLinearBlockLaw y
                (Problem520.harperScheduledPrimeBlock y (start + k))
                (4 * V / Real.log (y : ℝ)) t t)
              (harperRankinGaussianBlockLaw y
                (Problem520.harperScheduledPrimeBlock y (start + k))
                (4 * V / Real.log (y : ℝ)) t t)) ≤
            520 /
              Problem520.harperScheduledStrongComparisonFrequency start := by
  obtain ⟨gap, J, hwindow⟩ :=
    exists_gap_harperRankinScheduledCentralBandVarianceWindow V hV
  refine ⟨gap, J, ?_⟩
  intro d start n y hstart hy t htLower htUpper
  have hyOne : 1 < y := by
    have hbase := Problem520.harperBlockEndpoint_ge_sixteen
      (start + n + gap)
    omega
  have ha : 0 ≤ 4 * V / Real.log (y : ℝ) := by positivity
  have hpoint : ∀ k ∈ Finset.range n,
      2 * Problem520.harperCDFDistance
          (harperRankinCenteredLinearBlockLaw y
            (Problem520.harperScheduledPrimeBlock y (start + k))
            (4 * V / Real.log (y : ℝ)) t t)
          (harperRankinGaussianBlockLaw y
            (Problem520.harperScheduledPrimeBlock y (start + k))
            (4 * V / Real.log (y : ℝ)) t t) ≤
        2 * (130 /
          Problem520.harperScheduledStrongComparisonFrequency (start + k)) := by
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    have hfar :
        Problem520.harperBlockEndpoint (start + k + gap + 1) ≤ y := by
      exact (Problem520.monotone_harperBlockEndpoint (by omega)).trans hy
    have hvar := hwindow d (start + k) y
      (by omega) hfar t htLower htUpper
    gcongr
    exact harperRankinScheduledBlockCDFDistance_le_strong
      y (start + k) ha t t hvar.1
  calc
    (∑ k ∈ Finset.range n,
      2 * Problem520.harperCDFDistance
        (harperRankinCenteredLinearBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + k))
          (4 * V / Real.log (y : ℝ)) t t)
        (harperRankinGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y (start + k))
          (4 * V / Real.log (y : ℝ)) t t)) ≤
      ∑ k ∈ Finset.range n,
        2 * (130 /
          Problem520.harperScheduledStrongComparisonFrequency (start + k)) := by
      exact Finset.sum_le_sum hpoint
    _ = 2 * (∑ k ∈ Finset.range n,
        130 /
          Problem520.harperScheduledStrongComparisonFrequency (start + k)) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (260 /
        Problem520.harperScheduledStrongComparisonFrequency start) := by
      gcongr
      exact Problem520.sum_harperScheduledStrongComparisonBudget_le start n
    _ = 520 /
        Problem520.harperScheduledStrongComparisonFrequency start := by ring

end

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.norm_charFun_harperRankinScheduledBlockLaw_sub_gaussian_le_explicit
#print axioms Erdos.Problem1144.harperRankinScheduledBlockEsseenIntegral_le_explicit
#print axioms Erdos.Problem1144.abs_harperRankinScheduledBlockSmooth_sub_gaussian_le
#print axioms Erdos.Problem1144.harperRankinScheduledBlockCDFDistance_le_strong
#print axioms Erdos.Problem1144.exists_gap_sum_harperRankinScheduledCentralBandCDFDistance_le
