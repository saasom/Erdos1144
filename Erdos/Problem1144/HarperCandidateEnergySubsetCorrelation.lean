import Erdos.Problem1144.HarperCandidateEnergyPrefixLikelihood
import Erdos.Problem1144.HarperCandidateEnergyNormalizerCorrelation

open Finset
open scoped BigOperators

namespace Erdos.Problem1144

private theorem radial_scale_difference {q x : ℝ}
    (hq : 0 ≤ q) (hqx : q ≤ x) (hx : x ≤ 1 / 2) :
    0 ≤ 4 * x / (1 + x) ^ 2 - 4 * q / (1 + q) ^ 2 ∧
      4 * x / (1 + x) ^ 2 - 4 * q / (1 + q) ^ 2 ≤ 4 * (x - q) := by
  have hx0 : 0 ≤ x := hq.trans hqx
  have hqhalf : q ≤ 1 / 2 := hqx.trans hx
  have hxq : 0 ≤ x * q := mul_nonneg hx0 hq
  have hxq1 : x * q ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hqhalf)]
  have hden : 0 < (1 + x) ^ 2 * (1 + q) ^ 2 := by positivity
  have hden1 : 1 ≤ (1 + x) ^ 2 * (1 + q) ^ 2 := by
    have hx1 : 1 ≤ (1 + x) ^ 2 := by nlinarith
    have hq1 : 1 ≤ (1 + q) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hq1)]
  have heq : 4 * x / (1 + x) ^ 2 - 4 * q / (1 + q) ^ 2 =
      4 * (x - q) * (1 - x * q) / ((1 + x) ^ 2 * (1 + q) ^ 2) := by
    field_simp
    <;> ring
  rw [heq]
  constructor
  · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hqx)) (by linarith)) hden.le
  · apply (div_le_iff₀ hden).2
    have hloss : 0 ≤ 4 * (x - q) := mul_nonneg (by norm_num) (sub_nonneg.mpr hqx)
    have hleft := mul_le_mul_of_nonneg_left (show 1 - x * q ≤ 1 by linarith) hloss
    have hright := mul_le_mul_of_nonneg_left hden1 hloss
    nlinarith

private theorem radial_scale_le_eight_ninths {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    4 * x / (1 + x) ^ 2 ≤ 8 / 9 := by
  apply (div_le_iff₀ (by positivity : 0 < (1 + x) ^ 2)).2
  nlinarith [mul_nonneg (show 0 ≤ 1 - 2 * x by linarith)
    (show 0 ≤ 8 - 4 * x by linarith)]

private theorem log_radial_correlation_sub_le {q x c : ℝ}
    (hq : 0 ≤ q) (hqx : q ≤ x) (hx : x ≤ 1 / 2) (hc : -1 ≤ c) :
    Real.log (1 + (4 * q / (1 + q) ^ 2) * c) -
      Real.log (1 + (4 * x / (1 + x) ^ 2) * c) ≤ 36 * (x - q) := by
  let Q := 4 * q / (1 + q) ^ 2
  let X := 4 * x / (1 + x) ^ 2
  have hq0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hx0 : 0 ≤ X := by dsimp [X]; exact div_nonneg (by linarith) (sq_nonneg _)
  have hxsmall : X ≤ 8 / 9 := radial_scale_le_eight_ninths (hq.trans hqx) hx
  have hqsmall : Q ≤ 8 / 9 := radial_scale_le_eight_ninths hq (hqx.trans hx)
  have hXfloor : (1 / 9 : ℝ) ≤ 1 + X * c := by nlinarith [mul_le_mul_of_nonneg_left hc hx0]
  have hQfloor : (1 / 9 : ℝ) ≤ 1 + Q * c := by nlinarith [mul_le_mul_of_nonneg_left hc hq0]
  have hXp : 0 < 1 + X * c := by linarith
  have hQp : 0 < 1 + Q * c := by linarith
  have hdiff : 0 ≤ X - Q ∧ X - Q ≤ 4 * (x - q) := radial_scale_difference hq hqx hx
  have hprod := mul_le_mul_of_nonneg_left hc hdiff.1
  have hdelta : (1 + Q * c) - (1 + X * c) ≤ 4 * (x - q) := by nlinarith
  have hratio : (1 + Q * c) / (1 + X * c) - 1 ≤ 36 * (x - q) := by
    have hfloor := mul_le_mul_of_nonneg_left hXfloor (show 0 ≤ 36 * (x - q) from mul_nonneg (by norm_num) (sub_nonneg.mpr hqx))
    have hle : 1 + Q * c ≤ (36 * (x - q) + 1) * (1 + X * c) := by nlinarith
    have h := (div_le_iff₀ hXp).mpr hle
    linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hQp hXp)
  rw [Real.log_div hQp.ne' hXp.ne'] at hlog
  exact hlog.trans hratio

/-- A single shifted correlation loses at most 36 times the removed radial
prime mass relative to its actual critical counterpart. The constant is
4 (radial scale slope) times 9 (the inverse critical correlation floor). -/
theorem candidate_log_rankinPrimeCorrelation_sub_critical_le
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    Real.log (harperRankinTwoHeightPrimeCorrelation p a t s) -
      Real.log (harperTwoHeightPrimeCorrelation p t s) ≤
        36 * ((p : ℝ)⁻¹ - harperRankinEulerRadius p a ^ 2) := by
  have hrad : harperRankinEulerRadius p a ^ 2 ≤ (p : ℝ)⁻¹ := by
    rw [harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg hp.pos]
    exact mul_le_of_le_one_right (by positivity)
      (rpow_neg_le_one_of_one_le (by exact_mod_cast hp.one_le) ha)
  have hx : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ p by exact_mod_cast hp.two_le)
  have hc : -1 ≤ Real.cos (t * Real.log (p : ℝ)) * Real.cos (s * Real.log (p : ℝ)) := by
    have h := mul_le_mul (Real.abs_cos_le_one (t * Real.log (p : ℝ)))
      (Real.abs_cos_le_one (s * Real.log (p : ℝ))) (abs_nonneg _) (by norm_num)
    rw [← abs_mul] at h
    exact (abs_le.mp (by simpa using h)).1
  have h := log_radial_correlation_sub_le (sq_nonneg _) hrad hx hc
  rw [harperRankinTwoHeightPrimeCorrelation_eq, harperTwoHeightPrimeCorrelation_eq hp]
  unfold harperRankinEulerNormalizer
  convert h using 1 <;> congr 1 <;> congr 1 <;> ring

/-- The global logarithmic normalizer ratio controls every subset of the
removed radial mass, so arbitrary complements and partial blocks are allowed. -/
theorem candidate_log_rankinSubsetCorrelation_sub_critical_le
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y)) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    Real.log (candidateRankinSubsetCorrelation y S a t s) -
      Real.log (harperSubsetCorrelation y S t s) ≤
        72 * Real.log (Problem520.primeEnergyNormalizer y / harperRankinPrimeEnergyNormalizer y a) := by
  have hrad (p : Problem520.HarperPrimeIndex y) :
      0 ≤ (p.1 : ℝ)⁻¹ - harperRankinEulerRadius p.1 a ^ 2 := by
    have hp := Nat.prime_of_mem_primesBelow p.property
    rw [harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg hp.pos]
    have h := rpow_neg_le_one_of_one_le (show (1 : ℝ) ≤ p.1 by exact_mod_cast hp.one_le) ha
    exact sub_nonneg.mpr (mul_le_of_le_one_right (by positivity) h)
  have hmass := candidate_rankinRadius_loss_le_log_normalizer_ratio y ha
  have hsub : (∑ p ∈ S, ((p.1 : ℝ)⁻¹ - harperRankinEulerRadius p.1 a ^ 2)) ≤
      ∑ p : Problem520.HarperPrimeIndex y, ((p.1 : ℝ)⁻¹ - harperRankinEulerRadius p.1 a ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg S.subset_univ (fun p hp hnp => hrad p)
  unfold candidateRankinSubsetCorrelation harperSubsetCorrelation
  rw [Real.log_prod (fun p hp => (harperRankinTwoHeightPrimeCorrelation_pos
      (Nat.prime_of_mem_primesBelow p.property) ha t s).ne'),
    Real.log_prod (fun p hp => (harperTwoHeightPrimeCorrelation_pos
      (Nat.prime_of_mem_primesBelow p.property) t s).ne'), ← Finset.sum_sub_distrib]
  have h := Finset.sum_le_sum (s := S) (fun p hp =>
    candidate_log_rankinPrimeCorrelation_sub_critical_le (Nat.prime_of_mem_primesBelow p.property) ha t s)
  rw [← Finset.mul_sum] at h
  linarith

/-- Literal shifted correlation on any prime subset is bounded by the
critical correlation times the 72nd power of the actual normalizer ratio. -/
theorem candidate_rankinSubsetCorrelation_le_critical_mul_ratio
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y)) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    candidateRankinSubsetCorrelation y S a t s ≤
      (Problem520.primeEnergyNormalizer y / harperRankinPrimeEnergyNormalizer y a) ^ 72 *
        harperSubsetCorrelation y S t s := by
  have h := candidate_log_rankinSubsetCorrelation_sub_critical_le y S ha t s
  have hlog : Real.log (candidateRankinSubsetCorrelation y S a t s) ≤
      72 * Real.log (Problem520.primeEnergyNormalizer y / harperRankinPrimeEnergyNormalizer y a) +
      Real.log (harperSubsetCorrelation y S t s) := by linarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (candidate_rankinSubsetCorrelation_pos y S ha t s), Real.exp_add,
    Real.exp_log (harperSubsetCorrelation_pos y S t s)] at he
  have hpow : Real.exp (72 * Real.log
      (Problem520.primeEnergyNormalizer y / harperRankinPrimeEnergyNormalizer y a)) =
      (Problem520.primeEnergyNormalizer y / harperRankinPrimeEnergyNormalizer y a) ^ 72 := by
    rw [show (72 : ℝ) * Real.log
      (Problem520.primeEnergyNormalizer y / harperRankinPrimeEnergyNormalizer y a) =
      Real.log ((Problem520.primeEnergyNormalizer y / harperRankinPrimeEnergyNormalizer y a) ^ 72) by
        rw [Real.log_pow]; norm_num]
    exact Real.exp_log (pow_pos (div_pos (Problem520.primeEnergyNormalizer_pos y)
      (harperRankinPrimeEnergyNormalizer_pos y a)) _)
  rw [hpow] at he
  exact he

/-- Polynomial Rankin-parameter control on arbitrary subset correlations. -/
theorem candidate_rankinSubsetCorrelation_le_critical_polynomial
    {V : ℝ} (hV : 0 ≤ V) {y : ℕ} (hy : 4 ≤ y)
    (hsize : (1 + 4 * V) * Real.log 4 ≤ Real.log y)
    (S : Finset (Problem520.HarperPrimeIndex y)) (t s : ℝ) :
    candidateRankinSubsetCorrelation y S (4 * V / Real.log y) t s ≤
      (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 72 *
        harperSubsetCorrelation y S t s := by
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have ha : 0 ≤ 4 * V / Real.log (y : ℝ) := by positivity
  exact (candidate_rankinSubsetCorrelation_le_critical_mul_ratio y S ha t s).trans
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (div_nonneg (Problem520.primeEnergyNormalizer_pos y).le
        (harperRankinPrimeEnergyNormalizer_pos y _).le)
        (candidate_rankinNormalizer_ratio_le_polynomial hV hy hsize) 72)
      (harperSubsetCorrelation_pos y S t s).le)

end Erdos.Problem1144
