import Erdos.Problem1144.HarperCandidateEnergyNormalizerEffective
import Erdos.Problem1144.HarperRankinTwoHeightCorrelation

open Finset
open scoped BigOperators

namespace Erdos.Problem1144

private theorem candidate_sub_le_two_log_ratio
    {x q : ℝ} (hq : 0 ≤ q) (hqx : q ≤ x) (hx : x ≤ 1) :
    x - q ≤ 2 * (Real.log (1 + x) - Real.log (1 + q)) := by
  have hxp : 0 < 1 + x := by linarith
  have hqp : 0 < 1 + q := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hqp hxp)
  rw [Real.log_div hqp.ne' hxp.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_right hlog hxp.le
  simp only [sub_mul, div_mul_cancel₀ _ hxp.ne', one_mul] at hmul
  have hmono := Real.log_le_log hqp (by linarith : 1 + q ≤ 1 + x)
  have hprod := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hmono)
  nlinarith

/-- The loss in total prime mass is controlled by the logarithm of the
actual Euler-normalizer ratio, rather than a linear Rankin-parameter loss. -/
theorem candidate_rankinRadius_loss_le_log_normalizer_ratio
    (y : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (∑ p : Problem520.HarperPrimeIndex y,
      ((p.1 : ℝ)⁻¹ - harperRankinEulerRadius p.1 a ^ 2)) ≤
      2 * Real.log (Problem520.primeEnergyNormalizer y /
        harperRankinPrimeEnergyNormalizer y a) := by
  rw [Real.log_div (Problem520.primeEnergyNormalizer_pos y).ne'
    (harperRankinPrimeEnergyNormalizer_pos y a).ne']
  unfold Problem520.primeEnergyNormalizer harperRankinPrimeEnergyNormalizer
  rw [Real.log_prod (fun p hp => by positivity),
    Real.log_prod (fun p hp => (harperRankinEulerNormalizer_pos p a).ne'),
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_coe_sort ((y + 1).primesBelow)
    (fun p => ((p : ℝ)⁻¹ - harperRankinEulerRadius p a ^ 2))]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := Nat.prime_of_mem_primesBelow hp
  have hq : 0 ≤ harperRankinEulerRadius p a ^ 2 := sq_nonneg _
  have hqx : harperRankinEulerRadius p a ^ 2 ≤ (p : ℝ)⁻¹ := by
    rw [harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg hprime.pos a]
    exact mul_le_of_le_one_right (by positivity)
      (rpow_neg_le_one_of_one_le (by exact_mod_cast hprime.one_le) ha)
  have hx : (p : ℝ)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hprime.one_le)
  exact candidate_sub_le_two_log_ratio hq hqx hx

/-- Every shifted cosine kernel differs from its critical kernel by only
twice the logarithm of the literal normalizer ratio. -/
theorem candidate_rankinCosineKernel_le_critical_log_ratio
    (y : ℕ) {a : ℝ} (ha : 0 ≤ a) (u : ℝ) :
    harperRankinPrimeCosineKernel y a u ≤ harperPrimeCosineKernel y u +
      2 * Real.log (Problem520.primeEnergyNormalizer y /
        harperRankinPrimeEnergyNormalizer y a) := by
  have hsum : harperRankinPrimeCosineKernel y a u ≤ harperPrimeCosineKernel y u +
      ∑ p : Problem520.HarperPrimeIndex y,
        ((p.1 : ℝ)⁻¹ - harperRankinEulerRadius p.1 a ^ 2) := by
    unfold harperRankinPrimeCosineKernel harperPrimeCosineKernel
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hprime := Nat.prime_of_mem_primesBelow p.property
    have hqx : harperRankinEulerRadius p.1 a ^ 2 ≤ (p.1 : ℝ)⁻¹ := by
      rw [harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg hprime.pos a]
      exact mul_le_of_le_one_right (by positivity)
        (rpow_neg_le_one_of_one_le (by exact_mod_cast hprime.one_le) ha)
    have hcos := Real.neg_one_le_cos (u * Real.log (p.1 : ℝ))
    have hmul := mul_le_mul_of_nonneg_right hcos (sub_nonneg.mpr hqx)
    nlinarith
  exact hsum.trans (add_le_add le_rfl
    (candidate_rankinRadius_loss_le_log_normalizer_ratio y ha))

/-- Absolute ratio constant obtained from the existing Mertens upper bound
and the effective-cutoff lower bound. -/
noncomputable def candidateRankinNormalizerRatioConstant : ℝ :=
  2 * Real.exp (1 - Real.log (Real.log 2) +
    2 * (Real.log 4 + 4) / Real.log 2) / candidateRankinNormalizerConstant

theorem candidateRankinNormalizerRatioConstant_pos :
    0 < candidateRankinNormalizerRatioConstant := by
  unfold candidateRankinNormalizerRatioConstant
  exact div_pos (by positivity) candidateRankinNormalizerConstant_pos

/-- Uniform polynomial ratio of the critical and shifted normalizers. -/
theorem candidate_rankinNormalizer_ratio_le_polynomial
    {V : ℝ} (hV : 0 ≤ V) {y : ℕ} (hy : 4 ≤ y)
    (hsize : (1 + 4 * V) * Real.log 4 ≤ Real.log y) :
    Problem520.primeEnergyNormalizer y /
      harperRankinPrimeEnergyNormalizer y (4 * V / Real.log y) ≤
        candidateRankinNormalizerRatioConstant * (1 + 4 * V) := by
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hden : 0 < 1 + 4 * V := by positivity
  have hlow := candidate_rankinNormalizer_lower_polynomial hV hy hsize
  have hupp := Problem520.primeEnergyNormalizer_le_mertensConstant_mul_log
    (show 2 ≤ y by omega)
  have hr : 0 < candidateRankinNormalizerRatioConstant * (1 + 4 * V) :=
    mul_pos candidateRankinNormalizerRatioConstant_pos hden
  rw [div_le_iff₀ (harperRankinPrimeEnergyNormalizer_pos y _)]
  refine hupp.trans ?_
  calc
    _ = (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) *
        (candidateRankinNormalizerConstant * Real.log y / (2 * (1 + 4 * V))) := by
      unfold candidateRankinNormalizerRatioConstant
      field_simp [candidateRankinNormalizerConstant_pos.ne', hden.ne']
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hr.le

/-- The literal two-height correlation comparison now has polynomial
dependence on the Rankin parameter. No ballot-event estimate is assumed. -/
theorem candidate_rankinTwoHeightCorrelation_le_criticalKernel_polynomial
    {V : ℝ} (hV : 0 ≤ V) {y : ℕ} (hy : 4 ≤ y)
    (hsize : (1 + 4 * V) * Real.log 4 ≤ Real.log y) (t s : ℝ) :
    harperRankinTwoHeightCorrelation y (4 * V / Real.log y) t s ≤
      (candidateRankinNormalizerRatioConstant * (1 + 4 * V)) ^ 8 *
        Real.exp (2 * harperPrimeCosineKernel y (t - s) +
          2 * harperPrimeCosineKernel y (t + s) + 12) := by
  let a := 4 * V / Real.log (y : ℝ)
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  let R := candidateRankinNormalizerRatioConstant * (1 + 4 * V)
  have hR : 0 < R := mul_pos candidateRankinNormalizerRatioConstant_pos (by positivity)
  have hratio := Real.log_le_log
    (div_pos (Problem520.primeEnergyNormalizer_pos y)
      (harperRankinPrimeEnergyNormalizer_pos y a))
    (candidate_rankinNormalizer_ratio_le_polynomial hV hy hsize)
  have hdiff := candidate_rankinCosineKernel_le_critical_log_ratio y ha (t - s)
  have hsum := candidate_rankinCosineKernel_le_critical_log_ratio y ha (t + s)
  have hcorr := log_harperRankinTwoHeightCorrelation_le_differenceKernel y ha t s
  have hbound : Real.log (harperRankinTwoHeightCorrelation y a t s) ≤
      8 * Real.log R + (2 * harperPrimeCosineKernel y (t - s) +
        2 * harperPrimeCosineKernel y (t + s) + 12) := by
    change _ ≤ Real.log R at hratio
    linarith
  have h := Real.exp_le_exp.mpr hbound
  rw [Real.exp_log (harperRankinTwoHeightCorrelation_pos y ha t s), Real.exp_add] at h
  have hpow : Real.exp (8 * Real.log R) = R ^ 8 := by
    rw [show (8 : ℝ) * Real.log R = Real.log (R ^ 8) by rw [Real.log_pow]; norm_num]
    exact Real.exp_log (pow_pos hR _)
  rw [hpow] at h
  exact h

end Erdos.Problem1144
