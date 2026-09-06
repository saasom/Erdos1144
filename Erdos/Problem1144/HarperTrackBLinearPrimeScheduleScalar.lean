import Erdos.Problem1144.HarperTrackBLinearPrimeSchedule

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

namespace Erdos
namespace Problem1144

/-!
## Deterministic scalar Gaussian-tail facts for the concrete Track B schedule

This file keeps the purely arithmetic tail-budget checks separate from the
main schedule wrapper.  The analytic comparison fields are still supplied by
the final fresh-prime linear package; these lemmas only close the scalar
inequalities that do not depend on probability.
-/

theorem trackBLinearPrimeConcrete_countMean_le_Q_beta (j : ℕ) :
    trackBLinearPrimeConcreteScheduleSpec.countMean j ≤
      (trackBLinearPrimeConcreteScheduleSpec.Q j : ℝ) *
        trackBLinearPrimeConcreteScheduleSpec.beta j := by
  change (trackBLinearPrimeConcreteQ j : ℝ) / 4 ≤
    (trackBLinearPrimeConcreteQ j : ℝ) * ((1 : ℝ) / 4)
  rw [div_eq_mul_inv]
  norm_num

theorem trackBLinearPrimeConcrete_tailUpper_nonneg (j : ℕ) :
    0 ≤ trackBLinearPrimeConcreteScheduleSpec.tailUpper j := by
  norm_num [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteTailUpper]

theorem trackBLinearPrimeConcrete_pairCovUpper_nonneg (j : ℕ) :
    0 ≤ trackBLinearPrimeConcreteScheduleSpec.pairCovUpper j := by
  have hnonneg : 0 ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (by positivity) 4)
  change 0 ≤ 2 * (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹
  exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnonneg

theorem trackBLinearPrimeConcrete_countSecond_budget (j : ℕ) :
    (trackBLinearPrimeConcreteScheduleSpec.Q j : ℝ) *
        trackBLinearPrimeConcreteScheduleSpec.tailUpper j +
      (trackBLinearPrimeConcreteScheduleSpec.Q j : ℝ) ^ 2 *
        trackBLinearPrimeConcreteScheduleSpec.pairCovUpper j ≤
        trackBLinearPrimeConcreteScheduleSpec.countSecond j := by
  simp [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteTailUpper,
    trackBLinearPrimeConcretePairCovUpper, trackBLinearPrimeConcreteCountSecond]
  ring_nf
  rfl

theorem trackBLinearPrimeConcrete_inv_base_pow_ten_le_quarter (j : ℕ) :
    (((trackBLinearPrimeConcreteBase j : ℝ) ^ 10))⁻¹ ≤ (1 : ℝ) / 4 := by
  have hb2 : (2 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
    exact_mod_cast trackBLinearPrimeConcreteBase_two_le j
  have hpow : (4 : ℝ) ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 10 := by
    have hmono : (2 : ℝ) ^ 10 ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 10 :=
      pow_le_pow_left₀ (by norm_num) hb2 10
    norm_num at hmono
    exact le_trans (by norm_num) hmono
  have hpos : (0 : ℝ) < (trackBLinearPrimeConcreteBase j : ℝ) ^ 10 := by
    positivity
  simpa [one_div] using (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 4)).mpr hpow

theorem trackBLinearPrimeConcrete_gaussian_one_point_lower (j N : ℕ) :
    trackBLinearPrimeConcreteScheduleSpec.beta j +
        trackBLinearPrimeConcreteScheduleSpec.onePointSlack j ≤
      trackBLinearPrimeConcreteScheduleSpec.gaussianTail j N := by
  have hslack : trackBLinearPrimeConcreteScheduleSpec.onePointSlack j ≤ (1 : ℝ) / 4 := by
    simpa [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteOnePointSlack]
      using trackBLinearPrimeConcrete_inv_base_pow_ten_le_quarter j
  simp [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteBeta,
    trackBLinearPrimeConcreteGaussianTail] at hslack ⊢
  linarith

theorem trackBLinearPrimeConcrete_gaussian_pair_cov_upper (j N N' : ℕ) :
    trackBLinearPrimeConcreteScheduleSpec.gaussianPair j N N' -
        trackBLinearPrimeConcreteScheduleSpec.gaussianTail j N *
          trackBLinearPrimeConcreteScheduleSpec.gaussianTail j N' ≤
      trackBLinearPrimeConcreteScheduleSpec.gaussianPairCovUpper j := by
  simp [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteGaussianPair,
    trackBLinearPrimeConcreteGaussianTail, trackBLinearPrimeConcreteGaussianPairCovUpper]
  ring_nf
  rfl

theorem trackBLinearPrimeConcrete_inv_base_pow_ten_le_pow_four (j : ℕ) :
    (((trackBLinearPrimeConcreteBase j : ℝ) ^ 10))⁻¹ ≤
      (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹ := by
  have hb1 : (1 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
    exact_mod_cast (trackBLinearPrimeConcreteBase_one_lt j).le
  have hpow : (trackBLinearPrimeConcreteBase j : ℝ) ^ 4 ≤
      (trackBLinearPrimeConcreteBase j : ℝ) ^ 10 := by
    have hpow6 : (1 : ℝ) ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 6 :=
      one_le_pow₀ hb1
    have hpow4_nonneg : 0 ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 4 := by
      positivity
    have hmul :
        (trackBLinearPrimeConcreteBase j : ℝ) ^ 4 ≤
          (trackBLinearPrimeConcreteBase j : ℝ) ^ 4 *
            (trackBLinearPrimeConcreteBase j : ℝ) ^ 6 :=
      le_mul_of_one_le_right hpow4_nonneg hpow6
    have hpow' : (trackBLinearPrimeConcreteBase j : ℝ) ^ 4 ≤
        (trackBLinearPrimeConcreteBase j : ℝ) ^ (4 + 6) := by
      calc
        (trackBLinearPrimeConcreteBase j : ℝ) ^ 4
            ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 4 *
                (trackBLinearPrimeConcreteBase j : ℝ) ^ 6 := hmul
        _ = (trackBLinearPrimeConcreteBase j : ℝ) ^ (4 + 6) := by
          rw [pow_add]
    simpa using hpow'
  have hpos4 : (0 : ℝ) < (trackBLinearPrimeConcreteBase j : ℝ) ^ 4 := by
    positivity
  have hpos10 : (0 : ℝ) < (trackBLinearPrimeConcreteBase j : ℝ) ^ 10 := by
    positivity
  exact (inv_le_inv₀ hpos10 hpos4).mpr hpow

theorem trackBLinearPrimeConcrete_two_inv_base_pow_ten_le_pow_four (j : ℕ) :
    2 * (((trackBLinearPrimeConcreteBase j : ℝ) ^ 10))⁻¹ ≤
      (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹ := by
  have hb2 : (2 : ℝ) ≤ trackBLinearPrimeConcreteBase j := by
    exact_mod_cast trackBLinearPrimeConcreteBase_two_le j
  have hpow6 : (2 : ℝ) ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 6 := by
    have hmono : (2 : ℝ) ^ 6 ≤ (trackBLinearPrimeConcreteBase j : ℝ) ^ 6 :=
      pow_le_pow_left₀ (by norm_num) hb2 6
    exact le_trans (by norm_num) hmono
  have hpos6 : (0 : ℝ) < (trackBLinearPrimeConcreteBase j : ℝ) ^ 6 := by
    positivity
  have hinv6 : (((trackBLinearPrimeConcreteBase j : ℝ) ^ 6))⁻¹ ≤ (1 : ℝ) / 2 := by
    simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpow6
  have hpow_eq : (trackBLinearPrimeConcreteBase j : ℝ) ^ 10 =
      (trackBLinearPrimeConcreteBase j : ℝ) ^ 4 *
        (trackBLinearPrimeConcreteBase j : ℝ) ^ 6 := by
    rw [show 10 = 4 + 6 by norm_num, pow_add]
  calc
    2 * (((trackBLinearPrimeConcreteBase j : ℝ) ^ 10))⁻¹
        = (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹ *
            (2 * (((trackBLinearPrimeConcreteBase j : ℝ) ^ 6))⁻¹) := by
          rw [hpow_eq, mul_inv_rev]
          ring
    _ ≤ (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹ * 1 := by
          gcongr
          linarith
    _ = (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹ := by ring

theorem trackBLinearPrimeConcrete_pairCovBudget_le_pairCovUpper (j : ℕ) :
    trackBLinearPrimeConcreteScheduleSpec.gaussianPairCovUpper j +
        trackBLinearPrimeConcreteScheduleSpec.twoPointSlack j +
          trackBLinearPrimeConcreteScheduleSpec.productSlack j ≤
      trackBLinearPrimeConcreteScheduleSpec.pairCovUpper j := by
  have hle : (((trackBLinearPrimeConcreteBase j : ℝ) ^ 10))⁻¹ ≤
      (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹ :=
    trackBLinearPrimeConcrete_inv_base_pow_ten_le_pow_four j
  have htwo : 2 * (((trackBLinearPrimeConcreteBase j : ℝ) ^ 10))⁻¹ ≤
      (((trackBLinearPrimeConcreteBase j : ℝ) ^ 4))⁻¹ :=
    trackBLinearPrimeConcrete_two_inv_base_pow_ten_le_pow_four j
  simp [trackBLinearPrimeConcreteScheduleSpec, trackBLinearPrimeConcreteGaussianPairCovUpper,
    trackBLinearPrimeConcreteTwoPointSlack, trackBLinearPrimeConcreteProductSlack,
    trackBLinearPrimeConcretePairCovUpper]
  linarith

end Problem1144
end Erdos
