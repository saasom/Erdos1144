import Erdos.Problem1144.HarperRankinVarianceWindow
import Erdos.Problem520.HarperFejerInversion
import Erdos.Problem520.HarperQuarticBudget
import Mathlib.Probability.Distributions.Gaussian.Fernique

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Laws of Rankin-shifted centered prime blocks

This is the law-level interface needed to reuse the existing Fejér--Esseen
and Gaussian corridor infrastructure.  The discrete law is the pushforward
of the explicit shifted product cube, and the comparison law is the centered
Gaussian with exactly the same shifted block variance.
-/

/-- Law of one shifted centered finite prime block. -/
noncomputable def harperRankinCenteredLinearBlockLaw
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) : Measure ℝ :=
  Measure.map (harperRankinCenteredLinearPrimeBlockSum y S a t u)
    (harperRankinTiltedCubeLaw y a t)

instance harperRankinCenteredLinearBlockLaw_isProbabilityMeasure
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) :
    IsProbabilityMeasure (harperRankinCenteredLinearBlockLaw y S a t u) := by
  unfold harperRankinCenteredLinearBlockLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_of_finite _).aemeasurable

/-- Nonnegative-real wrapper for the exact shifted variance. -/
noncomputable def harperRankinLinearBlockVarianceNNReal
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) : NNReal :=
  ⟨harperRankinLinearBlockVariance y S a t u,
    harperRankinLinearBlockVariance_nonneg y S a t u⟩

@[simp] theorem coe_harperRankinLinearBlockVarianceNNReal
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) :
    (harperRankinLinearBlockVarianceNNReal y S a t u : ℝ) =
      harperRankinLinearBlockVariance y S a t u := rfl

/-- Centered Gaussian with the exact shifted block variance. -/
noncomputable def harperRankinGaussianBlockLaw
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) : Measure ℝ :=
  gaussianReal 0 (harperRankinLinearBlockVarianceNNReal y S a t u)

instance harperRankinGaussianBlockLaw_isProbabilityMeasure
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) :
    IsProbabilityMeasure (harperRankinGaussianBlockLaw y S a t u) := by
  unfold harperRankinGaussianBlockLaw
  infer_instance

/-- The shifted pushforward law has the already computed block
characteristic function. -/
theorem charFun_harperRankinCenteredLinearBlockLaw
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u v : ℝ) :
    charFun (harperRankinCenteredLinearBlockLaw y S a t u) v =
      harperRankinTiltedLinearPrimeBlockCharacteristic y S a t u v := by
  rw [charFun_apply_real]
  unfold harperRankinCenteredLinearBlockLaw
  rw [integral_map (measurable_of_finite _).aemeasurable (by fun_prop)]
  unfold harperRankinTiltedLinearPrimeBlockCharacteristic
    harperRankinCharacteristicBlockExponent
  apply integral_congr_ae
  exact ae_of_all _ fun eta ↦ by
    push_cast
    rfl

/-- Characteristic function of the variance-matched shifted Gaussian. -/
theorem charFun_harperRankinGaussianBlockLaw
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u v : ℝ) :
    charFun (harperRankinGaussianBlockLaw y S a t u) v =
      Complex.exp
        (-((v ^ 2 * harperRankinLinearBlockVariance y S a t u / 2 : ℝ) : ℂ)) := by
  unfold harperRankinGaussianBlockLaw
  rw [charFun_gaussianReal]
  simp only [coe_harperRankinLinearBlockVarianceNNReal,
    mul_zero, Complex.ofReal_zero, zero_mul, zero_sub]
  congr 1
  push_cast
  ring_nf

/-- Law-level shifted characteristic comparison on an arbitrary block. -/
theorem norm_charFun_harperRankinCenteredLinearBlockLaw_sub_gaussian_le
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (hprime : ∀ p ∈ S, 1 ≤ p.1) {a : ℝ} (ha : 0 ≤ a)
    (t u v : ℝ)
    (hsmall : ∀ p ∈ S,
      |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) ≤ 1)
    (hquad : ∀ p ∈ S,
      harperRankinPrimeGaussianQuadratic p.1 a t u v ≤ 1 / 2) :
    ‖charFun (harperRankinCenteredLinearBlockLaw y S a t u) v -
        charFun (harperRankinGaussianBlockLaw y S a t u) v‖ ≤
      (∑ p ∈ S, 8 * |v| ^ 3 *
        (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3) +
        ∑ p ∈ S, harperRankinPrimeGaussianQuadratic p.1 a t u v ^ 2 := by
  rw [charFun_harperRankinCenteredLinearBlockLaw,
    charFun_harperRankinGaussianBlockLaw]
  exact norm_harperRankinTiltedLinearPrimeBlockCharacteristic_sub_gaussian_le
    y S hprime ha t u v hsmall hquad

/-! ## First moments and exact Fejér inversion -/

theorem integrable_id_harperRankinCenteredLinearBlockLaw
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) :
    Integrable id (harperRankinCenteredLinearBlockLaw y S a t u) := by
  unfold harperRankinCenteredLinearBlockLaw
  rw [integrable_map_measure (by fun_prop)
    (measurable_of_finite _).aemeasurable]
  exact Integrable.of_finite

theorem integrable_id_harperRankinGaussianBlockLaw
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) :
    Integrable id (harperRankinGaussianBlockLaw y S a t u) := by
  unfold harperRankinGaussianBlockLaw
  exact IsGaussian.integrable_id

/-- The exact Fejér-smoothed CDF identity is unconditional for the shifted
block law. -/
theorem harperRankinCenteredLinearBlock_fejerSmoothedCDFIdentity
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) {T : ℝ} (hT : 0 < T) :
    Problem520.HarperFejerSmoothedCDFIdentity
      (harperRankinCenteredLinearBlockLaw y S a t u)
      (harperRankinGaussianBlockLaw y S a t u) T := by
  exact Problem520.harperFejerSmoothedCDFIdentity_of_integrable_id
    (harperRankinCenteredLinearBlockLaw y S a t u)
    (harperRankinGaussianBlockLaw y S a t u)
    (integrable_id_harperRankinCenteredLinearBlockLaw y S a t u)
    (integrable_id_harperRankinGaussianBlockLaw y S a t u) hT

/-! ## Shifted quartic budget -/

/-- Fourth-order Gaussian comparison budget of a shifted finite block. -/
noncomputable def harperRankinBlockGaussianQuarticBudget
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) : ℝ :=
  ∑ p ∈ S, (harperRankinCenteredLinearPrimeVariance p.1 a t u / 2) ^ 2

theorem harperRankinBlockGaussianQuarticBudget_nonneg
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u : ℝ) :
    0 ≤ harperRankinBlockGaussianQuarticBudget y S a t u := by
  unfold harperRankinBlockGaussianQuarticBudget
  exact Finset.sum_nonneg fun p hp ↦ sq_nonneg _

theorem sum_harperRankinPrimeGaussianQuadratic_sq_eq_quartic
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t u v : ℝ) :
    (∑ p ∈ S, harperRankinPrimeGaussianQuadratic p.1 a t u v ^ 2) =
      harperRankinBlockGaussianQuarticBudget y S a t u * |v| ^ 4 := by
  unfold harperRankinPrimeGaussianQuadratic
    harperRankinBlockGaussianQuarticBudget
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← sq_abs v]
  ring

theorem harperRankinCenteredLinearPrimeVariance_div_two_sq_le_cubicScale
    {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a) (t u : ℝ) :
    (harperRankinCenteredLinearPrimeVariance p a t u / 2) ^ 2 ≤
      (1 / 4 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  have hvar0 := harperRankinCenteredLinearPrimeVariance_nonneg p a t u
  have hvar := harperRankinCenteredLinearPrimeVariance_le_inv hp ha t u
  have hsquare := pow_le_pow_left₀ hvar0 hvar 2
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hsqrtPos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hpR
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt hpR.le
  have hinv : (p : ℝ)⁻¹ ^ 2 ≤
      (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
    rw [show (p : ℝ)⁻¹ ^ 2 = (Real.sqrt (p : ℝ))⁻¹ ^ 4 by
      rw [← hsqrtSq, inv_pow, ← pow_mul]
      norm_num]
    have hsqrtInvLe : (Real.sqrt (p : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hsqrtPos]
      exact Real.one_le_sqrt.mpr (by exact_mod_cast hp)
    calc
      (Real.sqrt (p : ℝ))⁻¹ ^ 4 =
          (Real.sqrt (p : ℝ))⁻¹ ^ 3 *
            (Real.sqrt (p : ℝ))⁻¹ := by ring
      _ ≤ (Real.sqrt (p : ℝ))⁻¹ ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left hsqrtInvLe (by positivity)
      _ = (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by ring
  calc
    (harperRankinCenteredLinearPrimeVariance p a t u / 2) ^ 2 =
        (1 / 4 : ℝ) *
          harperRankinCenteredLinearPrimeVariance p a t u ^ 2 := by ring
    _ ≤ (1 / 4 : ℝ) * (p : ℝ)⁻¹ ^ 2 := by gcongr
    _ ≤ (1 / 4 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by gcongr

/-- The shifted scheduled quartic budget has the same inverse-square-root
bound as the critical-line budget. -/
theorem harperRankinBlockGaussianQuarticBudget_scheduled_le
    (y j : ℕ) {a : ℝ} (ha : 0 ≤ a) (t u : ℝ) :
    harperRankinBlockGaussianQuarticBudget y
        (Problem520.harperScheduledPrimeBlock y j) a t u ≤
      (1 / 2 : ℝ) *
        (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ := by
  let S := Problem520.harperScheduledPrimeBlock y j
  unfold harperRankinBlockGaussianQuarticBudget
  calc
    (∑ p ∈ S,
        (harperRankinCenteredLinearPrimeVariance p.1 a t u / 2) ^ 2) ≤
        ∑ p ∈ S, (1 / 4 : ℝ) *
          (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3 := by
      apply Finset.sum_le_sum
      intro p hpS
      exact harperRankinCenteredLinearPrimeVariance_div_two_sq_le_cubicScale
        (by
          have := Problem520.sixteen_le_prime_of_mem_harperScheduledPrimeBlock hpS
          omega) ha t u
    _ = (3 / 8 : ℝ) * Problem520.harperBlockCubicRemainder y S := by
      unfold Problem520.harperBlockCubicRemainder
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hpS
      ring
    _ ≤ (3 / 8 : ℝ) *
        ((4 / 3 : ℝ) *
          (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹) := by
      gcongr
      exact Problem520.harperBlockCubicRemainder_scheduled_le y j
    _ = (1 / 2 : ℝ) *
        (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ := by ring

end

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.charFun_harperRankinCenteredLinearBlockLaw
#print axioms Erdos.Problem1144.charFun_harperRankinGaussianBlockLaw
#print axioms Erdos.Problem1144.harperRankinCenteredLinearBlock_fejerSmoothedCDFIdentity
#print axioms Erdos.Problem1144.harperRankinBlockGaussianQuarticBudget_scheduled_le
