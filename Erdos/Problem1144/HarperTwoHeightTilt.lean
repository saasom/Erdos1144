import Erdos.Problem1144.HarperCentralBallotCertificate
import Erdos.Problem520.HarperInverseEulerMoment

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Exact two-height tilted product law

The product of two Euler densities is again a product tilt of the fair prime
cube.  This module isolates its one-prime normalizer and normalized product
law.  It is the natural probability measure under which the remaining
two-height ballot intersection must be estimated.
-/

/-- Fair one-prime normalizer for the product of the squared Euler factors at
heights `t` and `s`. -/
noncomputable def harperTwoHeightPrimeNormalizer
    (p : Nat) (t s : Real) : Real :=
  ∫ b, Problem520.harperCoordinateFactor p t b *
    Problem520.harperCoordinateFactor p s b ∂Problem520.coin

theorem harperTwoHeightPrimeNormalizer_eq
    (p : Nat) (t s : Real) :
    harperTwoHeightPrimeNormalizer p t s =
      (Problem520.harperCoordinateFactor p t false *
          Problem520.harperCoordinateFactor p s false +
        Problem520.harperCoordinateFactor p t true *
          Problem520.harperCoordinateFactor p s true) / 2 := by
  unfold harperTwoHeightPrimeNormalizer
  rw [Problem520.integral_coin_bool]

theorem harperCoordinateFactor_false_eq_base_sub
    {p : Nat} (hp : p.Prime) (t : Real) :
    Problem520.harperCoordinateFactor p t false =
      1 + (p : Real)⁻¹ -
        2 * Real.cos (t * Real.log (p : Real)) / Real.sqrt (p : Real) := by
  rw [Problem520.harperCoordinateFactor,
    Problem520.harperEulerFactor_eq (fun _ => false) hp.pos]
  simp only [Problem520.ε, Bool.false_eq_true, if_false]
  ring

theorem harperCoordinateFactor_true_eq_base_add
    {p : Nat} (hp : p.Prime) (t : Real) :
    Problem520.harperCoordinateFactor p t true =
      1 + (p : Real)⁻¹ +
        2 * Real.cos (t * Real.log (p : Real)) / Real.sqrt (p : Real) := by
  rw [Problem520.harperCoordinateFactor,
    Problem520.harperEulerFactor_eq (fun _ => true) hp.pos]
  simp only [Problem520.ε, if_true]
  ring

/-- Exact correlation-kernel formula for the one-prime two-height
normalizer.  All dependence on the separation of the heights is contained in
the product of the two cosines. -/
theorem harperTwoHeightPrimeNormalizer_eq_correlation
    {p : Nat} (hp : p.Prime) (t s : Real) :
    harperTwoHeightPrimeNormalizer p t s =
      (1 + (p : Real)⁻¹) ^ (2 : Nat) +
        4 * Real.cos (t * Real.log (p : Real)) *
          Real.cos (s * Real.log (p : Real)) * (p : Real)⁻¹ := by
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  have hsqrt : Real.sqrt (p : Real) ≠ 0 :=
    (Real.sqrt_pos.2 hpR).ne'
  have hsqrtSq : Real.sqrt (p : Real) ^ (2 : Nat) = (p : Real) :=
    Real.sq_sqrt hpR.le
  let A : Real := 1 + (p : Real)⁻¹
  let Bt : Real :=
    2 * Real.cos (t * Real.log (p : Real)) / Real.sqrt (p : Real)
  let Bs : Real :=
    2 * Real.cos (s * Real.log (p : Real)) / Real.sqrt (p : Real)
  have htfalse : Problem520.harperCoordinateFactor p t false = A - Bt := by
    rw [Problem520.harperCoordinateFactor,
      Problem520.harperEulerFactor_eq (fun _ => false) hp.pos]
    simp only [Problem520.ε, Bool.false_eq_true, if_false]
    dsimp [A, Bt]
    ring
  have httrue : Problem520.harperCoordinateFactor p t true = A + Bt := by
    rw [Problem520.harperCoordinateFactor,
      Problem520.harperEulerFactor_eq (fun _ => true) hp.pos]
    simp only [Problem520.ε, if_true]
    dsimp [A, Bt]
    ring
  have hsfalse : Problem520.harperCoordinateFactor p s false = A - Bs := by
    rw [Problem520.harperCoordinateFactor,
      Problem520.harperEulerFactor_eq (fun _ => false) hp.pos]
    simp only [Problem520.ε, Bool.false_eq_true, if_false]
    dsimp [A, Bs]
    ring
  have hstrue : Problem520.harperCoordinateFactor p s true = A + Bs := by
    rw [Problem520.harperCoordinateFactor,
      Problem520.harperEulerFactor_eq (fun _ => true) hp.pos]
    simp only [Problem520.ε, if_true]
    dsimp [A, Bs]
    ring
  have hBtBs :
      Bt * Bs =
        4 * Real.cos (t * Real.log (p : Real)) *
          Real.cos (s * Real.log (p : Real)) * (p : Real)⁻¹ := by
    dsimp [Bt, Bs]
    field_simp [hsqrt]
    rw [hsqrtSq]
    ring
  rw [harperTwoHeightPrimeNormalizer_eq, htfalse, httrue, hsfalse, hstrue]
  rw [show ((A - Bt) * (A - Bs) + (A + Bt) * (A + Bs)) / 2 =
      A ^ (2 : Nat) + Bt * Bs by ring, hBtBs]

theorem harperTwoHeightPrimeNormalizer_pos
    {p : Nat} (hp : p.Prime) (t s : Real) :
    0 < harperTwoHeightPrimeNormalizer p t s := by
  rw [harperTwoHeightPrimeNormalizer_eq]
  exact div_pos
    (add_pos
      (mul_pos (Problem520.harperCoordinateFactor_pos hp t false)
        (Problem520.harperCoordinateFactor_pos hp s false))
      (mul_pos (Problem520.harperCoordinateFactor_pos hp t true)
        (Problem520.harperCoordinateFactor_pos hp s true)))
    (by norm_num)

/-- One-prime correlation after dividing out the two ordinary one-height
normalizers. -/
noncomputable def harperTwoHeightPrimeCorrelation
    (p : Nat) (t s : Real) : Real :=
  harperTwoHeightPrimeNormalizer p t s /
    (1 + (p : Real)⁻¹) ^ (2 : Nat)

theorem harperTwoHeightPrimeCorrelation_eq
    {p : Nat} (hp : p.Prime) (t s : Real) :
    harperTwoHeightPrimeCorrelation p t s =
      1 +
        (4 * Real.cos (t * Real.log (p : Real)) *
          Real.cos (s * Real.log (p : Real)) * (p : Real)⁻¹) /
            (1 + (p : Real)⁻¹) ^ (2 : Nat) := by
  unfold harperTwoHeightPrimeCorrelation
  rw [harperTwoHeightPrimeNormalizer_eq_correlation hp]
  have hden : (1 + (p : Real)⁻¹) ^ (2 : Nat) ≠ 0 := by positivity
  field_simp [hden]

theorem harperTwoHeightPrimeCorrelation_pos
    {p : Nat} (hp : p.Prime) (t s : Real) :
    0 < harperTwoHeightPrimeCorrelation p t s := by
  unfold harperTwoHeightPrimeCorrelation
  exact div_pos (harperTwoHeightPrimeNormalizer_pos hp t s) (by positivity)

private theorem four_mul_div_one_add_sq_le_linear_add_twelve_sq
    {r c : Real} (hr : 0 <= r) (hc : -1 <= c) :
    4 * c * r / (1 + r) ^ (2 : Nat) <=
      4 * c * r + 12 * r ^ (2 : Nat) := by
  have hden : 0 < (1 + r) ^ (2 : Nat) := by positivity
  have hdelta : 0 <= (1 + r) ^ (2 : Nat) - 1 := by nlinarith
  have hcmul :
      -(1 + r) ^ (2 : Nat) + 1 <=
        c * ((1 + r) ^ (2 : Nat) - 1) := by
    have := mul_le_mul_of_nonneg_right hc hdelta
    nlinarith
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg r, mul_nonneg hr (sq_nonneg r)]

/-- The logarithm of one normalized correlation factor is its oscillatory
`1/p` term plus an absolutely summable `O(1/p^2)` error. -/
theorem log_harperTwoHeightPrimeCorrelation_le
    {p : Nat} (hp : p.Prime) (t s : Real) :
    Real.log (harperTwoHeightPrimeCorrelation p t s) <=
      4 * Real.cos (t * Real.log (p : Real)) *
          Real.cos (s * Real.log (p : Real)) * (p : Real)⁻¹ +
        12 * (p : Real)⁻¹ ^ (2 : Nat) := by
  let ct := Real.cos (t * Real.log (p : Real))
  let cs := Real.cos (s * Real.log (p : Real))
  let r := (p : Real)⁻¹
  have hr : 0 <= r := by positivity
  have habs : |ct * cs| <= 1 := by
    calc
      |ct * cs| = |ct| * |cs| := abs_mul _ _
      _ <= 1 * 1 := mul_le_mul (Real.abs_cos_le_one _)
        (Real.abs_cos_le_one _)
        (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hc : -1 <= ct * cs := (abs_le.mp habs).1
  have hlinear :
      harperTwoHeightPrimeCorrelation p t s - 1 <=
        4 * ct * cs * r + 12 * r ^ (2 : Nat) := by
    rw [harperTwoHeightPrimeCorrelation_eq hp]
    simp only [add_sub_cancel_left]
    simpa only [ct, cs, r, mul_assoc] using
      (four_mul_div_one_add_sq_le_linear_add_twelve_sq hr hc)
  exact (Real.log_le_sub_one_of_pos
    (harperTwoHeightPrimeCorrelation_pos hp t s)).trans (by
      simpa only [ct, cs, r] using hlinear)

/-- The pure finite Euler correlation product. -/
noncomputable def harperTwoHeightCorrelation
    (y : Nat) (t s : Real) : Real :=
  ∏ p : Problem520.HarperPrimeIndex y,
    harperTwoHeightPrimeCorrelation p.1 t s

/-- Truncated reciprocal-prime cosine kernel. -/
noncomputable def harperPrimeCosineKernel
    (y : Nat) (u : Real) : Real :=
  ∑ p : Problem520.HarperPrimeIndex y,
    Real.cos (u * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹

/-- On the chosen positive vertical band the sum frequency is uniformly
separated from zero.  Hence only the difference frequency can create a
diagonal singularity. -/
theorem add_bounds_of_mem_harperLowerVerticalBand
    {t s : Real} (ht : t ∈ harperLowerVerticalBand)
    (hs : s ∈ harperLowerVerticalBand) :
    (2 / 3 : Real) <= t + s ∧ t + s <= 1 := by
  change (1 / 3 : Real) <= t ∧ t <= 1 / 2 at ht
  change (1 / 3 : Real) <= s ∧ s <= 1 / 2 at hs
  constructor <;> linarith

/-- Elementary phase stability at one prime.  A nearby height loses at most
`|t-s| log p` from the diagonal cosine-square contribution. -/
theorem cos_mul_cos_ge_sq_sub_abs_sub_mul_log
    {p : Nat} (hp : p.Prime) (t s : Real) :
    Real.cos (t * Real.log (p : Real)) *
        Real.cos (s * Real.log (p : Real)) >=
      Real.cos (t * Real.log (p : Real)) ^ (2 : Nat) -
        |t - s| * Real.log (p : Real) := by
  let L : Real := Real.log (p : Real)
  let ct : Real := Real.cos (t * L)
  let cs : Real := Real.cos (s * L)
  have hpR : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hL : 0 <= L := (Real.log_pos hpR).le
  have hphase : |cs - ct| <= |t - s| * L := by
    have hcos := Real.abs_cos_sub_cos_le (s * L) (t * L)
    calc
      |cs - ct| <= |s * L - t * L| := by
        simpa only [cs, ct] using hcos
      _ = |t - s| * L := by
        rw [show s * L - t * L = (s - t) * L by ring, abs_mul,
          abs_sub_comm, abs_of_nonneg hL]
  have hct : |ct| <= 1 := by
    dsimp only [ct]
    exact Real.abs_cos_le_one _
  have hproduct : |ct| * |cs - ct| <= |t - s| * L := by
    calc
      |ct| * |cs - ct| <= 1 * (|t - s| * L) :=
        mul_le_mul hct hphase (abs_nonneg _) (by positivity)
      _ = _ := one_mul _
  have habs := neg_abs_le (ct * (cs - ct))
  rw [abs_mul] at habs
  change ct * cs >= ct ^ (2 : Nat) - |t - s| * L
  nlinarith [hproduct]

/-- Absolutely summable finite remainder accompanying the cosine kernel. -/
noncomputable def harperPrimeSquareBudget (y : Nat) : Real :=
  ∑ p : Problem520.HarperPrimeIndex y,
    (p.1 : Real)⁻¹ ^ (2 : Nat)

theorem harperPrimeSquareBudget_nonneg (y : Nat) :
    0 <= harperPrimeSquareBudget y := by
  unfold harperPrimeSquareBudget
  positivity

/-- A coarse uniform bound is enough: the `1/p^2` error never contributes
to the singular two-height geometry. -/
theorem harperPrimeSquareBudget_le_one (y : Nat) :
    harperPrimeSquareBudget y <= 1 := by
  unfold harperPrimeSquareBudget
  have hsum :
      (∑ p : Problem520.HarperPrimeIndex y,
          (p.1 : Real)⁻¹ ^ (2 : Nat)) =
        ∑ p ∈ (y + 1).primesBelow,
          (p : Real)⁻¹ ^ (2 : Nat) := by
    exact Finset.sum_coe_sort ((y + 1).primesBelow)
      (fun p => (p : Real)⁻¹ ^ (2 : Nat))
  rw [hsum]
  calc
    (∑ p ∈ (y + 1).primesBelow,
        (p : Real)⁻¹ ^ (2 : Nat)) <=
      ∑ p ∈ Finset.Ioo 1 (y + 1),
        (p : Real)⁻¹ ^ (2 : Nat) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            have hpInfo := Nat.mem_primesBelow.mp hp
            exact Finset.mem_Ioo.mpr
              ⟨(Nat.prime_of_mem_primesBelow hp).one_lt, hpInfo.1⟩
          · intro p _hp _hnot
            positivity
    _ <= 1 := by
      have h := sum_Ioo_inv_sq_le (α := Real) 1 (y + 1)
      norm_num at h
      simpa only [inv_pow] using h

theorem harperTwoHeightCorrelation_pos
    (y : Nat) (t s : Real) :
    0 < harperTwoHeightCorrelation y t s := by
  unfold harperTwoHeightCorrelation
  exact Finset.prod_pos fun p _hp =>
    harperTwoHeightPrimeCorrelation_pos
      (Nat.prime_of_mem_primesBelow p.property) t s

/-- Finite logarithmic majorant for the full normalized correlation.  The
only nonsummable term left is the explicit prime cosine kernel. -/
theorem log_harperTwoHeightCorrelation_le
    (y : Nat) (t s : Real) :
    Real.log (harperTwoHeightCorrelation y t s) <=
      ∑ p : Problem520.HarperPrimeIndex y,
        (4 * Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹ +
          12 * (p.1 : Real)⁻¹ ^ (2 : Nat)) := by
  rw [harperTwoHeightCorrelation, Real.log_prod]
  · exact Finset.sum_le_sum fun p _hp =>
      log_harperTwoHeightPrimeCorrelation_le
        (Nat.prime_of_mem_primesBelow p.property) t s
  · intro p _hp
    exact (harperTwoHeightPrimeCorrelation_pos
      (Nat.prime_of_mem_primesBelow p.property) t s).ne'

/-- Product-to-sum form of the correlation majorant.  On the fixed positive
height band, `t+s` is bounded away from zero; all singular behavior is
therefore isolated in the difference kernel `t-s`. -/
theorem log_harperTwoHeightCorrelation_le_differenceKernel
    (y : Nat) (t s : Real) :
    Real.log (harperTwoHeightCorrelation y t s) <=
      2 * harperPrimeCosineKernel y (t - s) +
        2 * harperPrimeCosineKernel y (t + s) +
        12 * harperPrimeSquareBudget y := by
  refine (log_harperTwoHeightCorrelation_le y t s).trans_eq ?_
  unfold harperPrimeCosineKernel harperPrimeSquareBudget
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  have hsub :
      (t - s) * Real.log (p.1 : Real) =
        t * Real.log (p.1 : Real) - s * Real.log (p.1 : Real) := by ring
  have hadd :
      (t + s) * Real.log (p.1 : Real) =
        t * Real.log (p.1 : Real) + s * Real.log (p.1 : Real) := by ring
  rw [hsub, hadd, Real.cos_sub, Real.cos_add]
  ring

theorem harperTwoHeightCorrelation_le_exp_cosineKernel
    (y : Nat) (t s : Real) :
    harperTwoHeightCorrelation y t s <=
      Real.exp
        (∑ p : Problem520.HarperPrimeIndex y,
          (4 * Real.cos (t * Real.log (p.1 : Real)) *
              Real.cos (s * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹ +
            12 * (p.1 : Real)⁻¹ ^ (2 : Nat))) := by
  rw [← Real.exp_log (harperTwoHeightCorrelation_pos y t s)]
  exact Real.exp_le_exp.mpr (log_harperTwoHeightCorrelation_le y t s)

theorem harperTwoHeightCorrelation_le_exp_differenceKernel
    (y : Nat) (t s : Real) :
    harperTwoHeightCorrelation y t s <=
      Real.exp
        (2 * harperPrimeCosineKernel y (t - s) +
          2 * harperPrimeCosineKernel y (t + s) +
          12 * harperPrimeSquareBudget y) := by
  rw [← Real.exp_log (harperTwoHeightCorrelation_pos y t s)]
  exact Real.exp_le_exp.mpr
    (log_harperTwoHeightCorrelation_le_differenceKernel y t s)

theorem harperTwoHeightCorrelation_le_exp_differenceKernel_add_twelve
    (y : Nat) (t s : Real) :
    harperTwoHeightCorrelation y t s <=
      Real.exp
        (2 * harperPrimeCosineKernel y (t - s) +
          2 * harperPrimeCosineKernel y (t + s) + 12) := by
  refine (harperTwoHeightCorrelation_le_exp_differenceKernel y t s).trans ?_
  rw [Real.exp_le_exp]
  have hbudget := harperPrimeSquareBudget_le_one y
  nlinarith

/-- Normalized two-height mass of one sign. -/
noncomputable def harperTwoHeightCoinWeight
    (p : Nat) (t s : Real) (b : Bool) : Real :=
  Problem520.harperCoordinateFactor p t b *
      Problem520.harperCoordinateFactor p s b /
    (2 * harperTwoHeightPrimeNormalizer p t s)

theorem harperTwoHeightCoinWeight_nonneg
    (p : Nat) (t s : Real) (b : Bool) :
    0 <= harperTwoHeightCoinWeight p t s b := by
  unfold harperTwoHeightCoinWeight
  exact div_nonneg
    (mul_nonneg
      (Problem520.harperCoordinateFactor_nonneg p t b)
      (Problem520.harperCoordinateFactor_nonneg p s b))
    (mul_nonneg (by norm_num) (by
      unfold harperTwoHeightPrimeNormalizer
      exact integral_nonneg_of_ae (ae_of_all _ fun z =>
        mul_nonneg
          (Problem520.harperCoordinateFactor_nonneg p t z)
          (Problem520.harperCoordinateFactor_nonneg p s z))))

noncomputable def harperTwoHeightCoinWeightNNReal
    (p : Nat) (t s : Real) (b : Bool) : NNReal :=
  ⟨harperTwoHeightCoinWeight p t s b,
    harperTwoHeightCoinWeight_nonneg p t s b⟩

@[simp] theorem coe_harperTwoHeightCoinWeightNNReal
    (p : Nat) (t s : Real) (b : Bool) :
    (harperTwoHeightCoinWeightNNReal p t s b : Real) =
      harperTwoHeightCoinWeight p t s b := rfl

theorem harperTwoHeightCoinWeight_false_add_true
    {p : Nat} (hp : p.Prime) (t s : Real) :
    harperTwoHeightCoinWeight p t s false +
      harperTwoHeightCoinWeight p t s true = 1 := by
  unfold harperTwoHeightCoinWeight
  rw [← add_div, harperTwoHeightPrimeNormalizer_eq]
  have hsum :
      0 < Problem520.harperCoordinateFactor p t false *
            Problem520.harperCoordinateFactor p s false +
          Problem520.harperCoordinateFactor p t true *
            Problem520.harperCoordinateFactor p s true :=
    add_pos
      (mul_pos (Problem520.harperCoordinateFactor_pos hp t false)
        (Problem520.harperCoordinateFactor_pos hp s false))
      (mul_pos (Problem520.harperCoordinateFactor_pos hp t true)
        (Problem520.harperCoordinateFactor_pos hp s true))
  field_simp [hsum.ne']

theorem harperTwoHeightCoinWeightNNReal_false_add_true
    {p : Nat} (hp : p.Prime) (t s : Real) :
    harperTwoHeightCoinWeightNNReal p t s false +
      harperTwoHeightCoinWeightNNReal p t s true = 1 := by
  ext
  exact harperTwoHeightCoinWeight_false_add_true hp t s

/-- Exact sign bias under the two-height product tilt. -/
noncomputable def harperTwoHeightTiltBias
    (p : Nat) (t s : Real) : Real :=
  harperTwoHeightCoinWeight p t s true -
    harperTwoHeightCoinWeight p t s false

theorem harperTwoHeightTiltBias_eq
    {p : Nat} (hp : p.Prime) (t s : Real) :
    harperTwoHeightTiltBias p t s =
      (1 + (p : Real)⁻¹) *
          (2 * Real.cos (t * Real.log (p : Real)) / Real.sqrt (p : Real) +
            2 * Real.cos (s * Real.log (p : Real)) / Real.sqrt (p : Real)) /
        harperTwoHeightPrimeNormalizer p t s := by
  unfold harperTwoHeightTiltBias harperTwoHeightCoinWeight
  rw [harperCoordinateFactor_true_eq_base_add hp,
    harperCoordinateFactor_true_eq_base_add hp,
    harperCoordinateFactor_false_eq_base_sub hp,
    harperCoordinateFactor_false_eq_base_sub hp]
  field_simp [(harperTwoHeightPrimeNormalizer_pos hp t s).ne']
  ring

/-- One-coordinate two-height tilted probability law. -/
noncomputable def harperTwoHeightCoin
    (p : Nat) (_hp : p.Prime) (t s : Real) : Measure Bool :=
  (harperTwoHeightCoinWeightNNReal p t s false : ENNReal) •
      Measure.dirac false +
    (harperTwoHeightCoinWeightNNReal p t s true : ENNReal) •
      Measure.dirac true

instance harperTwoHeightCoin_isProbabilityMeasure
    (p : Nat) (hp : p.Prime) (t s : Real) :
    IsProbabilityMeasure (harperTwoHeightCoin p hp t s) where
  measure_univ := by
    simp [harperTwoHeightCoin]
    rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one]
    rw [← ENNReal.coe_add,
      harperTwoHeightCoinWeightNNReal_false_add_true hp]
    simp

@[simp] theorem harperTwoHeightCoin_apply_singleton
    (p : Nat) (hp : p.Prime) (t s : Real) (b : Bool) :
    harperTwoHeightCoin p hp t s {b} =
      (harperTwoHeightCoinWeightNNReal p t s b : ENNReal) := by
  cases b <;> simp [harperTwoHeightCoin] <;>
    rw [ENNReal.smul_def, smul_eq_mul, mul_one]

@[simp] theorem harperTwoHeightCoin_real_singleton
    (p : Nat) (hp : p.Prime) (t s : Real) (b : Bool) :
    (harperTwoHeightCoin p hp t s).real {b} =
      harperTwoHeightCoinWeight p t s b := by
  rw [Measure.real, harperTwoHeightCoin_apply_singleton]
  simp

/-- Expectation under one two-height tilted coin is its explicit biased
two-point average. -/
theorem integral_harperTwoHeightCoin
    (p : Nat) (hp : p.Prime) (t s : Real) (g : Bool -> Real) :
    (∫ b, g b ∂harperTwoHeightCoin p hp t s) =
      harperTwoHeightCoinWeight p t s false * g false +
        harperTwoHeightCoinWeight p t s true * g true := by
  rw [integral_fintype (Integrable.of_finite :
    Integrable g (harperTwoHeightCoin p hp t s))]
  simp only [harperTwoHeightCoin_real_singleton, smul_eq_mul]
  rw [Fintype.sum_bool]
  ring

theorem integral_cubeSign_harperTwoHeightCoin
    (p : Nat) (hp : p.Prime) (t s : Real) :
    (∫ b, Problem520.cubeSign b ∂harperTwoHeightCoin p hp t s) =
      harperTwoHeightTiltBias p t s := by
  rw [integral_harperTwoHeightCoin]
  change harperTwoHeightCoinWeight p t s false * (-1) +
      harperTwoHeightCoinWeight p t s true * 1 = _
  unfold harperTwoHeightTiltBias
  ring

/-- Mean drift, under the two-height law, of a prime increment centered for
the one-height tilt at `t` and observed at height `u`. -/
noncomputable def harperTwoHeightCenteredPrimeDrift
    (p : Nat) (t s u : Real) : Real :=
  (harperTwoHeightTiltBias p t s - Problem520.harperTiltBias p t) *
    (Real.cos (u * Real.log (p : Real)) / Real.sqrt (p : Real))

theorem integral_harperCenteredLinearPrimeIncrement_twoHeightCoin
    (p : Nat) (hp : p.Prime) (t s u : Real) :
    (∫ b, Problem520.harperCenteredLinearPrimeIncrement p t u b
        ∂harperTwoHeightCoin p hp t s) =
      harperTwoHeightCenteredPrimeDrift p t s u := by
  rw [integral_harperTwoHeightCoin]
  unfold Problem520.harperCenteredLinearPrimeIncrement
    Problem520.harperLinearPrimeIncrement
    harperTwoHeightCenteredPrimeDrift
  have hsum := harperTwoHeightCoinWeight_false_add_true hp t s
  unfold harperTwoHeightTiltBias
  simp only [Problem520.cubeSign, Bool.false_eq_true, if_false, if_true]
  calc
    _ = (harperTwoHeightCoinWeight p t s true -
          harperTwoHeightCoinWeight p t s false) *
            (Real.cos (u * Real.log (p : Real)) / Real.sqrt (p : Real)) -
        (harperTwoHeightCoinWeight p t s false +
          harperTwoHeightCoinWeight p t s true) *
            Problem520.harperTiltBias p t *
              (Real.cos (u * Real.log (p : Real)) /
                Real.sqrt (p : Real)) := by ring
    _ = _ := by rw [hsum]; ring

/-- After subtracting its explicit two-height drift, one prime increment has
the same sharp Hoeffding proxy as under the one-height law.  Bias changes the
center but not the length of the two-point range. -/
theorem hasSubgaussianMGF_harperTwoHeightCenteredPrimeIncrement
    (p : Nat) (hp : p.Prime) (t s u : Real) :
    HasSubgaussianMGF
      (fun b =>
        Problem520.harperCenteredLinearPrimeIncrement p t u b -
          harperTwoHeightCenteredPrimeDrift p t s u)
      (Problem520.harperLinearPrimeHoeffdingProxy p u)
      (harperTwoHeightCoin p hp t s) := by
  let c : Real :=
    Real.cos (u * Real.log (p : Real)) / Real.sqrt (p : Real)
  let d : Real := Problem520.harperTiltBias p t * c
  let X : Bool -> Real :=
    Problem520.harperCenteredLinearPrimeIncrement p t u
  have hX (b : Bool) : X b = Problem520.cubeSign b * c - d := by
    dsimp [X, c, d]
    unfold Problem520.harperCenteredLinearPrimeIncrement
      Problem520.harperLinearPrimeIncrement
    ring
  have hmem : ∀ b, X b ∈ Set.Icc (-|c| - d) (|c| - d) := by
    intro b
    rw [hX]
    have habs : |Problem520.cubeSign b * c| = |c| := by
      cases b <;> norm_num [Problem520.cubeSign]
    constructor
    · have h := neg_abs_le (Problem520.cubeSign b * c)
      rw [habs] at h
      linarith
    · have h := le_abs_self (Problem520.cubeSign b * c)
      rw [habs] at h
      linarith
  have hbase := hasSubgaussianMGF_of_mem_Icc
    (μ := harperTwoHeightCoin p hp t s)
    (X := X) (a := -|c| - d) (b := |c| - d)
    (measurable_of_finite X).aemeasurable
    (ae_of_all _ hmem)
  have hparam :
      ((‖(|c| - d) - (-|c| - d)‖₊ / 2) ^ (2 : Nat) : NNReal) =
        Problem520.harperLinearPrimeHoeffdingProxy p u := by
    apply NNReal.eq
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
      coe_nnnorm, Real.norm_eq_abs]
    have hdiff : (|c| - d) - (-|c| - d) = 2 * |c| := by ring
    rw [hdiff, abs_of_nonneg (by positivity : 0 <= 2 * |c|)]
    dsimp [c, Problem520.harperLinearPrimeHoeffdingProxy]
    rw [show 2 * |Real.cos (u * Real.log (p : Real)) /
        Real.sqrt (p : Real)| / 2 =
          |Real.cos (u * Real.log (p : Real)) /
            Real.sqrt (p : Real)| by ring,
      sq_abs]
    rfl
  rw [hparam] at hbase
  apply hbase.congr
  exact ae_of_all _ fun b => by
    dsimp only [X]
    rw [integral_harperCenteredLinearPrimeIncrement_twoHeightCoin]

/-- Exact off-diagonal drift formula.  Apart from positive factors, its sign
is the sign of the cosine product at the two heights.  This makes the
near-diagonal analytic task completely explicit. -/
theorem harperTwoHeightCenteredPrimeDrift_eq_product
    {p : Nat} (hp : p.Prime) (t s : Real) :
    harperTwoHeightCenteredPrimeDrift p t s t =
      let A : Real := 1 + (p : Real)⁻¹
      let qt : Real :=
        Real.cos (t * Real.log (p : Real)) / Real.sqrt (p : Real)
      let qs : Real :=
        Real.cos (s * Real.log (p : Real)) / Real.sqrt (p : Real)
      2 * qt * qs * (A ^ (2 : Nat) - (2 * qt) ^ (2 : Nat)) /
        (A * harperTwoHeightPrimeNormalizer p t s) := by
  let A : Real := 1 + (p : Real)⁻¹
  let qt : Real :=
    Real.cos (t * Real.log (p : Real)) / Real.sqrt (p : Real)
  let qs : Real :=
    Real.cos (s * Real.log (p : Real)) / Real.sqrt (p : Real)
  let M : Real := harperTwoHeightPrimeNormalizer p t s
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 < M := harperTwoHeightPrimeNormalizer_pos hp t s
  have hMformula : M = A ^ (2 : Nat) + 4 * qt * qs := by
    dsimp only [M]
    rw [harperTwoHeightPrimeNormalizer_eq,
      harperCoordinateFactor_false_eq_base_sub hp,
      harperCoordinateFactor_false_eq_base_sub hp,
      harperCoordinateFactor_true_eq_base_add hp,
      harperCoordinateFactor_true_eq_base_add hp]
    dsimp only [A, qt, qs]
    ring
  have hOneBias : Problem520.harperTiltBias p t = (2 * qt) / A := by
    have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
    have hsqrt : Real.sqrt (p : Real) ≠ 0 :=
      (Real.sqrt_pos.2 hpR).ne'
    unfold Problem520.harperTiltBias
    dsimp only [A, qt]
    field_simp [hsqrt]
  unfold harperTwoHeightCenteredPrimeDrift
  rw [harperTwoHeightTiltBias_eq hp, hOneBias]
  have hqt :
      2 * Real.cos (t * Real.log (p : Real)) / Real.sqrt (p : Real) =
        2 * qt := by
    dsimp only [qt]
    ring
  have hqs :
      2 * Real.cos (s * Real.log (p : Real)) / Real.sqrt (p : Real) =
        2 * qs := by
    dsimp only [qs]
    ring
  rw [hqt, hqs]
  change
    (A * (2 * qt + 2 * qs) / M - (2 * qt) / A) * qt =
      2 * qt * qs * (A ^ (2 : Nat) - (2 * qt) ^ (2 : Nat)) /
        (A * M)
  apply (eq_div_iff (mul_ne_zero hA.ne' hM.ne')).2
  field_simp [hA.ne', hM.ne']
  rw [hMformula]
  ring

/-- If the two prime phases have the same cosine sign, the corresponding
centered drift at the first height is nonnegative. -/
theorem harperTwoHeightCenteredPrimeDrift_nonneg_of_cos_mul_nonneg
    {p : Nat} (hp : p.Prime) (t s : Real)
    (hcos : 0 <=
      Real.cos (t * Real.log (p : Real)) *
        Real.cos (s * Real.log (p : Real))) :
    0 <= harperTwoHeightCenteredPrimeDrift p t s t := by
  rw [harperTwoHeightCenteredPrimeDrift_eq_product hp]
  let A : Real := 1 + (p : Real)⁻¹
  let qt : Real :=
    Real.cos (t * Real.log (p : Real)) / Real.sqrt (p : Real)
  let qs : Real :=
    Real.cos (s * Real.log (p : Real)) / Real.sqrt (p : Real)
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  have hsqrt : 0 < Real.sqrt (p : Real) := Real.sqrt_pos.2 hpR
  have hqtqs : 0 <= qt * qs := by
    dsimp only [qt, qs]
    rw [div_mul_div_comm]
    exact div_nonneg hcos (mul_nonneg hsqrt.le hsqrt.le)
  have hA : 0 < A := by dsimp [A]; positivity
  have hminus : 0 < A - 2 * qt := by
    have h := Problem520.harperCoordinateFactor_pos hp t false
    rw [harperCoordinateFactor_false_eq_base_sub hp] at h
    simpa only [A, qt, mul_div_assoc] using h
  have hplus : 0 < A + 2 * qt := by
    have h := Problem520.harperCoordinateFactor_pos hp t true
    rw [harperCoordinateFactor_true_eq_base_add hp] at h
    simpa only [A, qt, mul_div_assoc] using h
  have hgap : 0 <= A ^ (2 : Nat) - (2 * qt) ^ (2 : Nat) := by
    nlinarith [mul_pos hminus hplus]
  have hnum :
      0 <= 2 * qt * qs *
        (A ^ (2 : Nat) - (2 * qt) ^ (2 : Nat)) := by
    calc
      0 <= 2 * (qt * qs) *
          (A ^ (2 : Nat) - (2 * qt) ^ (2 : Nat)) :=
        mul_nonneg (mul_nonneg (by norm_num) hqtqs) hgap
      _ = _ := by ring
  exact div_nonneg
    hnum
    (mul_nonneg hA.le
      (harperTwoHeightPrimeNormalizer_pos hp t s).le)

/-- On the diagonal the second tilt pushes the path centered for the first
tilt upward.  This is the elementary drift mechanism that compensates for
the singular correlation normalizer near `t = s`. -/
theorem harperTwoHeightCenteredPrimeDrift_diagonal_nonneg
    {p : Nat} (hp : p.Prime) (t : Real) :
    0 <= harperTwoHeightCenteredPrimeDrift p t t t := by
  let A : Real := 1 + (p : Real)⁻¹
  let q : Real := Real.cos (t * Real.log (p : Real)) / Real.sqrt (p : Real)
  let M : Real := harperTwoHeightPrimeNormalizer p t t
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 < M := by
    exact harperTwoHeightPrimeNormalizer_pos hp t t
  have hfactorMinus : 0 < A - 2 * q := by
    have h := Problem520.harperCoordinateFactor_pos hp t false
    rw [harperCoordinateFactor_false_eq_base_sub hp] at h
    simpa only [A, q, mul_div_assoc] using h
  have hfactorPlus : 0 < A + 2 * q := by
    have h := Problem520.harperCoordinateFactor_pos hp t true
    rw [harperCoordinateFactor_true_eq_base_add hp] at h
    simpa only [A, q, mul_div_assoc] using h
  have hgap : 0 < A ^ (2 : Nat) - (2 * q) ^ (2 : Nat) := by
    nlinarith [mul_pos hfactorMinus hfactorPlus]
  have hMformula : M = A ^ (2 : Nat) + (2 * q) ^ (2 : Nat) := by
    dsimp only [M]
    rw [harperTwoHeightPrimeNormalizer_eq,
      harperCoordinateFactor_false_eq_base_sub hp,
      harperCoordinateFactor_true_eq_base_add hp]
    dsimp only [A, q]
    ring
  have hOneBias : Problem520.harperTiltBias p t = (2 * q) / A := by
    have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
    have hsqrt : Real.sqrt (p : Real) ≠ 0 :=
      (Real.sqrt_pos.2 hpR).ne'
    unfold Problem520.harperTiltBias
    dsimp only [A, q]
    field_simp [hsqrt]
  have hDrift :
      harperTwoHeightCenteredPrimeDrift p t t t =
        2 * q ^ (2 : Nat) *
          (A ^ (2 : Nat) - (2 * q) ^ (2 : Nat)) / (A * M) := by
    unfold harperTwoHeightCenteredPrimeDrift
    rw [harperTwoHeightTiltBias_eq hp, hOneBias]
    have hq :
        2 * Real.cos (t * Real.log (p : Real)) / Real.sqrt (p : Real) =
          2 * q := by
      dsimp only [q]
      ring
    rw [hq]
    change
      (A * (2 * q + 2 * q) / M - (2 * q) / A) * q = _
    have hMsum : A ^ (2 : Nat) + (2 * q) ^ (2 : Nat) ≠ 0 := by
      rw [← hMformula]
      exact hM.ne'
    rw [hMformula]
    field_simp [hA.ne', hMsum]
    ring
  rw [hDrift]
  exact div_nonneg
    (mul_nonneg (by positivity) hgap.le)
    (mul_nonneg hA.le hM.le)

/-- On the diagonal the two-height drift is exactly the ordinary one-height
variance multiplied by an explicit likelihood ratio. -/
theorem harperTwoHeightCenteredPrimeDrift_diagonal_eq_variance_mul
    {p : Nat} (hp : p.Prime) (t : Real) :
    harperTwoHeightCenteredPrimeDrift p t t t =
      (2 * (1 + (p : Real)⁻¹) /
        harperTwoHeightPrimeNormalizer p t t) *
          Problem520.harperLinearPrimeCenteredVariance p t t := by
  rw [harperTwoHeightCenteredPrimeDrift_eq_product hp]
  let A : Real := 1 + (p : Real)⁻¹
  let q : Real :=
    Real.cos (t * Real.log (p : Real)) / Real.sqrt (p : Real)
  let M : Real := harperTwoHeightPrimeNormalizer p t t
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 < M := harperTwoHeightPrimeNormalizer_pos hp t t
  have hBias : Problem520.harperTiltBias p t = 2 * q / A := by
    have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
    have hsqrt : Real.sqrt (p : Real) ≠ 0 :=
      (Real.sqrt_pos.2 hpR).ne'
    unfold Problem520.harperTiltBias
    dsimp only [A, q]
    field_simp [hsqrt]
  unfold Problem520.harperLinearPrimeCenteredVariance
  change
    2 * q * q * (A ^ (2 : Nat) - (2 * q) ^ (2 : Nat)) /
        (A * M) =
      (2 * A / M) * (q ^ (2 : Nat) *
        (1 - Problem520.harperTiltBias p t ^ (2 : Nat)))
  rw [hBias]
  field_simp [hA.ne', hM.ne']

/-- From prime `16` onward the diagonal likelihood ratio is at least one.
Thus the singular two-height tilt creates at least one full one-height
variance unit of upward drift per coordinate. -/
theorem one_le_two_mul_base_div_twoHeightPrimeNormalizer_diagonal
    {p : Nat} (hp : p.Prime) (hp16 : 16 <= p) (t : Real) :
    1 <= 2 * (1 + (p : Real)⁻¹) /
      harperTwoHeightPrimeNormalizer p t t := by
  let x : Real := p
  let A : Real := 1 + x⁻¹
  let q : Real := Real.cos (t * Real.log x) / Real.sqrt x
  let M : Real := harperTwoHeightPrimeNormalizer p t t
  have hx : 0 < x := by dsimp [x]; exact_mod_cast hp.pos
  have hx16 : (16 : Real) <= x := by
    dsimp only [x]
    exact_mod_cast hp16
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 < M := harperTwoHeightPrimeNormalizer_pos hp t t
  have hsqrtSq : Real.sqrt x ^ (2 : Nat) = x := Real.sq_sqrt hx.le
  have hcosSq : Real.cos (t * Real.log x) ^ (2 : Nat) <= 1 := by
    nlinarith [Real.neg_one_le_cos (t * Real.log x),
      Real.cos_le_one (t * Real.log x)]
  have hqSq : q ^ (2 : Nat) <= x⁻¹ := by
    dsimp only [q]
    rw [div_pow, hsqrtSq, inv_eq_one_div]
    exact div_le_div_of_nonneg_right hcosSq hx.le
  have hfour : 4 * x⁻¹ <= 1 - x⁻¹ ^ (2 : Nat) := by
    field_simp [hx.ne']
    nlinarith [sq_nonneg (x - 3)]
  have hMformula : M = A ^ (2 : Nat) + (2 * q) ^ (2 : Nat) := by
    dsimp only [M]
    rw [harperTwoHeightPrimeNormalizer_eq,
      harperCoordinateFactor_false_eq_base_sub hp,
      harperCoordinateFactor_true_eq_base_add hp]
    dsimp only [A, q, x]
    ring
  have hMle : M <= 2 * A := by
    rw [hMformula]
    calc
      A ^ (2 : Nat) + (2 * q) ^ (2 : Nat) <=
          A ^ (2 : Nat) + 4 * x⁻¹ := by nlinarith
      _ <= 2 * A := by
        dsimp only [A]
        nlinarith [hfour]
  change 1 <= 2 * A / M
  exact (le_div_iff₀ hM).2 (by linarith)

theorem harperLinearPrimeCenteredVariance_le_twoHeightDiagonalDrift
    {p : Nat} (hp : p.Prime) (hp16 : 16 <= p) (t : Real) :
    Problem520.harperLinearPrimeCenteredVariance p t t <=
      harperTwoHeightCenteredPrimeDrift p t t t := by
  rw [harperTwoHeightCenteredPrimeDrift_diagonal_eq_variance_mul hp]
  have hratio :=
    one_le_two_mul_base_div_twoHeightPrimeNormalizer_diagonal hp hp16 t
  have hvar :
      0 <= Problem520.harperLinearPrimeCenteredVariance p t t := by
    unfold Problem520.harperLinearPrimeCenteredVariance
    exact mul_nonneg (sq_nonneg _)
      ((by norm_num : (0 : Real) <= 3 / 4).trans
        (Problem520.three_fourths_le_one_sub_harperTiltBias_sq hp16 t))
  exact (one_mul _).symm.trans_le
    (mul_le_mul_of_nonneg_right hratio hvar)

/-- Total mean drift of a centered linearized path over a finite prime
block under the two-height tilt. -/
noncomputable def harperTwoHeightCenteredBlockDrift
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s u : Real) : Real :=
  ∑ p ∈ S, harperTwoHeightCenteredPrimeDrift p.1 t s u

/-- The diagonal upward-drift mechanism is hereditary: it holds for every
finite prime block, with no condition on how the block was chosen. -/
theorem harperTwoHeightCenteredBlockDrift_diagonal_nonneg
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y)) (t : Real) :
    0 <= harperTwoHeightCenteredBlockDrift y S t t t := by
  unfold harperTwoHeightCenteredBlockDrift
  exact Finset.sum_nonneg fun p hpS =>
    harperTwoHeightCenteredPrimeDrift_diagonal_nonneg
      (Nat.prime_of_mem_primesBelow p.property) t

/-- Every scheduled block has diagonal upward drift at least its ordinary
one-height variance. -/
theorem harperLinearBlockVariance_le_twoHeightDiagonalDrift_scheduled
    (y j : Nat) (t : Real) :
    Problem520.harperLinearBlockVariance y
        (Problem520.harperScheduledPrimeBlock y j) t t <=
      harperTwoHeightCenteredBlockDrift y
        (Problem520.harperScheduledPrimeBlock y j) t t t := by
  unfold Problem520.harperLinearBlockVariance
    harperTwoHeightCenteredBlockDrift
  apply Finset.sum_le_sum
  intro p hpS
  exact harperLinearPrimeCenteredVariance_le_twoHeightDiagonalDrift
    (Nat.prime_of_mem_primesBelow p.property)
    (Problem520.sixteen_le_prime_of_mem_harperScheduledPrimeBlock hpS) t

/-- Sharp scheduled-block test on every central band: diagonal drift is more
than `1/3`, while the Hoeffding proxy is less than `1/2`. -/
theorem exists_harperScheduledCentralBandTwoHeightDiagonal_bounds :
    ∃ J : Nat, ∀ d j y : Nat, J + d <= j ->
      Problem520.harperBlockEndpoint (j + 1) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
            (1 / 3 : Real) <
                harperTwoHeightCenteredBlockDrift y
                  (Problem520.harperScheduledPrimeBlock y j) t t t ∧
              (Problem520.harperLinearBlockHoeffdingProxy y
                (Problem520.harperScheduledPrimeBlock y j) t : Real) <
                  1 / 2 := by
  obtain ⟨J, hvariance⟩ :=
    Problem520.exists_harperScheduledCentralBandDiagonalVariance_third_threeEighths
  refine ⟨J, ?_⟩
  intro d j y hj hy t htLower htUpper
  have hvar := hvariance d j y hj hy t htLower htUpper
  have hdrift :=
    harperLinearBlockVariance_le_twoHeightDiagonalDrift_scheduled y j t
  have hproxy :=
    Problem520.three_fourths_mul_harperLinearBlockHoeffdingProxy_le_variance
      y (Problem520.harperScheduledPrimeBlock y j)
      (fun p hpS =>
        Problem520.sixteen_le_prime_of_mem_harperScheduledPrimeBlock hpS)
      t t
  constructor
  · exact hvar.1.trans_le hdrift
  · nlinarith

/-- Product of the one-prime two-height normalizers. -/
noncomputable def harperTwoHeightNormalizer
    (y : Nat) (t s : Real) : Real :=
  ∏ p : Problem520.HarperPrimeIndex y,
    harperTwoHeightPrimeNormalizer p.1 t s

theorem harperTwoHeightNormalizer_pos
    (y : Nat) (t s : Real) : 0 < harperTwoHeightNormalizer y t s := by
  unfold harperTwoHeightNormalizer
  exact Finset.prod_pos fun p _hp =>
    harperTwoHeightPrimeNormalizer_pos
      (Nat.prime_of_mem_primesBelow p.property) t s

/-- Exact split of the two-height normalizer into the square of the usual
energy normalizer and the pure cosine-correlation product. -/
theorem harperTwoHeightNormalizer_eq_energy_sq_mul_correlation
    (y : Nat) (t s : Real) :
    harperTwoHeightNormalizer y t s =
      Problem520.primeEnergyNormalizer y ^ (2 : Nat) *
        harperTwoHeightCorrelation y t s := by
  unfold harperTwoHeightNormalizer harperTwoHeightCorrelation
  calc
    (∏ p : Problem520.HarperPrimeIndex y,
        harperTwoHeightPrimeNormalizer p.1 t s) =
      ∏ p : Problem520.HarperPrimeIndex y,
        ((1 + (p.1 : Real)⁻¹) ^ (2 : Nat) *
          harperTwoHeightPrimeCorrelation p.1 t s) := by
            apply Finset.prod_congr rfl
            intro p _hp
            unfold harperTwoHeightPrimeCorrelation
            have hden : (1 + (p.1 : Real)⁻¹) ^ (2 : Nat) ≠ 0 := by
              positivity
            field_simp [hden]
    _ = (∏ p : Problem520.HarperPrimeIndex y,
          (1 + (p.1 : Real)⁻¹) ^ (2 : Nat)) *
        ∏ p : Problem520.HarperPrimeIndex y,
          harperTwoHeightPrimeCorrelation p.1 t s := by
            rw [Finset.prod_mul_distrib]
    _ = (∏ p : Problem520.HarperPrimeIndex y,
          (1 + (p.1 : Real)⁻¹)) ^ (2 : Nat) *
        ∏ p : Problem520.HarperPrimeIndex y,
          harperTwoHeightPrimeCorrelation p.1 t s := by
            rw [Finset.prod_pow]
    _ = Problem520.primeEnergyNormalizer y ^ (2 : Nat) *
        ∏ p : Problem520.HarperPrimeIndex y,
          harperTwoHeightPrimeCorrelation p.1 t s := by
            rw [Problem520.prod_harperCoordinateNormalizer]

/-- The normalized finite product law for the two-height tilt. -/
noncomputable def harperTwoHeightCubeLaw
    (y : Nat) (t s : Real) : Measure (Problem520.HarperPrimeCube y) :=
  Measure.pi fun p : Problem520.HarperPrimeIndex y =>
    harperTwoHeightCoin p.1
      (Nat.prime_of_mem_primesBelow p.property) t s

instance harperTwoHeightCubeLaw_isProbabilityMeasure
    (y : Nat) (t s : Real) :
    IsProbabilityMeasure (harperTwoHeightCubeLaw y t s) := by
  unfold harperTwoHeightCubeLaw
  infer_instance

/-- Coordinates remain independent under the explicit two-height product
law. -/
theorem iIndepFun_harperTwoHeightCube_coordinates
    (y : Nat) (t s : Real) :
    iIndepFun
      (fun p : Problem520.HarperPrimeIndex y =>
        fun eta : Problem520.HarperPrimeCube y => eta p)
      (harperTwoHeightCubeLaw y t s) := by
  unfold harperTwoHeightCubeLaw
  exact iIndepFun_pi
    (X := fun _ : Problem520.HarperPrimeIndex y => id)
    (fun _ => aemeasurable_id)

/-- Every coordinate of the two-height cube has the corresponding explicit
two-height tilted coin as its marginal law. -/
theorem measurePreserving_harperTwoHeightCube_eval
    (y : Nat) (t s : Real) (p : Problem520.HarperPrimeIndex y) :
    MeasurePreserving
      (fun eta : Problem520.HarperPrimeCube y => eta p)
      (harperTwoHeightCubeLaw y t s)
      (harperTwoHeightCoin p.1
        (Nat.prime_of_mem_primesBelow p.property) t s) := by
  unfold harperTwoHeightCubeLaw
  exact measurePreserving_eval
    (fun q : Problem520.HarperPrimeIndex y =>
      harperTwoHeightCoin q.1
        (Nat.prime_of_mem_primesBelow q.property) t s) p

/-- Integration of a one-coordinate observable under the two-height cube
reduces exactly to its two-point marginal. -/
theorem integral_harperTwoHeightCube_eval
    (y : Nat) (t s : Real) (p : Problem520.HarperPrimeIndex y)
    (g : Bool -> Real) :
    (∫ eta, g (eta p) ∂harperTwoHeightCubeLaw y t s) =
      ∫ b, g b ∂harperTwoHeightCoin p.1
        (Nat.prime_of_mem_primesBelow p.property) t s := by
  have hmp := measurePreserving_harperTwoHeightCube_eval y t s p
  calc
    (∫ eta, g (eta p) ∂harperTwoHeightCubeLaw y t s) =
        ∫ b, g b ∂Measure.map
          (fun eta : Problem520.HarperPrimeCube y => eta p)
          (harperTwoHeightCubeLaw y t s) := by
      symm
      exact integral_map hmp.measurable.aemeasurable
        (measurable_of_finite g).aestronglyMeasurable
    _ = ∫ b, g b ∂harperTwoHeightCoin p.1
          (Nat.prime_of_mem_primesBelow p.property) t s := by
      rw [hmp.map_eq]

/-- The exact expectation of a centered finite prime block under the
two-height product law is its explicit drift sum. -/
theorem integral_harperCenteredLinearPrimeBlockSum_twoHeightCube
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s u : Real) :
    (∫ eta, Problem520.harperCenteredLinearPrimeBlockSum y S t u eta
        ∂harperTwoHeightCubeLaw y t s) =
      harperTwoHeightCenteredBlockDrift y S t s u := by
  unfold Problem520.harperCenteredLinearPrimeBlockSum
    harperTwoHeightCenteredBlockDrift
  rw [integral_finset_sum S fun _ _ => Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro p hpS
  rw [integral_harperTwoHeightCube_eval,
    integral_harperCenteredLinearPrimeIncrement_twoHeightCoin]

/-- A whole finite prime block, after subtracting its exact two-height drift,
is sub-Gaussian with the usual sum of fair-sign proxies. -/
theorem hasSubgaussianMGF_harperTwoHeightCenteredPrimeBlockSum
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s u : Real) :
    HasSubgaussianMGF
      (fun eta =>
        Problem520.harperCenteredLinearPrimeBlockSum y S t u eta -
          harperTwoHeightCenteredBlockDrift y S t s u)
      (Problem520.harperLinearBlockHoeffdingProxy y S u)
      (harperTwoHeightCubeLaw y t s) := by
  let X : Problem520.HarperPrimeIndex y ->
      Problem520.HarperPrimeCube y -> Real := fun p eta =>
    Problem520.harperCenteredLinearPrimeIncrement p.1 t u (eta p) -
      harperTwoHeightCenteredPrimeDrift p.1 t s u
  have hindep : iIndepFun X (harperTwoHeightCubeLaw y t s) := by
    have h := (iIndepFun_harperTwoHeightCube_coordinates y t s).comp
      (fun p b =>
        Problem520.harperCenteredLinearPrimeIncrement p.1 t u b -
          harperTwoHeightCenteredPrimeDrift p.1 t s u)
      (fun _p => measurable_of_finite _)
    simpa only [X, Function.comp_apply] using h
  have hcoordinate : ∀ p ∈ S,
      HasSubgaussianMGF (X p)
        (Problem520.harperLinearPrimeHoeffdingProxy p.1 u)
        (harperTwoHeightCubeLaw y t s) := by
    intro p hpS
    have hcoin :=
      hasSubgaussianMGF_harperTwoHeightCenteredPrimeIncrement p.1
        (Nat.prime_of_mem_primesBelow p.property) t s u
    have hmp := measurePreserving_harperTwoHeightCube_eval y t s p
    have hcoinMap :
        HasSubgaussianMGF
          (fun b =>
            Problem520.harperCenteredLinearPrimeIncrement p.1 t u b -
              harperTwoHeightCenteredPrimeDrift p.1 t s u)
          (Problem520.harperLinearPrimeHoeffdingProxy p.1 u)
          ((harperTwoHeightCubeLaw y t s).map
            (fun eta : Problem520.HarperPrimeCube y => eta p)) := by
      simpa only [hmp.map_eq] using hcoin
    have hpull := HasSubgaussianMGF.of_map
      hmp.measurable.aemeasurable hcoinMap
    simpa only [X, Function.comp_apply] using hpull
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun
    hindep (s := S) hcoordinate
  simpa only [X, Problem520.harperCenteredLinearPrimeBlockSum,
    harperTwoHeightCenteredBlockDrift, Finset.sum_sub_distrib] using hsum

/-- One-sided endpoint bound under the two-height law.  If the explicit drift
exceeds an upper barrier `U`, the chance that the centered block sum remains
below `U` has the corresponding Gaussian decay. -/
theorem harperTwoHeightCubeLaw_blockSum_le
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s u U : Real)
    (hU : U <= harperTwoHeightCenteredBlockDrift y S t s u) :
    (harperTwoHeightCubeLaw y t s).real
        {eta |
          Problem520.harperCenteredLinearPrimeBlockSum y S t u eta <= U} <=
      Real.exp
        (-(harperTwoHeightCenteredBlockDrift y S t s u - U) ^ (2 : Nat) /
          (2 * (Problem520.harperLinearBlockHoeffdingProxy y S u : Real))) := by
  let Z : Problem520.HarperPrimeCube y -> Real := fun eta =>
    Problem520.harperCenteredLinearPrimeBlockSum y S t u eta -
      harperTwoHeightCenteredBlockDrift y S t s u
  have hsub : HasSubgaussianMGF Z
      (Problem520.harperLinearBlockHoeffdingProxy y S u)
      (harperTwoHeightCubeLaw y t s) := by
    simpa only [Z] using
      hasSubgaussianMGF_harperTwoHeightCenteredPrimeBlockSum y S t s u
  have htail := hsub.neg.measure_ge_le (sub_nonneg.mpr hU)
  have hevent :
      {eta : Problem520.HarperPrimeCube y |
          Problem520.harperCenteredLinearPrimeBlockSum y S t u eta <= U} =
        {eta |
          harperTwoHeightCenteredBlockDrift y S t s u - U <= -Z eta} := by
    ext eta
    change
      Problem520.harperCenteredLinearPrimeBlockSum y S t u eta <= U ↔
        harperTwoHeightCenteredBlockDrift y S t s u - U <=
          -(Problem520.harperCenteredLinearPrimeBlockSum y S t u eta -
            harperTwoHeightCenteredBlockDrift y S t s u)
    constructor <;> intro h <;> linarith
  rw [hevent]
  simpa only [Pi.neg_apply] using htail

@[simp] theorem harperTwoHeightCubeLaw_real_singleton
    (y : Nat) (t s : Real) (eta : Problem520.HarperPrimeCube y) :
    (harperTwoHeightCubeLaw y t s).real {eta} =
      ∏ p : Problem520.HarperPrimeIndex y,
        harperTwoHeightCoinWeight p.1 t s (eta p) := by
  rw [Measure.real, harperTwoHeightCubeLaw, Measure.pi_singleton,
    ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [← Measure.real, harperTwoHeightCoin_real_singleton]

theorem harperTwoHeightPrimeNormalizer_mul_weight
    {p : Nat} (hp : p.Prime) (t s : Real) (b : Bool) :
    harperTwoHeightPrimeNormalizer p t s *
        harperTwoHeightCoinWeight p t s b =
      Problem520.harperCoordinateFactor p t b *
        Problem520.harperCoordinateFactor p s b * (1 / 2 : Real) := by
  unfold harperTwoHeightCoinWeight
  field_simp [(harperTwoHeightPrimeNormalizer_pos hp t s).ne']

/-- Pointwise Radon--Nikodym identity for the two-height product tilt. -/
theorem harperTwoHeightNormalizer_mul_cubeLaw_singleton
    (y : Nat) (t s : Real) (eta : Problem520.HarperPrimeCube y) :
    harperTwoHeightNormalizer y t s *
        (harperTwoHeightCubeLaw y t s).real {eta} =
      Problem520.harperCubeDensity y t eta *
        Problem520.harperCubeDensity y s eta *
        (Measure.pi (fun _ : Problem520.HarperPrimeIndex y =>
          Problem520.coin)).real {eta} := by
  rw [harperTwoHeightCubeLaw_real_singleton,
    Problem520.fairHarperCubeLaw_real_singleton]
  unfold harperTwoHeightNormalizer Problem520.harperCubeDensity
  calc
    (∏ p : Problem520.HarperPrimeIndex y,
        harperTwoHeightPrimeNormalizer p.1 t s) *
        ∏ p : Problem520.HarperPrimeIndex y,
          harperTwoHeightCoinWeight p.1 t s (eta p) =
      ∏ p : Problem520.HarperPrimeIndex y,
        (harperTwoHeightPrimeNormalizer p.1 t s *
          harperTwoHeightCoinWeight p.1 t s (eta p)) := by
            rw [Finset.prod_mul_distrib]
    _ = ∏ p : Problem520.HarperPrimeIndex y,
        (Problem520.harperCoordinateFactor p.1 t (eta p) *
          Problem520.harperCoordinateFactor p.1 s (eta p) *
          (1 / 2 : Real)) := by
            apply Finset.prod_congr rfl
            intro p _hp
            exact harperTwoHeightPrimeNormalizer_mul_weight
              (Nat.prime_of_mem_primesBelow p.property) t s (eta p)
    _ = (∏ p : Problem520.HarperPrimeIndex y,
          Problem520.harperCoordinateFactor p.1 t (eta p)) *
        (∏ p : Problem520.HarperPrimeIndex y,
          Problem520.harperCoordinateFactor p.1 s (eta p)) *
        ∏ _p : Problem520.HarperPrimeIndex y, (1 / 2 : Real) := by
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

/-- Exact two-height change of measure for an arbitrary function on the
finite prime cube. -/
theorem harperTwoHeightNormalizer_mul_integral_cubeLaw_eq
    (y : Nat) (t s : Real)
    (g : Problem520.HarperPrimeCube y -> Real) :
    harperTwoHeightNormalizer y t s *
        (∫ eta, g eta ∂harperTwoHeightCubeLaw y t s) =
      ∫ eta,
        (Problem520.harperCubeDensity y t eta *
          Problem520.harperCubeDensity y s eta) * g eta
        ∂Measure.pi (fun _ : Problem520.HarperPrimeIndex y =>
          Problem520.coin) := by
  rw [integral_fintype (Integrable.of_finite :
      Integrable g (harperTwoHeightCubeLaw y t s)),
    integral_fintype (Integrable.of_finite :
      Integrable (fun eta =>
        (Problem520.harperCubeDensity y t eta *
          Problem520.harperCubeDensity y s eta) * g eta)
        (Measure.pi (fun _ : Problem520.HarperPrimeIndex y =>
          Problem520.coin))),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _heta
  calc
    harperTwoHeightNormalizer y t s *
        ((harperTwoHeightCubeLaw y t s).real {eta} • g eta) =
      (harperTwoHeightNormalizer y t s *
          (harperTwoHeightCubeLaw y t s).real {eta}) * g eta := by
            simp only [smul_eq_mul]
            ring
    _ = (Problem520.harperCubeDensity y t eta *
          Problem520.harperCubeDensity y s eta *
          (Measure.pi (fun _ : Problem520.HarperPrimeIndex y =>
            Problem520.coin)).real {eta}) * g eta := by
            rw [harperTwoHeightNormalizer_mul_cubeLaw_singleton]
    _ = (Measure.pi (fun _ : Problem520.HarperPrimeIndex y =>
          Problem520.coin)).real {eta} •
        ((Problem520.harperCubeDensity y t eta *
          Problem520.harperCubeDensity y s eta) * g eta) := by
            simp only [smul_eq_mul]
            ring

/-- Exact sharp cancellation against a one-height law, point by point.  The
normalized correlation times the two-height point mass is the one-height
point mass weighted by the other normalized Euler density. -/
theorem harperTwoHeightCorrelation_mul_cubeLaw_singleton
    (y : Nat) (t s : Real) (eta : Problem520.HarperPrimeCube y) :
    harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real {eta} =
      Problem520.normalizedHarperCubeDensity y s eta *
        (Problem520.harperTiltedCubeLaw y t).real {eta} := by
  let E : Real := Problem520.primeEnergyNormalizer y
  have hE : E ≠ 0 := Problem520.primeEnergyNormalizer_pos y |>.ne'
  apply mul_left_cancel₀ (pow_ne_zero 2 hE)
  calc
    E ^ (2 : Nat) *
        (harperTwoHeightCorrelation y t s *
          (harperTwoHeightCubeLaw y t s).real {eta}) =
      harperTwoHeightNormalizer y t s *
        (harperTwoHeightCubeLaw y t s).real {eta} := by
          rw [harperTwoHeightNormalizer_eq_energy_sq_mul_correlation]
          dsimp only [E]
          ring
    _ = Problem520.harperCubeDensity y t eta *
          Problem520.harperCubeDensity y s eta *
          (Measure.pi (fun _ : Problem520.HarperPrimeIndex y =>
            Problem520.coin)).real {eta} := by
          rw [harperTwoHeightNormalizer_mul_cubeLaw_singleton]
    _ = E ^ (2 : Nat) *
        (Problem520.normalizedHarperCubeDensity y s eta *
          (Problem520.harperTiltedCubeLaw y t).real {eta}) := by
          rw [Problem520.harperTiltedCubeLaw_real_singleton_eq]
          unfold Problem520.normalizedHarperCubeDensity
          change
            Problem520.harperCubeDensity y t eta *
                  Problem520.harperCubeDensity y s eta *
                  (Measure.pi (fun _ : Problem520.HarperPrimeIndex y =>
                    Problem520.coin)).real {eta} =
              E ^ (2 : Nat) *
                (Problem520.harperCubeDensity y s eta / E *
                  (Problem520.harperCubeDensity y t eta / E *
                    (Measure.pi (fun _ : Problem520.HarperPrimeIndex y =>
                      Problem520.coin)).real {eta}))
          field_simp [hE]

/-- Integral form of the sharp one-height/two-height cancellation. -/
theorem harperTwoHeightCorrelation_mul_integral_cubeLaw_eq_oneHeight
    (y : Nat) (t s : Real)
    (g : Problem520.HarperPrimeCube y -> Real) :
    harperTwoHeightCorrelation y t s *
        (∫ eta, g eta ∂harperTwoHeightCubeLaw y t s) =
      ∫ eta,
        Problem520.normalizedHarperCubeDensity y s eta * g eta
        ∂Problem520.harperTiltedCubeLaw y t := by
  rw [integral_fintype (Integrable.of_finite :
      Integrable g (harperTwoHeightCubeLaw y t s)),
    integral_fintype (Integrable.of_finite :
      Integrable (fun eta =>
        Problem520.normalizedHarperCubeDensity y s eta * g eta)
        (Problem520.harperTiltedCubeLaw y t)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta heta
  simp only [smul_eq_mul]
  calc
    harperTwoHeightCorrelation y t s *
        ((harperTwoHeightCubeLaw y t s).real {eta} * g eta) =
      (harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real {eta}) * g eta := by ring
    _ = (Problem520.normalizedHarperCubeDensity y s eta *
          (Problem520.harperTiltedCubeLaw y t).real {eta}) * g eta := by
      rw [harperTwoHeightCorrelation_mul_cubeLaw_singleton]
    _ = (Problem520.harperTiltedCubeLaw y t).real {eta} *
        (Problem520.normalizedHarperCubeDensity y s eta * g eta) := by ring

/-- Event form: correlation times a two-height probability is exactly a
restricted one-height expectation, with no loss in the critical exponent. -/
theorem harperTwoHeightCorrelation_mul_probability_eq_oneHeight_restrict
    (y : Nat) (t s : Real)
    (A : Set (Problem520.HarperPrimeCube y)) :
    harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real A =
      ∫ eta in A,
        Problem520.normalizedHarperCubeDensity y s eta
        ∂Problem520.harperTiltedCubeLaw y t := by
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  rw [← integral_indicator_one (μ := harperTwoHeightCubeLaw y t s) hA,
    harperTwoHeightCorrelation_mul_integral_cubeLaw_eq_oneHeight]
  rw [← integral_indicator hA]
  apply integral_congr_ae
  exact ae_of_all _ fun eta => by
    by_cases heta : eta ∈ A
    · simp [Set.indicator_of_mem heta]
    · simp [Set.indicator_of_notMem heta]

/-! ## Localizing the exact cancellation to the ballot primes -/

/-- The normalized one-height Euler density restricted to a chosen set of
prime coordinates. -/
noncomputable def harperSubsetNormalizedDensity
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (s : Real) (eta : Problem520.HarperPrimeCube y) : Real :=
  ∏ p ∈ S,
    Problem520.harperCoordinateFactor p.1 s (eta p) /
      (1 + (p.1 : Real)⁻¹)

/-- The two-height correlation contributed by a chosen set of prime
coordinates. -/
noncomputable def harperSubsetCorrelation
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) : Real :=
  ∏ p ∈ S, harperTwoHeightPrimeCorrelation p.1 t s

/-- The ordinary one-height normalizer restricted to a chosen prime set. -/
noncomputable def harperSubsetOneHeightNormalizer
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y)) : Real :=
  ∏ p ∈ S, (1 + (p.1 : Real)⁻¹)

theorem harperSubsetOneHeightNormalizer_pos
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y)) :
    0 < harperSubsetOneHeightNormalizer y S := by
  unfold harperSubsetOneHeightNormalizer
  exact Finset.prod_pos fun p _hp => by positivity

/-- Ratio form of the likelihood on a prime subset. -/
theorem harperSubsetNormalizedDensity_eq_energy_div
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (s : Real) (eta : Problem520.HarperPrimeCube y) :
    harperSubsetNormalizedDensity y S s eta =
      (∏ p ∈ S, Problem520.harperCoordinateFactor p.1 s (eta p)) /
        harperSubsetOneHeightNormalizer y S := by
  unfold harperSubsetNormalizedDensity harperSubsetOneHeightNormalizer
  rw [Finset.prod_div_distrib]

theorem harperSubsetNormalizedDensity_pos
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (s : Real) (eta : Problem520.HarperPrimeCube y) :
    0 < harperSubsetNormalizedDensity y S s eta := by
  unfold harperSubsetNormalizedDensity
  apply Finset.prod_pos
  intro p hp
  exact div_pos
    (Problem520.harperCoordinateFactor_pos
      (Nat.prime_of_mem_primesBelow p.property) s (eta p))
    (by positivity)

/-- Exact logarithm of a restricted normalized density. -/
theorem log_harperSubsetNormalizedDensity
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (s : Real) (eta : Problem520.HarperPrimeCube y) :
    Real.log (harperSubsetNormalizedDensity y S s eta) =
      2 * Problem520.harperLogBlockSum y S s eta -
        Real.log (harperSubsetOneHeightNormalizer y S) := by
  rw [harperSubsetNormalizedDensity_eq_energy_div, Real.log_div,
    Problem520.log_harperEulerBlockEnergy_eq_two_mul_logBlockSum]
  · apply (Finset.prod_pos fun p _hp =>
      Problem520.harperCoordinateFactor_pos
        (Nat.prime_of_mem_primesBelow p.property) s (eta p)).ne'
  · exact (harperSubsetOneHeightNormalizer_pos y S).ne'

private theorem sub_sq_le_log_one_add
    {x : Real} (hx : 0 <= x) :
    x - x ^ (2 : Nat) <= Real.log (1 + x) := by
  have hden : 0 < x + 2 := by linarith
  have hrat : x - x ^ (2 : Nat) <= 2 * x / (x + 2) := by
    apply (le_div_iff₀ hden).2
    nlinarith [mul_nonneg hx hx]
  exact hrat.trans (Real.le_log_one_add_of_nonneg hx)

/-- A sharp elementary lower bound for every restricted one-height
normalizer.  The entire loss from replacing `log(1+1/p)` by `1/p` is the
summable inverse-square mass. -/
theorem sum_inv_sub_sq_le_log_harperSubsetOneHeightNormalizer
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y)) :
    (∑ p ∈ S,
        let x : Real := (p.1 : Real)⁻¹
        x - x ^ (2 : Nat)) <=
      Real.log (harperSubsetOneHeightNormalizer y S) := by
  unfold harperSubsetOneHeightNormalizer
  rw [Real.log_prod]
  · apply Finset.sum_le_sum
    intro p hp
    exact sub_sq_le_log_one_add
      (show 0 <= (p.1 : Real)⁻¹ by positivity)
  · intro p hp
    positivity

/-- The full normalized density is the product of its contributions on a
set of coordinates and on the complementary coordinates. -/
theorem normalizedHarperCubeDensity_eq_subset_mul_compl
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (s : Real) (eta : Problem520.HarperPrimeCube y) :
    Problem520.normalizedHarperCubeDensity y s eta =
      harperSubsetNormalizedDensity y S s eta *
        harperSubsetNormalizedDensity y Sᶜ s eta := by
  unfold Problem520.normalizedHarperCubeDensity
    Problem520.harperCubeDensity harperSubsetNormalizedDensity
  rw [← Problem520.prod_harperCoordinateNormalizer]
  rw [← Finset.prod_div_distrib]
  exact (Finset.prod_mul_prod_compl S
    (fun p : Problem520.HarperPrimeIndex y =>
      Problem520.harperCoordinateFactor p.1 s (eta p) /
        (1 + (p.1 : Real)⁻¹))).symm

/-- Under the one-height tilt at `t`, the mean of one normalized Euler
factor at `s` is exactly the corresponding two-height correlation factor. -/
theorem integral_normalizedCoordinateFactor_harperTiltedCoin
    (p : Nat) (t s : Real) :
    (∫ b,
        Problem520.harperCoordinateFactor p s b /
          (1 + (p : Real)⁻¹)
        ∂Problem520.harperTiltedCoin p t) =
      harperTwoHeightPrimeCorrelation p t s := by
  rw [Problem520.integral_harperTiltedCoin]
  unfold Problem520.harperTiltedCoinWeight
    harperTwoHeightPrimeCorrelation
  rw [harperTwoHeightPrimeNormalizer_eq]
  have hA : 1 + (p : Real)⁻¹ ≠ 0 := by positivity
  field_simp [hA]

/-- The mean of a restricted normalized density is precisely its restricted
two-height correlation. -/
theorem integral_harperSubsetNormalizedDensity
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    (∫ eta, harperSubsetNormalizedDensity y S s eta
        ∂Problem520.harperTiltedCubeLaw y t) =
      harperSubsetCorrelation y S t s := by
  let g : Problem520.HarperPrimeIndex y -> Bool -> Real := fun p b =>
    if p ∈ S then
      Problem520.harperCoordinateFactor p.1 s b /
        (1 + (p.1 : Real)⁻¹)
    else 1
  have hfactor := Problem520.integral_prod_harperTiltedCubeLaw y t g
  have hleft :
      (fun eta => ∏ p : Problem520.HarperPrimeIndex y, g p (eta p)) =
        harperSubsetNormalizedDensity y S s := by
    funext eta
    simp only [g, Finset.prod_ite_mem, Finset.univ_inter]
    rfl
  have hright :
      (∏ p : Problem520.HarperPrimeIndex y,
          ∫ b, g p b ∂Problem520.harperTiltedCoin p.1 t) =
        harperSubsetCorrelation y S t s := by
    unfold harperSubsetCorrelation
    calc
      (∏ p : Problem520.HarperPrimeIndex y,
          ∫ b, g p b ∂Problem520.harperTiltedCoin p.1 t) =
          ∏ p : Problem520.HarperPrimeIndex y,
            if p ∈ S then harperTwoHeightPrimeCorrelation p.1 t s
            else 1 := by
              apply Finset.prod_congr rfl
              intro p _hp
              by_cases hpS : p ∈ S
              · simp only [g, if_pos hpS]
                exact integral_normalizedCoordinateFactor_harperTiltedCoin
                  p.1 t s
              · simp only [g, if_neg hpS, integral_const,
                  probReal_univ, one_smul]
      _ = ∏ p ∈ S, harperTwoHeightPrimeCorrelation p.1 t s :=
        Fintype.prod_ite_mem S _
  rw [hleft, hright] at hfactor
  exact hfactor

/-- A finite-cube event depends only on the coordinates in `S`. -/
def HarperEventDependsOn
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (A : Set (Problem520.HarperPrimeCube y)) : Prop :=
  ∀ eta xi, (∀ p, p ∈ S -> eta p = xi p) ->
    (eta ∈ A ↔ xi ∈ A)

/-- The scheduled centered path only uses the primes in its consecutive
scheduled range. -/
theorem harperScheduledCenteredBlockVectorVarying_eq_of_eqOn_rangeFrom
    (y start n : Nat) (t : Real) (u : Fin n -> Real)
    (eta xi : Problem520.HarperPrimeCube y)
    (heq : ∀ p,
      p ∈ Problem520.harperScheduledPrimeRangeFrom y start n ->
        eta p = xi p) :
    Problem520.harperScheduledCenteredBlockVectorVarying
        y start n t u eta =
      Problem520.harperScheduledCenteredBlockVectorVarying
        y start n t u xi := by
  funext i
  unfold Problem520.harperScheduledCenteredBlockVectorVarying
    Problem520.harperCenteredLinearPrimeBlockSum
  apply Finset.sum_congr rfl
  intro p hp
  have hpRange :
      p ∈ Problem520.harperScheduledPrimeRangeFrom y start n := by
    unfold Problem520.harperScheduledPrimeRangeFrom
    rw [Finset.mem_biUnion]
    exact ⟨i.1, Finset.mem_range.mpr i.2, by simpa using hp⟩
  rw [heq p hpRange]

/-- The literal central lower-ballot event depends only on the scheduled
prime range which generates its path. -/
theorem harperCentralLowerBallotCubeEvent_dependsOn_rangeFrom
    (y start n : Nat) (t : Real) :
    HarperEventDependsOn y
      (Problem520.harperScheduledPrimeRangeFrom y start n)
      (harperCentralLowerBallotCubeEvent y start n t) := by
  intro eta xi heq
  unfold harperCentralLowerBallotCubeEvent
  change
    Problem520.harperScheduledCenteredBlockVectorVarying
          y start n t (fun _i : Fin n => t) eta ∈
        Problem520.harperPartialSumBarrierSet
          (harperScheduledAutomaticLowerBarrier start n)
          (harperScheduledAutomaticUpperBarrier start n) ↔
      Problem520.harperScheduledCenteredBlockVectorVarying
          y start n t (fun _i : Fin n => t) xi ∈
        Problem520.harperPartialSumBarrierSet
          (harperScheduledAutomaticLowerBarrier start n)
          (harperScheduledAutomaticUpperBarrier start n)
  rw [harperScheduledCenteredBlockVectorVarying_eq_of_eqOn_rangeFrom
    y start n t (fun _i : Fin n => t) eta xi heq]

/-- Every prefix selected by the central ballot has centered sum at most
`3`.  This is the flat upper barrier `1` plus the repository's total mesh
width bound `2`. -/
theorem harperCenteredRangeFrom_le_three_of_mem_centralLowerBallot
    (y start n : Nat) (t : Real)
    (eta : Problem520.HarperPrimeCube y)
    (heta : eta ∈ harperCentralLowerBallotCubeEvent y start n t)
    (k : Fin n) :
    Problem520.harperCenteredLinearPrimeBlockSum y
        (Problem520.harperScheduledPrimeRangeFrom y start (k.val + 1))
        t t eta <= 3 := by
  let v := Problem520.harperScheduledCenteredBlockVectorVarying
    y start n t (fun _i : Fin n => t) eta
  have hpath : Problem520.harperPathPartialSum v k <=
      harperScheduledAutomaticUpperBarrier start n k := by
    change v ∈ Problem520.harperPartialSumBarrierSet
        (harperScheduledAutomaticLowerBarrier start n)
        (harperScheduledAutomaticUpperBarrier start n) at heta
    exact (Problem520.mem_harperPartialSumBarrierSet.mp heta k).2
  have hprefix :
      Problem520.harperCenteredLinearPrimeBlockSum y
          (Problem520.harperScheduledPrimeRangeFrom y start (k.val + 1))
          t t eta = Problem520.harperPathPartialSum v k := by
    calc
      Problem520.harperCenteredLinearPrimeBlockSum y
          (Problem520.harperScheduledPrimeRangeFrom y start (k.val + 1))
          t t eta =
        ∑ i ∈ Finset.range (k.val + 1),
          Problem520.harperCenteredLinearPrimeBlockSum y
            (Problem520.harperScheduledPrimeBlock y (start + i))
            t t eta := by
              symm
              exact Problem520.sum_harperCenteredLinearPrimeBlockSum_eq_rangeFrom
                y start (k.val + 1) t t eta
      _ = ∑ i : Fin (k.val + 1),
          Problem520.harperCenteredLinearPrimeBlockSum y
            (Problem520.harperScheduledPrimeBlock y (start + i.val))
            t t eta := by
              exact (Fin.sum_univ_eq_sum_range
                (fun i : Nat =>
                  Problem520.harperCenteredLinearPrimeBlockSum y
                    (Problem520.harperScheduledPrimeBlock y (start + i))
                    t t eta) (k.val + 1)).symm
      _ = ∑ i : Fin (k.val + 1),
          Problem520.harperPathPrefix (show k.val + 1 <= n by omega) v i := by
            rfl
      _ = Problem520.harperPathPartialSum v k :=
        (Problem520.harperPathPartialSum_eq_sum_prefix v k).symm
  have hwidth :=
    Problem520.harperCumulativeScheduledRelativeCellWidth_le_two start n k
  calc
    Problem520.harperCenteredLinearPrimeBlockSum y
        (Problem520.harperScheduledPrimeRangeFrom y start (k.val + 1))
        t t eta = Problem520.harperPathPartialSum v k := hprefix
    _ <= harperScheduledAutomaticUpperBarrier start n k := hpath
    _ <= 3 := by
      unfold harperScheduledAutomaticUpperBarrier
      linarith

/-- Deterministic likelihood cap on every ballot prefix.  This is the sharp
bridge from the additive upper barrier to the multiplicative Euler density:
the only remaining deterministic terms are the exact diagonal main mean,
the summable Taylor remainder, and the exact prefix normalizer. -/
theorem harperSubsetNormalizedDensity_prefix_le_exp_of_mem_centralLowerBallot
    (y start n : Nat) (t : Real)
    (eta : Problem520.HarperPrimeCube y)
    (heta : eta ∈ harperCentralLowerBallotCubeEvent y start n t)
    (k : Fin n) :
    let S := Problem520.harperScheduledPrimeRangeFrom
      y start (k.val + 1)
    let R := (4 / 3 : Real) *
      (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
    harperSubsetNormalizedDensity y S t eta <=
      Real.exp
        (2 * (3 +
          Problem520.harperLogMainBlockMean y S t t + R) -
          Real.log (harperSubsetOneHeightNormalizer y S)) := by
  dsimp only
  let S := Problem520.harperScheduledPrimeRangeFrom
    y start (k.val + 1)
  let R := (4 / 3 : Real) *
    (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
  have hpos : 0 < harperSubsetNormalizedDensity y S t eta :=
    harperSubsetNormalizedDensity_pos y S t eta
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  rw [log_harperSubsetNormalizedDensity]
  have hTaylor :=
    Problem520.abs_harperLogRangeFrom_sub_centered_add_mean_le
      y start (k.val + 1) t t eta
  have hTaylorUpper := le_of_abs_le hTaylor
  have hcenter :=
    harperCenteredRangeFrom_le_three_of_mem_centralLowerBallot
      y start n t eta heta k
  change
    2 * Problem520.harperLogBlockSum y S t eta -
          Real.log (harperSubsetOneHeightNormalizer y S) <=
      2 * (3 + Problem520.harperLogMainBlockMean y S t t + R) -
        Real.log (harperSubsetOneHeightNormalizer y S)
  change
    Problem520.harperLogBlockSum y S t eta -
        (Problem520.harperCenteredLinearPrimeBlockSum y S t t eta +
          Problem520.harperLogMainBlockMean y S t t) <= R at hTaylorUpper
  change Problem520.harperCenteredLinearPrimeBlockSum y S t t eta <= 3
    at hcenter
  nlinarith

/-- Normalizer-free version of the prefix likelihood cap.  The exponent now
displays exactly the nonsummable reciprocal-prime term and the summable
inverse-square correction which must be paired with the separation strip. -/
theorem harperSubsetNormalizedDensity_prefix_le_exp_reciprocalBudget
    (y start n : Nat) (t : Real)
    (eta : Problem520.HarperPrimeCube y)
    (heta : eta ∈ harperCentralLowerBallotCubeEvent y start n t)
    (k : Fin n) :
    let S := Problem520.harperScheduledPrimeRangeFrom
      y start (k.val + 1)
    let R := (4 / 3 : Real) *
      (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
    let Q := ∑ p ∈ S,
      let x : Real := (p.1 : Real)⁻¹
      x - x ^ (2 : Nat)
    harperSubsetNormalizedDensity y S t eta <=
      Real.exp
        (2 * (3 +
          Problem520.harperLogMainBlockMean y S t t + R) - Q) := by
  dsimp only
  let S := Problem520.harperScheduledPrimeRangeFrom
    y start (k.val + 1)
  let R := (4 / 3 : Real) *
    (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
  let Q := ∑ p ∈ S,
    let x : Real := (p.1 : Real)⁻¹
    x - x ^ (2 : Nat)
  have hcap :=
    harperSubsetNormalizedDensity_prefix_le_exp_of_mem_centralLowerBallot
      y start n t eta heta k
  have hnormalizer : Q <=
      Real.log (harperSubsetOneHeightNormalizer y S) := by
    exact sum_inv_sub_sq_le_log_harperSubsetOneHeightNormalizer y S
  dsimp only at hcap
  apply hcap.trans
  apply Real.exp_le_exp.mpr
  change
    2 * (3 + Problem520.harperLogMainBlockMean y S t t + R) -
          Real.log (harperSubsetOneHeightNormalizer y S) <=
      2 * (3 + Problem520.harperLogMainBlockMean y S t t + R) - Q
  linarith

/-- Split a restricted likelihood into a prefix and the remaining
coordinates. -/
theorem harperSubsetNormalizedDensity_eq_subset_mul_sdiff
    (y : Nat) {P S : Finset (Problem520.HarperPrimeIndex y)}
    (hPS : P ⊆ S) (s : Real) (eta : Problem520.HarperPrimeCube y) :
    harperSubsetNormalizedDensity y S s eta =
      harperSubsetNormalizedDensity y P s eta *
        harperSubsetNormalizedDensity y (S \ P) s eta := by
  unfold harperSubsetNormalizedDensity
  have hprod := Finset.prod_sdiff
    (f := fun p : Problem520.HarperPrimeIndex y =>
      Problem520.harperCoordinateFactor p.1 s (eta p) /
        (1 + (p.1 : Real)⁻¹)) hPS
  nlinarith

theorem harperSubsetCorrelation_pos
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    0 < harperSubsetCorrelation y S t s := by
  unfold harperSubsetCorrelation
  exact Finset.prod_pos fun p _hp =>
    harperTwoHeightPrimeCorrelation_pos
      (Nat.prime_of_mem_primesBelow p.property) t s

/-- Complement arithmetic for restricted correlations: removing a prefix
from the active set and multiplying by the old complement is exactly the
correlation of the prefix complement. -/
theorem harperSubsetCorrelation_compl_mul_sdiff
    (y : Nat) {P S : Finset (Problem520.HarperPrimeIndex y)}
    (hPS : P ⊆ S) (t s : Real) :
    harperSubsetCorrelation y Sᶜ t s *
        harperSubsetCorrelation y (S \ P) t s =
      harperSubsetCorrelation y Pᶜ t s := by
  unfold harperSubsetCorrelation
  have hdis : Disjoint Sᶜ (S \ P) := by
    rw [Finset.disjoint_left]
    intro p hpCompl hpDiff
    have hpNotS : p ∉ S := by simpa using hpCompl
    exact hpNotS (Finset.mem_sdiff.mp hpDiff).1
  have hset : Sᶜ ∪ (S \ P) = Pᶜ := by
    ext p
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_sdiff]
    constructor
    · intro hp
      rcases hp with hp | hp
      · exact fun hpP => hp (hPS hpP)
      · exact hp.2
    · intro hpP
      by_cases hpS : p ∈ S
      · exact Or.inr ⟨hpS, hpP⟩
      · exact Or.inl hpS
  rw [← Finset.prod_union hdis, hset]

/-- If an event caps the likelihood on a prefix `P`, the rest of the
likelihood can be averaged exactly.  This removes the event and replaces the
remaining coordinates by their exact correlation. -/
theorem integral_harperSubsetNormalizedDensity_restrict_le_of_prefixCap
    (y : Nat) {P S : Finset (Problem520.HarperPrimeIndex y)}
    (hPS : P ⊆ S) (t s M : Real)
    (A : Set (Problem520.HarperPrimeCube y)) (hM : 0 <= M)
    (hcap : ∀ eta ∈ A,
      harperSubsetNormalizedDensity y P s eta <= M) :
    (∫ eta in A, harperSubsetNormalizedDensity y S s eta
        ∂Problem520.harperTiltedCubeLaw y t) <=
      M * harperSubsetCorrelation y (S \ P) t s := by
  have hAmeas : MeasurableSet A := (Set.toFinite A).measurableSet
  rw [← integral_indicator hAmeas]
  calc
    (∫ eta,
        A.indicator (harperSubsetNormalizedDensity y S s) eta
        ∂Problem520.harperTiltedCubeLaw y t) <=
      ∫ eta,
        M * harperSubsetNormalizedDensity y (S \ P) s eta
        ∂Problem520.harperTiltedCubeLaw y t := by
          apply integral_mono Integrable.of_finite Integrable.of_finite
          intro eta
          by_cases heta : eta ∈ A
          · rw [Set.indicator_of_mem heta,
              harperSubsetNormalizedDensity_eq_subset_mul_sdiff y hPS]
            exact mul_le_mul_of_nonneg_right (hcap eta heta)
              (harperSubsetNormalizedDensity_pos y (S \ P) s eta).le
          · rw [Set.indicator_of_notMem heta]
            exact mul_nonneg hM
              (harperSubsetNormalizedDensity_pos y (S \ P) s eta).le
    _ = M * harperSubsetCorrelation y (S \ P) t s := by
      rw [integral_const_mul,
        integral_harperSubsetNormalizedDensity]

/-- An intersection of two events depending on the same coordinate set
still depends only on that set. -/
theorem HarperEventDependsOn.inter
    {y : Nat} {S : Finset (Problem520.HarperPrimeIndex y)}
    {A B : Set (Problem520.HarperPrimeCube y)}
    (hA : HarperEventDependsOn y S A)
    (hB : HarperEventDependsOn y S B) :
    HarperEventDependsOn y S (A ∩ B) := by
  intro eta xi heq
  simp only [Set.mem_inter_iff, hA eta xi heq, hB eta xi heq]

/-- Exact localization of the sharp cancellation.  If an event only sees
the coordinates in `S`, all complementary coordinates integrate out as
their exact complementary correlation. -/
theorem harperTwoHeightCorrelation_mul_probability_eq_localized
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) (A : Set (Problem520.HarperPrimeCube y))
    (hA : HarperEventDependsOn y S A) :
    harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real A =
      harperSubsetCorrelation y Sᶜ t s *
        (∫ eta in A, harperSubsetNormalizedDensity y S s eta
          ∂Problem520.harperTiltedCubeLaw y t) := by
  let mu := Problem520.harperTiltedCubeLaw y t
  let active : Problem520.HarperPrimeCube y -> Real :=
    harperSubsetNormalizedDensity y S s
  let outside : Problem520.HarperPrimeCube y -> Real :=
    harperSubsetNormalizedDensity y Sᶜ s
  let restrictS : Problem520.HarperPrimeCube y -> (S -> Bool) :=
    fun eta p => eta p.1
  let restrictOutside :
      Problem520.HarperPrimeCube y -> (↥(Sᶜ) -> Bool) :=
    fun eta p => eta p.1
  let fillS : (S -> Bool) -> Problem520.HarperPrimeCube y :=
    fun z p => if hp : p ∈ S then z ⟨p, hp⟩ else false
  let fillOutside : (↥(Sᶜ) -> Bool) -> Problem520.HarperPrimeCube y :=
    fun z p => if hp : p ∈ Sᶜ then z ⟨p, hp⟩ else false
  let F : Problem520.HarperPrimeCube y -> Real :=
    A.indicator active
  let G : Problem520.HarperPrimeCube y -> Real := outside
  let f : (S -> Bool) -> Real := fun z => F (fillS z)
  let g : (↥(Sᶜ) -> Bool) -> Real := fun z => G (fillOutside z)
  have hactive (eta : Problem520.HarperPrimeCube y) :
      active eta = active (fillS (restrictS eta)) := by
    unfold active harperSubsetNormalizedDensity
    apply Finset.prod_congr rfl
    intro p hp
    simp only [fillS, restrictS, hp, dite_true]
  have houtside (eta : Problem520.HarperPrimeCube y) :
      outside eta = outside (fillOutside (restrictOutside eta)) := by
    unfold outside harperSubsetNormalizedDensity
    apply Finset.prod_congr rfl
    intro p hp
    simp only [fillOutside, restrictOutside, hp, dite_true]
  have hF : F = f ∘ restrictS := by
    funext eta
    have hmem : eta ∈ A ↔ fillS (restrictS eta) ∈ A := by
      apply hA
      intro p hp
      simp only [fillS, restrictS, hp, dite_true]
    by_cases heta : eta ∈ A
    · have hfill : fillS (restrictS eta) ∈ A := hmem.mp heta
      simp only [F, f, Function.comp_apply, Set.indicator_of_mem heta,
        Set.indicator_of_mem hfill]
      exact hactive eta
    · have hfill : fillS (restrictS eta) ∉ A := by
        exact fun h => heta (hmem.mpr h)
      simp only [F, f, Function.comp_apply, Set.indicator_of_notMem heta,
        Set.indicator_of_notMem hfill]
  have hG : G = g ∘ restrictOutside := by
    funext eta
    change outside eta = outside (fillOutside (restrictOutside eta))
    exact houtside eta
  have hrestrict : restrictS ⟂ᵢ[mu] restrictOutside := by
    exact (Problem520.iIndepFun_harperTiltedCube_coordinates y t).indepFun_finset
      S Sᶜ (disjoint_compl_right : Disjoint S Sᶜ)
        (fun _p => measurable_of_finite _)
  have hFG : F ⟂ᵢ[mu] G := by
    rw [hF, hG]
    exact hrestrict.comp (measurable_of_finite f) (measurable_of_finite g)
  have hfactor :
      (∫ eta, F eta * G eta ∂mu) =
        (∫ eta, F eta ∂mu) * ∫ eta, G eta ∂mu :=
    hFG.integral_fun_mul_eq_mul_integral
      (measurable_of_finite F).aestronglyMeasurable
      (measurable_of_finite G).aestronglyMeasurable
  have hAmeas : MeasurableSet A := (Set.toFinite A).measurableSet
  rw [harperTwoHeightCorrelation_mul_probability_eq_oneHeight_restrict]
  calc
    (∫ eta in A, Problem520.normalizedHarperCubeDensity y s eta
        ∂Problem520.harperTiltedCubeLaw y t) =
        ∫ eta, F eta * G eta ∂mu := by
          rw [← integral_indicator hAmeas]
          apply integral_congr_ae
          exact ae_of_all _ fun eta => by
            by_cases heta : eta ∈ A
            · rw [Set.indicator_of_mem heta,
                normalizedHarperCubeDensity_eq_subset_mul_compl y S s eta]
              simp [F, G, active, outside, heta]
            · simp [F, G, active, outside, heta]
    _ = (∫ eta, F eta ∂mu) * ∫ eta, G eta ∂mu := hfactor
    _ = (∫ eta in A, harperSubsetNormalizedDensity y S s eta
          ∂Problem520.harperTiltedCubeLaw y t) *
        harperSubsetCorrelation y Sᶜ t s := by
          rw [show (∫ eta, F eta ∂mu) =
              ∫ eta in A, harperSubsetNormalizedDensity y S s eta
                ∂Problem520.harperTiltedCubeLaw y t by
            rw [← integral_indicator hAmeas],
            show (∫ eta, G eta ∂mu) =
                harperSubsetCorrelation y Sᶜ t s by
              exact integral_harperSubsetNormalizedDensity y Sᶜ t s]
    _ = harperSubsetCorrelation y Sᶜ t s *
        (∫ eta in A, harperSubsetNormalizedDensity y S s eta
          ∂Problem520.harperTiltedCubeLaw y t) := by ring

/-- Prefix-cancellation inequality.  Once an event depending on `S` caps
the likelihood on `P ⊆ S`, every other likelihood coordinate averages out
exactly, leaving only the correlation of `Pᶜ`. -/
theorem harperTwoHeightCorrelation_mul_probability_le_of_prefixCap
    (y : Nat) {P S : Finset (Problem520.HarperPrimeIndex y)}
    (hPS : P ⊆ S) (t s M : Real)
    (A : Set (Problem520.HarperPrimeCube y))
    (hA : HarperEventDependsOn y S A) (hM : 0 <= M)
    (hcap : ∀ eta ∈ A,
      harperSubsetNormalizedDensity y P s eta <= M) :
    harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real A <=
      M * harperSubsetCorrelation y Pᶜ t s := by
  rw [harperTwoHeightCorrelation_mul_probability_eq_localized
    y S t s A hA]
  have hrestricted :=
    integral_harperSubsetNormalizedDensity_restrict_le_of_prefixCap
      y hPS t s M A hM hcap
  calc
    harperSubsetCorrelation y Sᶜ t s *
        (∫ eta in A, harperSubsetNormalizedDensity y S s eta
          ∂Problem520.harperTiltedCubeLaw y t) <=
      harperSubsetCorrelation y Sᶜ t s *
        (M * harperSubsetCorrelation y (S \ P) t s) :=
          mul_le_mul_of_nonneg_left hrestricted
            (harperSubsetCorrelation_pos y Sᶜ t s).le
    _ = M * (harperSubsetCorrelation y Sᶜ t s *
        harperSubsetCorrelation y (S \ P) t s) := by ring
    _ = M * harperSubsetCorrelation y Pᶜ t s := by
      rw [harperSubsetCorrelation_compl_mul_sdiff y hPS]

/-- Specialization of exact localization to the simultaneous central ballot
event.  The only random likelihood left inside the restricted expectation is
the likelihood on the scheduled ballot primes themselves. -/
theorem harperCentralLowerBallot_correlation_probability_eq_localized
    (y start n : Nat) (t s : Real) :
    let S := Problem520.harperScheduledPrimeRangeFrom y start n
    let A : Real -> Set (Problem520.HarperPrimeCube y) := fun u =>
      harperCentralLowerBallotCubeEvent y start n u
    harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real (A t ∩ A s) =
      harperSubsetCorrelation y Sᶜ t s *
        (∫ eta in A t ∩ A s,
          harperSubsetNormalizedDensity y S s eta
          ∂Problem520.harperTiltedCubeLaw y t) := by
  dsimp only
  apply harperTwoHeightCorrelation_mul_probability_eq_localized
  exact (harperCentralLowerBallotCubeEvent_dependsOn_rangeFrom
      y start n t).inter
    (harperCentralLowerBallotCubeEvent_dependsOn_rangeFrom
      y start n s)

/-- The same localization with the full two-height normalizer restored. -/
theorem harperCentralLowerBallot_normalizer_probability_eq_localized
    (y start n : Nat) (t s : Real) :
    let S := Problem520.harperScheduledPrimeRangeFrom y start n
    let A : Real -> Set (Problem520.HarperPrimeCube y) := fun u =>
      harperCentralLowerBallotCubeEvent y start n u
    harperTwoHeightNormalizer y t s *
        (harperTwoHeightCubeLaw y t s).real (A t ∩ A s) =
      Problem520.primeEnergyNormalizer y ^ (2 : Nat) *
        harperSubsetCorrelation y Sᶜ t s *
        (∫ eta in A t ∩ A s,
          harperSubsetNormalizedDensity y S s eta
          ∂Problem520.harperTiltedCubeLaw y t) := by
  dsimp only
  rw [harperTwoHeightNormalizer_eq_energy_sq_mul_correlation]
  rw [show
      Problem520.primeEnergyNormalizer y ^ (2 : Nat) *
            harperTwoHeightCorrelation y t s *
              (harperTwoHeightCubeLaw y t s).real
                (harperCentralLowerBallotCubeEvent y start n t ∩
                  harperCentralLowerBallotCubeEvent y start n s) =
        Problem520.primeEnergyNormalizer y ^ (2 : Nat) *
          (harperTwoHeightCorrelation y t s *
            (harperTwoHeightCubeLaw y t s).real
              (harperCentralLowerBallotCubeEvent y start n t ∩
                harperCentralLowerBallotCubeEvent y start n s)) by ring,
    harperCentralLowerBallot_correlation_probability_eq_localized]
  ring

/-- The concrete prefix-cancellation bound for the simultaneous central
ballot.  At any selected prefix `k`, all randomness and all correlation from
that prefix disappear; what remains is the explicit deterministic likelihood
budget times the correlation of the prefix complement. -/
theorem harperCentralLowerBallot_correlation_probability_le_prefix
    (y start n : Nat) (t s : Real) (k : Fin n) :
    let P := Problem520.harperScheduledPrimeRangeFrom
      y start (k.val + 1)
    let R := (4 / 3 : Real) *
      (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
    let Q := ∑ p ∈ P,
      let x : Real := (p.1 : Real)⁻¹
      x - x ^ (2 : Nat)
    harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real
          (harperCentralLowerBallotCubeEvent y start n t ∩
            harperCentralLowerBallotCubeEvent y start n s) <=
      Real.exp
          (2 * (3 +
            Problem520.harperLogMainBlockMean y P s s + R) - Q) *
        harperSubsetCorrelation y Pᶜ t s := by
  dsimp only
  let P := Problem520.harperScheduledPrimeRangeFrom
    y start (k.val + 1)
  let S := Problem520.harperScheduledPrimeRangeFrom y start n
  let R := (4 / 3 : Real) *
    (Real.sqrt (Problem520.harperBlockEndpoint start : Real))⁻¹
  let Q := ∑ p ∈ P,
    let x : Real := (p.1 : Real)⁻¹
    x - x ^ (2 : Nat)
  let M := Real.exp
    (2 * (3 + Problem520.harperLogMainBlockMean y P s s + R) - Q)
  have hPS : P ⊆ S := by
    intro p hp
    have hp' :=
      (Problem520.mem_harperScheduledPrimeRangeFrom p).mp hp
    apply (Problem520.mem_harperScheduledPrimeRangeFrom p).mpr
    refine ⟨hp'.1, hp'.2.trans ?_⟩
    apply Problem520.monotone_harperBlockEndpoint
    omega
  apply harperTwoHeightCorrelation_mul_probability_le_of_prefixCap
    y hPS t s M
  · exact (harperCentralLowerBallotCubeEvent_dependsOn_rangeFrom
        y start n t).inter
      (harperCentralLowerBallotCubeEvent_dependsOn_rangeFrom
        y start n s)
  · exact Real.exp_pos _ |>.le
  · intro eta heta
    exact harperSubsetNormalizedDensity_prefix_le_exp_reciprocalBudget
      y start n s eta heta.2 k

/-- Event form of the exact two-height change of measure.  The unnormalized
restricted mass is the product normalizer times a genuine probability of the
same event under the two-height tilted cube law. -/
theorem harperTwoHeightCubeMass_eq_normalizer_mul_probability
    (y : Nat) (t s : Real)
    (A : Set (Problem520.HarperPrimeCube y)) :
    harperTwoHeightCubeMass y t s A =
      harperTwoHeightNormalizer y t s *
        (harperTwoHeightCubeLaw y t s).real A := by
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  rw [← integral_indicator_one (μ := harperTwoHeightCubeLaw y t s) hA,
    harperTwoHeightNormalizer_mul_integral_cubeLaw_eq]
  unfold harperTwoHeightCubeMass
  rw [← integral_indicator hA]
  apply integral_congr_ae
  exact ae_of_all _ fun eta => by
    by_cases heta : eta ∈ A
    · simp [Set.indicator_of_mem heta]
    · simp [Set.indicator_of_notMem heta]

theorem harperTwoHeightCubeMass_le_normalizer
    (y : Nat) (t s : Real)
    (A : Set (Problem520.HarperPrimeCube y)) :
    harperTwoHeightCubeMass y t s A <=
      harperTwoHeightNormalizer y t s := by
  rw [harperTwoHeightCubeMass_eq_normalizer_mul_probability]
  nth_rewrite 2 [← mul_one (harperTwoHeightNormalizer y t s)]
  exact mul_le_mul_of_nonneg_left measureReal_le_one
    (harperTwoHeightNormalizer_pos y t s).le

/-! ## The remaining estimate after exact prime-range localization -/

/-- The sharp remaining two-height estimate.  The complementary prime
coordinates have been integrated out exactly; the restricted expectation
contains only the scheduled primes which generate the two ballot paths. -/
def HarperCentralLowerBallotLocalizedStatement : Prop :=
  ∃ C : Real, 0 < C ∧ ∃ Y : Nat, ∀ y : Nat,
    Y <= y -> 4 <= y ->
      let n := harper1144LowerBallotPathLength y
      let S := Problem520.harperScheduledPrimeRangeFrom y n n
      let A : Real -> Set (Problem520.HarperPrimeCube y) := fun t =>
        harperCentralLowerBallotCubeEvent y n n t
      (∫ ts,
          Problem520.primeEnergyNormalizer y ^ (2 : Nat) *
            harperSubsetCorrelation y Sᶜ ts.1 ts.2 *
            (∫ eta in A ts.1 ∩ A ts.2,
              harperSubsetNormalizedDensity y S ts.2 eta
              ∂Problem520.harperTiltedCubeLaw y ts.1)
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand)) <=
        ((C * harperInitialCriticalScale y) *
          Real.log (y : Real)) ^ (2 : Nat)

/-- Equivalent product-law form retained as the direct bridge to the older
two-height restricted-mass certificate. -/
def HarperCentralLowerBallotTwoHeightTiltStatement : Prop :=
  ∃ C : Real, 0 < C ∧ ∃ Y : Nat, ∀ y : Nat,
    Y <= y -> 4 <= y ->
      let n := harper1144LowerBallotPathLength y
      let A : Real -> Set (Problem520.HarperPrimeCube y) := fun t =>
        harperCentralLowerBallotCubeEvent y n n t
      (∫ ts,
          harperTwoHeightNormalizer y ts.1 ts.2 *
            (harperTwoHeightCubeLaw y ts.1 ts.2).real
              (A ts.1 ∩ A ts.2)
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand)) <=
        ((C * harperInitialCriticalScale y) *
          Real.log (y : Real)) ^ (2 : Nat)

/-- Exact prime-range localization turns the sharp localized estimate into
the product-law estimate with no inequality or constant loss. -/
theorem harperCentralLowerBallotTwoHeightTiltStatement_of_localized
    (hlocal : HarperCentralLowerBallotLocalizedStatement) :
    HarperCentralLowerBallotTwoHeightTiltStatement := by
  obtain ⟨C, hC, Y, hlocal⟩ := hlocal
  refine ⟨C, hC, Y, ?_⟩
  intro y hyY hy4
  let n := harper1144LowerBallotPathLength y
  let S := Problem520.harperScheduledPrimeRangeFrom y n n
  let A : Real -> Set (Problem520.HarperPrimeCube y) := fun t =>
    harperCentralLowerBallotCubeEvent y n n t
  have hmain := hlocal y hyY hy4
  dsimp only at hmain ⊢
  calc
    (∫ ts,
        harperTwoHeightNormalizer y ts.1 ts.2 *
          (harperTwoHeightCubeLaw y ts.1 ts.2).real
            (harperCentralLowerBallotCubeEvent y n n ts.1 ∩
              harperCentralLowerBallotCubeEvent y n n ts.2)
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) =
      ∫ ts,
        Problem520.primeEnergyNormalizer y ^ (2 : Nat) *
          harperSubsetCorrelation y
            (Problem520.harperScheduledPrimeRangeFrom y n n)ᶜ
            ts.1 ts.2 *
          (∫ eta in
              harperCentralLowerBallotCubeEvent y n n ts.1 ∩
                harperCentralLowerBallotCubeEvent y n n ts.2,
            harperSubsetNormalizedDensity y
              (Problem520.harperScheduledPrimeRangeFrom y n n) ts.2 eta
            ∂Problem520.harperTiltedCubeLaw y ts.1)
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand) := by
            apply integral_congr_ae
            exact ae_of_all _ fun ts =>
              harperCentralLowerBallot_normalizer_probability_eq_localized
                y n n ts.1 ts.2
    _ <= ((C * harperInitialCriticalScale y) *
          Real.log (y : Real)) ^ (2 : Nat) := hmain

/-- The normalized product-law formulation is exactly the original
two-height restricted-mass certificate. -/
theorem harperCentralLowerBallotTwoHeightStatement_of_tilt
    (htilt : HarperCentralLowerBallotTwoHeightTiltStatement) :
    HarperCentralLowerBallotTwoHeightStatement := by
  obtain ⟨C, hC, Y, htilt⟩ := htilt
  refine ⟨C, hC, Y, ?_⟩
  intro y hyY hy4
  let n := harper1144LowerBallotPathLength y
  let A : Real -> Set (Problem520.HarperPrimeCube y) := fun t =>
    harperCentralLowerBallotCubeEvent y n n t
  have hmain := htilt y hyY hy4
  dsimp only at hmain ⊢
  simpa only [harperTwoHeightCubeMass_eq_normalizer_mul_probability]
    using hmain

/-- End-to-end handoff from the single normalized two-height integral to the
missing lower half moment. -/
theorem harperRademacherInitialHalfMomentLowerStatement_of_twoHeightTilt
    (htilt : HarperCentralLowerBallotTwoHeightTiltStatement) :
    HarperRademacherInitialHalfMomentLowerStatement :=
  harperRademacherInitialHalfMomentLowerStatement_of_centralLowerBallot
    (harperCentralLowerBallotTwoHeightStatement_of_tilt htilt)

/-- End-to-end handoff from the exact prime-range localized estimate to the
missing lower half moment. -/
theorem harperRademacherInitialHalfMomentLowerStatement_of_localized
    (hlocal : HarperCentralLowerBallotLocalizedStatement) :
    HarperRademacherInitialHalfMomentLowerStatement :=
  harperRademacherInitialHalfMomentLowerStatement_of_twoHeightTilt
    (harperCentralLowerBallotTwoHeightTiltStatement_of_localized hlocal)

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.harperTwoHeightCubeMass_eq_normalizer_mul_probability
#print axioms Erdos.Problem1144.harperTwoHeightCorrelation_mul_probability_eq_oneHeight_restrict
#print axioms Erdos.Problem1144.harperTwoHeightCorrelation_mul_probability_eq_localized
#print axioms Erdos.Problem1144.harperCentralLowerBallot_normalizer_probability_eq_localized
#print axioms Erdos.Problem1144.harperTwoHeightCorrelation_le_exp_differenceKernel_add_twelve
#print axioms Erdos.Problem1144.harperTwoHeightCenteredPrimeDrift_eq_product
#print axioms Erdos.Problem1144.integral_harperCenteredLinearPrimeBlockSum_twoHeightCube
#print axioms Erdos.Problem1144.harperTwoHeightCubeLaw_blockSum_le
#print axioms Erdos.Problem1144.sum_inv_sub_sq_le_log_harperSubsetOneHeightNormalizer
#print axioms Erdos.Problem1144.harperSubsetNormalizedDensity_prefix_le_exp_reciprocalBudget
#print axioms Erdos.Problem1144.integral_harperSubsetNormalizedDensity_restrict_le_of_prefixCap
#print axioms Erdos.Problem1144.harperTwoHeightCorrelation_mul_probability_le_of_prefixCap
#print axioms Erdos.Problem1144.harperCentralLowerBallot_correlation_probability_le_prefix
#print axioms Erdos.Problem1144.harperRademacherInitialHalfMomentLowerStatement_of_twoHeightTilt
#print axioms Erdos.Problem1144.harperRademacherInitialHalfMomentLowerStatement_of_localized
