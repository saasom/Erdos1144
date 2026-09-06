import Erdos.Problem1144.HarperRankinTwoHeightRestrictedMass
import Erdos.Problem1144.HarperTwoHeightTilt

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Rankin-shifted two-height correlation

The dangerous two-height normalizer has exactly the same cosine-kernel form
after the Rankin shift, with `1/p` replaced by `p^(-1-a)`.  At
`a = 4V/log y` the replacement costs only a constant depending on `V`.
-/

/-- Fair one-prime normalizer of the product of two shifted Euler factors. -/
noncomputable def harperRankinTwoHeightPrimeNormalizer
    (p : ℕ) (a t s : ℝ) : ℝ :=
  ∫ b, harperRankinCoordinateFactor p a t b *
    harperRankinCoordinateFactor p a s b ∂Problem520.coin

theorem harperRankinTwoHeightPrimeNormalizer_eq
    (p : ℕ) (a t s : ℝ) :
    harperRankinTwoHeightPrimeNormalizer p a t s =
      (harperRankinCoordinateFactor p a t false *
          harperRankinCoordinateFactor p a s false +
        harperRankinCoordinateFactor p a t true *
          harperRankinCoordinateFactor p a s true) / 2 := by
  unfold harperRankinTwoHeightPrimeNormalizer
  rw [Problem520.integral_coin_bool]

theorem harperRankinCoordinateFactor_false_eq_base_sub
    (p : ℕ) (a t : ℝ) :
    harperRankinCoordinateFactor p a t false =
      harperRankinEulerNormalizer p a -
        2 * harperRankinEulerRadius p a *
          Real.cos (t * Real.log (p : ℝ)) := by
  unfold harperRankinCoordinateFactor
  rw [harperRankinEulerFactor_eq]
  simp only [Problem520.ε, Bool.false_eq_true, if_false]
  unfold harperRankinEulerNormalizer
  ring

theorem harperRankinCoordinateFactor_true_eq_base_add
    (p : ℕ) (a t : ℝ) :
    harperRankinCoordinateFactor p a t true =
      harperRankinEulerNormalizer p a +
        2 * harperRankinEulerRadius p a *
          Real.cos (t * Real.log (p : ℝ)) := by
  unfold harperRankinCoordinateFactor
  rw [harperRankinEulerFactor_eq]
  simp only [Problem520.ε, if_true]
  unfold harperRankinEulerNormalizer
  ring

theorem harperRankinCoordinateFactor_pos
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) (b : Bool) :
    0 < harperRankinCoordinateFactor p a t b := by
  let r : ℝ := harperRankinEulerRadius p a
  let c : ℝ := Real.cos (t * Real.log (p : ℝ))
  have hr : 0 ≤ r := harperRankinEulerRadius_nonneg p a
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hsqrtNonneg : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (p : ℝ) ^ (2 : ℕ) = (p : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtOne : 1 < Real.sqrt (p : ℝ) := by nlinarith
  have hinvSqrtOne : (Real.sqrt (p : ℝ))⁻¹ < 1 :=
    (inv_lt_one₀ (by positivity)).2 hsqrtOne
  have hr1 : r < 1 :=
    (harperRankinEulerRadius_le_inv_sqrt hp.one_le ha).trans_lt
      hinvSqrtOne
  have hepsc : -1 ≤ Problem520.ε (fun _ ↦ b) p * c := by
    cases b
    · simp only [Problem520.ε, Bool.false_eq_true, if_false, neg_mul,
        one_mul, neg_le_neg_iff]
      exact Real.cos_le_one _
    · simp only [Problem520.ε, if_true, one_mul]
      exact Real.neg_one_le_cos _
  have hlinear : 0 <
      1 + Problem520.ε (fun _ ↦ b) p * r * c := by
    have hmul := mul_le_mul_of_nonneg_left hepsc hr
    dsimp only [r, c] at hmul ⊢
    nlinarith
  unfold harperRankinCoordinateFactor harperRankinEulerFactor
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hlinear) (sq_nonneg _)

/-- Exact shifted correlation-kernel formula at one prime. -/
theorem harperRankinTwoHeightPrimeNormalizer_eq_correlation
    (p : ℕ) (a t s : ℝ) :
    harperRankinTwoHeightPrimeNormalizer p a t s =
      harperRankinEulerNormalizer p a ^ (2 : ℕ) +
        4 * harperRankinEulerRadius p a ^ (2 : ℕ) *
          Real.cos (t * Real.log (p : ℝ)) *
          Real.cos (s * Real.log (p : ℝ)) := by
  rw [harperRankinTwoHeightPrimeNormalizer_eq,
    harperRankinCoordinateFactor_false_eq_base_sub,
    harperRankinCoordinateFactor_false_eq_base_sub,
    harperRankinCoordinateFactor_true_eq_base_add,
    harperRankinCoordinateFactor_true_eq_base_add]
  ring

theorem harperRankinTwoHeightPrimeNormalizer_pos
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    0 < harperRankinTwoHeightPrimeNormalizer p a t s := by
  rw [harperRankinTwoHeightPrimeNormalizer_eq]
  exact div_pos
    (add_pos
      (mul_pos (harperRankinCoordinateFactor_pos hp ha t false)
        (harperRankinCoordinateFactor_pos hp ha s false))
      (mul_pos (harperRankinCoordinateFactor_pos hp ha t true)
        (harperRankinCoordinateFactor_pos hp ha s true)))
    (by norm_num)

/-- One-prime correlation after removing both one-height normalizers. -/
noncomputable def harperRankinTwoHeightPrimeCorrelation
    (p : ℕ) (a t s : ℝ) : ℝ :=
  harperRankinTwoHeightPrimeNormalizer p a t s /
    harperRankinEulerNormalizer p a ^ (2 : ℕ)

theorem harperRankinTwoHeightPrimeCorrelation_eq
    (p : ℕ) (a t s : ℝ) :
    harperRankinTwoHeightPrimeCorrelation p a t s =
      1 +
        (4 * harperRankinEulerRadius p a ^ (2 : ℕ) *
          Real.cos (t * Real.log (p : ℝ)) *
          Real.cos (s * Real.log (p : ℝ))) /
            harperRankinEulerNormalizer p a ^ (2 : ℕ) := by
  unfold harperRankinTwoHeightPrimeCorrelation
  rw [harperRankinTwoHeightPrimeNormalizer_eq_correlation]
  have hden : harperRankinEulerNormalizer p a ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero _ (harperRankinEulerNormalizer_pos p a).ne'
  rw [add_div, div_self hden]

theorem harperRankinTwoHeightPrimeCorrelation_pos
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    0 < harperRankinTwoHeightPrimeCorrelation p a t s := by
  unfold harperRankinTwoHeightPrimeCorrelation
  exact div_pos (harperRankinTwoHeightPrimeNormalizer_pos hp ha t s)
    (pow_pos (harperRankinEulerNormalizer_pos p a) _)

private theorem four_mul_div_one_add_sq_le_linear_add_twelve_sq_rankin
    {r c : ℝ} (hr : 0 ≤ r) (hc : -1 ≤ c) :
    4 * c * r / (1 + r) ^ (2 : ℕ) ≤
      4 * c * r + 12 * r ^ (2 : ℕ) := by
  have hden : 0 < (1 + r) ^ (2 : ℕ) := by positivity
  have hdelta : 0 ≤ (1 + r) ^ (2 : ℕ) - 1 := by nlinarith
  have hcmul :
      -(1 + r) ^ (2 : ℕ) + 1 ≤
        c * ((1 + r) ^ (2 : ℕ) - 1) := by
    have := mul_le_mul_of_nonneg_right hc hdelta
    nlinarith
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg r, mul_nonneg hr (sq_nonneg r)]

theorem log_harperRankinTwoHeightPrimeCorrelation_le
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    Real.log (harperRankinTwoHeightPrimeCorrelation p a t s) ≤
      4 * harperRankinEulerRadius p a ^ (2 : ℕ) *
          Real.cos (t * Real.log (p : ℝ)) *
          Real.cos (s * Real.log (p : ℝ)) +
        12 * harperRankinEulerRadius p a ^ (4 : ℕ) := by
  let r : ℝ := harperRankinEulerRadius p a ^ (2 : ℕ)
  let c : ℝ := Real.cos (t * Real.log (p : ℝ)) *
    Real.cos (s * Real.log (p : ℝ))
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have habs : |c| ≤ 1 := by
    dsimp only [c]
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
      (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hc : -1 ≤ c := (abs_le.mp habs).1
  have hnormalizer : harperRankinEulerNormalizer p a = 1 + r := by
    rfl
  have hlinear :
      harperRankinTwoHeightPrimeCorrelation p a t s - 1 ≤
        4 * c * r + 12 * r ^ (2 : ℕ) := by
    rw [harperRankinTwoHeightPrimeCorrelation_eq]
    simp only [add_sub_cancel_left, hnormalizer]
    have hmain :=
      four_mul_div_one_add_sq_le_linear_add_twelve_sq_rankin hr hc
    dsimp only [c, r] at hmain ⊢
    convert hmain using 1 <;> ring
  exact (Real.log_le_sub_one_of_pos
    (harperRankinTwoHeightPrimeCorrelation_pos hp ha t s)).trans (by
      dsimp only [c, r] at hlinear ⊢
      nlinarith)

/-- Product of all normalized shifted two-height correlation factors. -/
noncomputable def harperRankinTwoHeightCorrelation
    (y : ℕ) (a t s : ℝ) : ℝ :=
  ∏ p : Problem520.HarperPrimeIndex y,
    harperRankinTwoHeightPrimeCorrelation p.1 a t s

theorem harperRankinTwoHeightCorrelation_pos
    (y : ℕ) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    0 < harperRankinTwoHeightCorrelation y a t s := by
  unfold harperRankinTwoHeightCorrelation
  exact Finset.prod_pos fun p _hp ↦
    harperRankinTwoHeightPrimeCorrelation_pos
      (Nat.prime_of_mem_primesBelow p.property) ha t s

/-- The shifted reciprocal-prime cosine kernel. -/
noncomputable def harperRankinPrimeCosineKernel
    (y : ℕ) (a u : ℝ) : ℝ :=
  ∑ p : Problem520.HarperPrimeIndex y,
    harperRankinEulerRadius p.1 a ^ (2 : ℕ) *
      Real.cos (u * Real.log (p.1 : ℝ))

theorem log_harperRankinTwoHeightCorrelation_le_differenceKernel
    (y : ℕ) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    Real.log (harperRankinTwoHeightCorrelation y a t s) ≤
      2 * harperRankinPrimeCosineKernel y a (t - s) +
        2 * harperRankinPrimeCosineKernel y a (t + s) + 12 := by
  rw [harperRankinTwoHeightCorrelation, Real.log_prod]
  · calc
      (∑ p : Problem520.HarperPrimeIndex y,
          Real.log (harperRankinTwoHeightPrimeCorrelation p.1 a t s)) ≤
          ∑ p : Problem520.HarperPrimeIndex y,
            (4 * harperRankinEulerRadius p.1 a ^ (2 : ℕ) *
                Real.cos (t * Real.log (p.1 : ℝ)) *
                Real.cos (s * Real.log (p.1 : ℝ)) +
              12 * harperRankinEulerRadius p.1 a ^ (4 : ℕ)) := by
        exact Finset.sum_le_sum fun p _hp ↦
          log_harperRankinTwoHeightPrimeCorrelation_le
            (Nat.prime_of_mem_primesBelow p.property) ha t s
      _ = 2 * harperRankinPrimeCosineKernel y a (t - s) +
            2 * harperRankinPrimeCosineKernel y a (t + s) +
            12 * ∑ p : Problem520.HarperPrimeIndex y,
              harperRankinEulerRadius p.1 a ^ (4 : ℕ) := by
        unfold harperRankinPrimeCosineKernel
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _hp
        have hsub :
            (t - s) * Real.log (p.1 : ℝ) =
              t * Real.log (p.1 : ℝ) - s * Real.log (p.1 : ℝ) := by ring
        have hadd :
            (t + s) * Real.log (p.1 : ℝ) =
              t * Real.log (p.1 : ℝ) + s * Real.log (p.1 : ℝ) := by ring
        rw [hsub, hadd, Real.cos_sub, Real.cos_add]
        ring
      _ ≤ _ := by
        have hquartic :
            (∑ p : Problem520.HarperPrimeIndex y,
              harperRankinEulerRadius p.1 a ^ (4 : ℕ)) ≤ 1 := by
          calc
            _ ≤ ∑ p : Problem520.HarperPrimeIndex y,
                (p.1 : ℝ)⁻¹ ^ (2 : ℕ) := by
              apply Finset.sum_le_sum
              intro p _hp
              have hr := harperRankinEulerRadius_le_inv_sqrt
                (Nat.prime_of_mem_primesBelow p.property).one_le ha
              have hr0 := harperRankinEulerRadius_nonneg p.1 a
              have hsqrtSq : Real.sqrt (p.1 : ℝ) ^ (2 : ℕ) =
                  (p.1 : ℝ) := Real.sq_sqrt (by positivity)
              have hsq : harperRankinEulerRadius p.1 a ^ (2 : ℕ) ≤
                  (p.1 : ℝ)⁻¹ := by
                calc
                  harperRankinEulerRadius p.1 a ^ (2 : ℕ) ≤
                      (Real.sqrt (p.1 : ℝ))⁻¹ ^ (2 : ℕ) :=
                    pow_le_pow_left₀ hr0 hr 2
                  _ = (p.1 : ℝ)⁻¹ := by
                    rw [inv_pow, hsqrtSq]
              have hsquare := pow_le_pow_left₀ (sq_nonneg _) hsq 2
              simpa only [← pow_mul] using hsquare
            _ = harperPrimeSquareBudget y := rfl
            _ ≤ 1 := harperPrimeSquareBudget_le_one y
        nlinarith
  · intro p _hp
    exact (harperRankinTwoHeightPrimeCorrelation_pos
      (Nat.prime_of_mem_primesBelow p.property) ha t s).ne'

private theorem one_sub_rpow_neg_le_mul_log_rankin
    {p a : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) :
    1 - p ^ (-a) ≤ a * Real.log p := by
  have hpPos : 0 < p := zero_lt_one.trans_le hp
  have hexp := Real.add_one_le_exp (-a * Real.log p)
  have hrpow : p ^ (-a) = Real.exp (-a * Real.log p) := by
    rw [Real.rpow_def_of_pos hpPos]
    congr 1
    ring
  rw [← hrpow] at hexp
  linarith

/-- Replacing `1/p` by the shifted weight `p^(-1-a)` changes any cosine
kernel by at most the elementary Rankin loss. -/
theorem harperRankinPrimeCosineKernel_le_critical_add_loss
    (y : ℕ) {a : ℝ} (ha : 0 ≤ a) (u : ℝ) :
    harperRankinPrimeCosineKernel y a u ≤
      harperPrimeCosineKernel y u +
        a * Problem520.weightedPrimeReciprocalPrefix y := by
  rw [show Problem520.weightedPrimeReciprocalPrefix y =
      ∑ p : Problem520.HarperPrimeIndex y,
        Real.log (p.1 : ℝ) * (p.1 : ℝ)⁻¹ by
    unfold Problem520.weightedPrimeReciprocalPrefix
    calc
      (∑ p ∈ (y + 1).primesBelow,
          Real.log (p : ℝ) / (p : ℝ)) =
          ∑ p : Problem520.HarperPrimeIndex y,
            Real.log (p.1 : ℝ) / (p.1 : ℝ) :=
        (Finset.sum_coe_sort ((y + 1).primesBelow)
          (fun p ↦ Real.log (p : ℝ) / (p : ℝ))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        ring]
  unfold harperRankinPrimeCosineKernel harperPrimeCosineKernel
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _hp
  let x : ℝ := (p.1 : ℝ)⁻¹
  let q : ℝ := harperRankinEulerRadius p.1 a ^ (2 : ℕ)
  let c : ℝ := Real.cos (u * Real.log (p.1 : ℝ))
  have hpPrime := Nat.prime_of_mem_primesBelow p.property
  have hpOneR : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hpPrime.one_le
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hqle : q ≤ x := by
    dsimp only [q, x]
    rw [harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg hpPrime.pos a]
    exact mul_le_of_le_one_right (by positivity)
      (rpow_neg_le_one_of_one_le hpOneR ha)
  have hc : -1 ≤ c := by
    dsimp only [c]
    exact Real.neg_one_le_cos _
  have hlinear : c * q ≤ c * x + (x - q) := by
    have := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hqle)
    nlinarith
  have hloss : x - q ≤ a * (Real.log (p.1 : ℝ) * x) := by
    have hlocal := one_sub_rpow_neg_le_mul_log_rankin hpOneR ha
    dsimp only [x, q]
    rw [harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg hpPrime.pos a]
    calc
      (p.1 : ℝ)⁻¹ - (p.1 : ℝ)⁻¹ * (p.1 : ℝ) ^ (-a) =
          (p.1 : ℝ)⁻¹ * (1 - (p.1 : ℝ) ^ (-a)) := by ring
      _ ≤ (p.1 : ℝ)⁻¹ * (a * Real.log (p.1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlocal (by positivity)
      _ = a * (Real.log (p.1 : ℝ) * (p.1 : ℝ)⁻¹) := by ring
  dsimp only [c, q, x] at hlinear hloss ⊢
  linarith

/-- At the coefficient-localizing shift, both height kernels differ from
their critical-line versions by a constant depending only on `V`. -/
theorem harperRankinTwoHeightCorrelation_le_criticalKernel_fixedShift
    {V : ℝ} (hV : 0 ≤ V) {y : ℕ} (hy : 4 ≤ y) (t s : ℝ) :
    harperRankinTwoHeightCorrelation y
        (4 * V / Real.log (y : ℝ)) t s ≤
      Real.exp
        (2 * harperPrimeCosineKernel y (t - s) +
          2 * harperPrimeCosineKernel y (t + s) + 12 +
          16 * V * (1 + (Real.log 4 + 4) / Real.log 4)) := by
  let a : ℝ := 4 * V / Real.log (y : ℝ)
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  rw [← Real.exp_log (harperRankinTwoHeightCorrelation_pos y ha t s)]
  apply Real.exp_le_exp.mpr
  refine (log_harperRankinTwoHeightCorrelation_le_differenceKernel
    y ha t s).trans ?_
  have hdiff := harperRankinPrimeCosineKernel_le_critical_add_loss
    y ha (t - s)
  have hsum := harperRankinPrimeCosineKernel_le_critical_add_loss
    y ha (t + s)
  have hweighted := Problem520.weightedPrimeReciprocalPrefix_le_log_add_const
    (show 1 ≤ y by omega)
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hlog4y : Real.log (4 : ℝ) ≤ Real.log (y : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hy)
  have hratio :
      (Real.log (y : ℝ) + (Real.log 4 + 4)) /
          Real.log (y : ℝ) ≤
        1 + (Real.log 4 + 4) / Real.log 4 := by
    rw [add_div, div_self hlog.ne']
    have hinv : (Real.log (y : ℝ))⁻¹ ≤ (Real.log 4)⁻¹ :=
      (inv_le_inv₀ hlog hlog4).2 hlog4y
    gcongr
  have haloss :
      a * Problem520.weightedPrimeReciprocalPrefix y ≤
        4 * V * (1 + (Real.log 4 + 4) / Real.log 4) := by
    calc
      a * Problem520.weightedPrimeReciprocalPrefix y ≤
          a * (Real.log (y : ℝ) + (Real.log 4 + 4)) := by gcongr
      _ = 4 * V *
          ((Real.log (y : ℝ) + (Real.log 4 + 4)) /
            Real.log (y : ℝ)) := by dsimp only [a]; ring
      _ ≤ _ := by gcongr
  dsimp only [a] at hdiff hsum
  linarith

#print axioms Erdos.Problem1144.harperRankinTwoHeightPrimeNormalizer_eq_correlation
#print axioms Erdos.Problem1144.log_harperRankinTwoHeightCorrelation_le_differenceKernel
#print axioms Erdos.Problem1144.harperRankinPrimeCosineKernel_le_critical_add_loss
#print axioms Erdos.Problem1144.harperRankinTwoHeightCorrelation_le_criticalKernel_fixedShift

end


end Problem1144
end Erdos
