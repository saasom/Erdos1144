import Erdos.Problem1144.HarperRankinParseval
import Erdos.Problem1144.HarperRankinVarianceWindow
import Erdos.Problem520.MertensProduct

open Finset
open scoped BigOperators

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# The Rankin-shifted Euler normalizer

For a fixed damping parameter `V`, the shift `a = 4V/log y` changes the
critical Euler normalizer only by a constant factor.  The proof is elementary:
each local loss is controlled by `exp (-2a log(p)/p)`, and the already
verified weighted-prime prefix bound sums these losses to `O(a log y)`.
-/

private theorem exp_neg_two_mul_le_one_sub
    {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hpos : 0 < 1 - x := by linarith
  rw [← Real.le_log_iff_exp_le hpos]
  calc
    -2 * x ≤ -x / (1 - x) := by
      rw [le_div_iff₀ hpos]
      nlinarith
    _ = 1 - (1 - x)⁻¹ := by
      field_simp [hpos.ne']
      ring
    _ ≤ Real.log (1 - x) := Real.one_sub_inv_le_log_of_pos hpos

private theorem one_sub_rpow_neg_le_mul_log
    {p a : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) :
    1 - p ^ (-a) ≤ a * Real.log p := by
  have hpPos : 0 < p := zero_lt_one.trans_le hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp
  have hexp := Real.add_one_le_exp (-a * Real.log p)
  have hrpow : p ^ (-a) = Real.exp (-a * Real.log p) := by
    rw [Real.rpow_def_of_pos hpPos]
    congr 1
    ring
  rw [← hrpow] at hexp
  linarith

/-- One shifted prime factor loses at most its logarithmically weighted
Rankin cost. -/
theorem mul_exp_neg_rankinCost_le_harperRankinEulerNormalizer
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) :
    (1 + (p : ℝ)⁻¹) *
        Real.exp (-2 * a * (Real.log (p : ℝ) / (p : ℝ))) ≤
      harperRankinEulerNormalizer p a := by
  let u : ℝ := (p : ℝ)⁻¹
  let q : ℝ := (p : ℝ) ^ (-a)
  let x : ℝ := u * (1 - q)
  have hpTwo : 2 ≤ p := hp.two_le
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hpTwo
  have hpPos : (0 : ℝ) < p := by positivity
  have hpOne : (1 : ℝ) ≤ p := by linarith
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have huHalf : u ≤ 1 / 2 := by
    dsimp only [u]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ hpPos (by norm_num)).2 hpR
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hqOne : q ≤ 1 := by
    dsimp only [q]
    exact (Real.rpow_le_one_iff_of_pos hpPos).2
      (Or.inl ⟨hpOne, neg_nonpos.mpr ha⟩)
  have hx : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg hu (sub_nonneg.mpr hqOne)
  have hxHalf : x ≤ 1 / 2 := by
    have hsub : 1 - q ≤ 1 := by linarith
    exact (mul_le_of_le_one_right hu hsub).trans huHalf
  have hxCost : x ≤ a * (Real.log (p : ℝ) / (p : ℝ)) := by
    have hloss := one_sub_rpow_neg_le_mul_log hpOne ha
    dsimp only [x, u, q]
    rw [div_eq_mul_inv]
    calc
      (p : ℝ)⁻¹ * (1 - (p : ℝ) ^ (-a)) ≤
          (p : ℝ)⁻¹ * (a * Real.log (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hloss hu
      _ = a * (Real.log (p : ℝ) * (p : ℝ)⁻¹) := by ring
  have hExpCost :
      Real.exp (-2 * a * (Real.log (p : ℝ) / (p : ℝ))) ≤
        Real.exp (-2 * x) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hExpX := exp_neg_two_mul_le_one_sub hx hxHalf
  have hfac : 0 ≤ 1 + u := by positivity
  have hmain :
      (1 + u) *
          Real.exp (-2 * a * (Real.log (p : ℝ) / (p : ℝ))) ≤
        (1 + u) * (1 - x) :=
    mul_le_mul_of_nonneg_left (hExpCost.trans hExpX) hfac
  have hlast : (1 + u) * (1 - x) ≤ 1 + u * q := by
    have hsquare : 0 ≤ u ^ 2 * (1 - q) := mul_nonneg (sq_nonneg u) (by linarith)
    dsimp only [x]
    nlinarith
  have hnormalizer : harperRankinEulerNormalizer p a = 1 + u * q := by
    unfold harperRankinEulerNormalizer
    rw [harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg hp.pos a]
  rw [hnormalizer]
  simpa only [u, q] using hmain.trans hlast

/-- Product form: the entire shifted normalizer is the critical normalizer
times an explicitly controlled exponential loss. -/
theorem primeEnergyNormalizer_mul_exp_rankinLoss_le
    (y : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    Problem520.primeEnergyNormalizer y *
        Real.exp (-2 * a * Problem520.weightedPrimeReciprocalPrefix y) ≤
      harperRankinPrimeEnergyNormalizer y a := by
  classical
  let P : Finset ℕ := (y + 1).primesBelow
  have hlocal (p : ℕ) (hp : p ∈ P) :
      (1 + (p : ℝ)⁻¹) *
          Real.exp (-2 * a * (Real.log (p : ℝ) / (p : ℝ))) ≤
        harperRankinEulerNormalizer p a :=
    mul_exp_neg_rankinCost_le_harperRankinEulerNormalizer
      (Nat.prime_of_mem_primesBelow hp) ha
  have hprod := Finset.prod_le_prod
    (fun p hp ↦ mul_nonneg (by positivity) (Real.exp_pos _).le)
    hlocal
  unfold Problem520.primeEnergyNormalizer
    Problem520.weightedPrimeReciprocalPrefix
    harperRankinPrimeEnergyNormalizer
  change
    (∏ p ∈ P, (1 + (p : ℝ)⁻¹)) *
        Real.exp (-2 * a * ∑ p ∈ P,
          Real.log (p : ℝ) / (p : ℝ)) ≤
      ∏ p ∈ P, harperRankinEulerNormalizer p a
  calc
    (∏ p ∈ P, (1 + (p : ℝ)⁻¹)) *
          Real.exp (-2 * a * ∑ p ∈ P,
            Real.log (p : ℝ) / (p : ℝ)) =
        ∏ p ∈ P,
          ((1 + (p : ℝ)⁻¹) *
            Real.exp (-2 * a * (Real.log (p : ℝ) / (p : ℝ)))) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      rw [← Finset.mul_sum]
    _ ≤ _ := hprod

/-- At Harper's damping `a = 4V/log y`, the shifted normalizer remains a
fixed positive multiple of `log y`.  The constant is explicit and depends
only on `V`, never on `y`. -/
theorem exp_rankinNormalizerConstant_mul_log_le
    {V : ℝ} (hV : 0 ≤ V) {y : ℕ} (hy : 4 ≤ y) :
    ((1 / 2 : ℝ) *
        Real.exp (-8 * V *
          (1 + (Real.log 4 + 4) / Real.log 4))) *
        Real.log (y : ℝ) ≤
      harperRankinPrimeEnergyNormalizer y
        (4 * V / Real.log (y : ℝ)) := by
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlog4y : Real.log (4 : ℝ) ≤ Real.log (y : ℝ) := by
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 4)
      (by exact_mod_cast hy)
  let a : ℝ := 4 * V / Real.log (y : ℝ)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hweighted := Problem520.weightedPrimeReciprocalPrefix_le_log_add_const
    (show 1 ≤ y by omega)
  have hcost :
      2 * a * Problem520.weightedPrimeReciprocalPrefix y ≤
        8 * V * (1 + (Real.log 4 + 4) / Real.log 4) := by
    have hconst : 0 ≤ Real.log 4 + 4 := by positivity
    have hinv : (Real.log (y : ℝ))⁻¹ ≤ (Real.log 4)⁻¹ := by
      exact (inv_le_inv₀ hlog hlog4).2 hlog4y
    have hratio :
        (Real.log (y : ℝ) + (Real.log 4 + 4)) /
            Real.log (y : ℝ) ≤
          1 + (Real.log 4 + 4) / Real.log 4 := by
      rw [add_div, div_self hlog.ne']
      gcongr
    dsimp only [a]
    calc
      2 * (4 * V / Real.log (y : ℝ)) *
          Problem520.weightedPrimeReciprocalPrefix y ≤
        2 * (4 * V / Real.log (y : ℝ)) *
          (Real.log (y : ℝ) + (Real.log 4 + 4)) := by
            gcongr
      _ = 8 * V *
          ((Real.log (y : ℝ) + (Real.log 4 + 4)) /
            Real.log (y : ℝ)) := by ring
      _ ≤ 8 * V *
          (1 + (Real.log 4 + 4) / Real.log 4) := by gcongr
  have hexp :
      Real.exp (-8 * V * (1 + (Real.log 4 + 4) / Real.log 4)) ≤
        Real.exp (-2 * a * Problem520.weightedPrimeReciprocalPrefix y) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hcritical := Problem520.half_mul_log_le_primeEnergyNormalizer
    (show 2 ≤ y by omega)
  have hloss := primeEnergyNormalizer_mul_exp_rankinLoss_le y ha
  calc
    ((1 / 2 : ℝ) *
          Real.exp (-8 * V * (1 + (Real.log 4 + 4) / Real.log 4))) *
        Real.log (y : ℝ) =
      ((1 / 2 : ℝ) * Real.log (y : ℝ)) *
        Real.exp (-8 * V * (1 + (Real.log 4 + 4) / Real.log 4)) := by ring
    _ ≤ Problem520.primeEnergyNormalizer y *
        Real.exp (-8 * V * (1 + (Real.log 4 + 4) / Real.log 4)) := by
      gcongr
    _ ≤ Problem520.primeEnergyNormalizer y *
        Real.exp (-2 * a * Problem520.weightedPrimeReciprocalPrefix y) := by
      exact mul_le_mul_of_nonneg_left hexp
        (Problem520.primeEnergyNormalizer_pos y).le
    _ ≤ harperRankinPrimeEnergyNormalizer y a := hloss

#print axioms Erdos.Problem1144.primeEnergyNormalizer_mul_exp_rankinLoss_le
#print axioms Erdos.Problem1144.exp_rankinNormalizerConstant_mul_log_le

end

end Problem1144
end Erdos
